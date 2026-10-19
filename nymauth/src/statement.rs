// SPDX-License-Identifier: MIT
//! The nym_auth statement for mdoc credentials as one narrow API over plain bytes.
//!
//! This is the library form of the reference prover and verifier of the nym_auth circuits
//! (`SPEC.md` V3 to V6, configuration `known-offender-matching-ssc`, mdoc only). The caller
//! supplies the circuits as data (the bincode `(step, core)` shapes), the credential's
//! `IssuerSigned` as CBOR and the values the verifier named; it gets a proof and the pseudonym.
//!
//! What the proof shows, without showing the credential: the issuer signed it (ES256, key Q); it
//! is a `eu.europa.ec.eudi.nym_auth.1` mdoc; its `birth_date` lies in [E, C]; it is valid at T;
//! the device key it binds signed the verifier's challenge digest `e2`; the holder knows the
//! `secret_seed` whose SHA-256 is the signed `ssc`; and the revealed pseudonym is
//! SHA-256(`nym_auth/v1/known-offender-matching-ssc` ‖ secret_seed ‖ 0x00×32 ‖ verifier_input).
//!
//! # Integration contract
//!
//! The proof shows the statement *for the values it is given*, so those values must come from the
//! verifier, never from the holder: the time `T`, the challenge digest `e2` (which binds the
//! proof to this session, origin and nonce) and `verifier_input` (which selects the pseudonym).
//! The verifier computes `T` from its own clock, `e2` from the request it issued and
//! `verifier_input` from its own identifier, and passes them to [`verify`]. A verifier that takes
//! any of them from the presentation lets a holder replay or re-target a proof. The issuer key
//! `Q` must be the key the verifier trusts for the credential's issuer (it is a public input,
//! checked on the curve by this module). The range `[E, C]` is checked here against the rulebook
//! (see [`check_range`]).
//!
//! # Issuer profile
//!
//! The circuits and this parser assume credentials issued under the nym_auth profile
//! (`SPEC.md` 2.1), which gives every attribute a unique name: the first item with a given
//! `elementIdentifier` is the one used. A credential with duplicate names is outside the profile;
//! the issuer must not issue one.
//!
//! # Circuit pinning
//!
//! [`Keys::from_shapes`] accepts only shapes whose SHA-256 is in [`APPROVED_SHAPES`]: a verifier
//! that built keys from attacker-chosen shapes would accept proofs of a weaker statement.
//!
//! # Known circuit-level gap (for the circuit authors)
//!
//! The circuit does not check that the issuer key `Q` is a point on P-256, nor its range; `Q` is a
//! public input, so this module checks it on the host ([`Error::Input`]). A circuit-level check
//! would make a verifier safe even against a host that skips it.
//!
//! No function here panics: a panic in the witness or the prover is caught and returned as
//! [`Error::Internal`]. The copy of `secret_seed` this module makes is zeroed on every path; the
//! witness builder holds its own copies of the seed's bytes while it runs, which the library
//! cannot reach.

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;

use halo2curves::{
  CurveAffine,
  secp256r1::{Fp, Secp256r1Affine},
};
use zeroize::Zeroizing;

use crate::app::{self, Proof, ProverKey, Rejection, VerifierKey};
use crate::fixtures::cbor::{Item, Value, text};
use crate::gadgets::p256::{PublicKey, Signature};
use crate::mdoc::{MdocNymCore, MdocWitness};
use crate::presentation::{Date, Presentation, Public, Time, TimeEncoding};
use crate::pseudonym::{self, NymMessages, NymPublic};
use crate::request::Request;
use crate::table::{FULL_MDOC, sha256};

/// The docType of a nym_auth mdoc.
pub const DOC_TYPE: &str = "eu.europa.ec.eudi.nym_auth.1";
/// The element that holds the birth date.
pub const BIRTH_DATE: &str = "birth_date";
/// The element that holds SHA-256(secret_seed).
pub const SSC: &str = "ssc";
/// The length of `secret_seed` in bytes.
pub const SEED_BYTES: usize = 16;

/// Digests (SHA-256, hex) of the decompressed shapes that [`Keys::from_shapes`] accepts, each with
/// the circuit version it is. **To approve a new circuit version, append one line here** after the
/// circuit authors publish it and `statement::shapes()` is checked to reproduce it; nothing else
/// changes. Remove a line to retire a version.
pub const APPROVED_SHAPES: &[(&str, &str)] =
  &[("nymauth-vega-mdoc v1", "4da5e73afb9be2682e70be793c9956a73304e21f31246aa10da0d3e95c926425")];

/// The rulebook's smallest age window, in days (`le - ge + 1`; nym_auth rulebook, `age_check`).
pub const MIN_WINDOW_DAYS: i64 = 365;

/// The largest `IssuerSigned` accepted, in bytes (a nym_auth one is about 1 KiB).
pub const MAX_ISSUER_SIGNED: usize = 64 * 1024;

/// The largest proof read, in bytes (a proof is about 96 KB).
pub const MAX_PROOF: usize = 512 * 1024;

/// Why the inputs were refused, coarsely. The first broken rule of the circuit is not exposed:
/// it would tell a probing caller which check failed. Build with the `debug-rules` feature to
/// carry it in [`Refusal::rule`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RefusalCode {
  /// `secret_seed` does not open the credential's `ssc`.
  SeedMismatch,
  /// The issuer signature (or the issuer key) does not match the credential.
  IssuerSignature,
  /// The device signature does not match the credential's device key and the challenge.
  DeviceSignature,
  /// The credential does not satisfy the statement (type, validity, age range, structure).
  Credential,
}

/// A refusal: no proof was made.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Refusal {
  pub code: RefusalCode,
  /// The first broken rule, for tests and debugging only.
  #[cfg(feature = "debug-rules")]
  pub rule: String,
}

impl Refusal {
  fn new(code: RefusalCode, _rule: &str) -> Self {
    Refusal {
      code,
      #[cfg(feature = "debug-rules")]
      rule: _rule.to_string(),
    }
  }

  /// Classifies a broken rule's path.
  fn of_rule(rule: &str) -> Self {
    let code = if rule.contains("seed digest") {
      RefusalCode::SeedMismatch
    } else if rule.contains("device signature") {
      RefusalCode::DeviceSignature
    } else if rule.contains("issuer signature") {
      RefusalCode::IssuerSignature
    } else {
      RefusalCode::Credential
    };
    Refusal::new(code, rule)
  }
}

/// Why a statement could not be proved, or a proof was not accepted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
  /// An input is malformed: a length, a date, a time, a range, the issuer key, or the
  /// credential's structure. The text names the input and never holds the seed.
  Input(String),
  /// The shapes are unreadable, inconsistent or past the budget.
  Shapes(String),
  /// The shapes are well formed but not approved ([`APPROVED_SHAPES`]); holds their SHA-256.
  UnknownCircuit(String),
  /// The inputs break a rule of the circuit; no proof was made.
  Refused(Refusal),
  /// The prover failed.
  Prover(String),
  /// The proof does not verify (the prover's own verification failed).
  ProofInvalid(String),
  /// The proof verifies, but not for the values the verifier named (another issuer key, date,
  /// time, challenge or verifier_input, or a step instance at another position).
  Mismatch(String),
  /// A bug: a panic was caught.
  Internal(String),
}

impl std::fmt::Display for Error {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Error::Input(t) => write!(f, "invalid input: {t}"),
      Error::Shapes(t) => write!(f, "invalid circuit shapes: {t}"),
      Error::UnknownCircuit(h) => write!(f, "circuit shapes {h} are not approved"),
      Error::Refused(r) => write!(f, "inputs refused: {:?}", r.code),
      Error::Prover(t) => write!(f, "prover failed: {t}"),
      Error::ProofInvalid(t) => write!(f, "proof invalid: {t}"),
      Error::Mismatch(t) => write!(f, "proof does not match the named values: {t}"),
      Error::Internal(t) => write!(f, "internal error: {t}"),
    }
  }
}

impl std::error::Error for Error {}

/// The keys of the nym_auth mdoc circuits, built from their shapes. Setup is the costly step;
/// build the keys once and reuse them for every proof and verification.
pub struct Keys {
  prover: ProverKey,
  verifier: VerifierKey,
}

impl Keys {
  /// Builds the keys from the circuits as data: the decompressed `(step, core)` shapes in the
  /// prover's serialization (bincode), as published for `nymauth-vega-mdoc`.
  ///
  /// Refuses shapes that are not in [`APPROVED_SHAPES`] with [`Error::UnknownCircuit`], before
  /// reading them.
  pub fn from_shapes(shapes: &[u8]) -> Result<Self, Error> {
    guarded(|| {
      let digest = hex(&sha256(shapes));
      if !APPROVED_SHAPES.iter().any(|(_, approved)| *approved == digest) {
        return Err(Error::UnknownCircuit(digest));
      }
      let (prover, verifier) = app::setup_from_shapes_in(&FULL_MDOC, shapes)
        .map_err(|e| Error::Shapes(format!("{e:?}")))?;
      Ok(Keys { prover, verifier })
    })
  }
}

/// The circuits as data, built from their source: the bincode `(step, core)` shapes that
/// [`Keys::from_shapes`] reads. The published artifact must equal this; a test pins it.
pub fn shapes() -> Result<Vec<u8>, Error> {
  guarded(|| app::shapes(&MdocNymCore::blank()).map_err(|e| Error::Shapes(format!("{e:?}"))))
}

/// The values the verifier names, and that the prover must be given to prove for them.
#[derive(Clone, Debug)]
pub struct Statement<'a> {
  /// Big-endian x of the issuer key Q.
  pub issuer_key_x: &'a [u8],
  /// Big-endian y of the issuer key Q.
  pub issuer_key_y: &'a [u8],
  /// T, `YYYY-MM-DDThh:mm:ssZ`.
  pub time: &'a str,
  /// E, `YYYY-MM-DD`; `0000-00-00` sets no lower bound.
  pub earliest: &'a str,
  /// C, `YYYY-MM-DD`; `9999-12-31` sets no upper bound.
  pub cutoff: &'a str,
  /// e2: SHA-256 of the message the device key signed.
  pub challenge_digest: &'a [u8],
  /// SHA-256(verifier_id).
  pub verifier_input: &'a [u8],
}

/// What only the holder has.
pub struct Holder<'a> {
  /// The credential's `IssuerSigned` as CBOR.
  pub issuer_signed: &'a [u8],
  /// The 16-byte secret_seed.
  pub secret_seed: &'a [u8],
  /// The device key's ES256 signature on the challenge, `r || s`.
  pub device_signature: &'a [u8],
}

/// A proof and the pseudonym it reveals.
#[derive(Clone, PartialEq, Eq)]
pub struct Proved {
  /// The proof (bincode), as the verifier reads it.
  pub proof: Vec<u8>,
  pub pseudonym: [u8; 32],
}

impl std::fmt::Debug for Proved {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "Proved({} proof bytes)", self.proof.len())
  }
}

/// Runs `f`, turning a panic into [`Error::Internal`].
fn guarded<T>(f: impl FnOnce() -> Result<T, Error>) -> Result<T, Error> {
  match catch_unwind(AssertUnwindSafe(f)) {
    Ok(result) => result,
    Err(payload) => {
      let what = payload
        .downcast_ref::<&str>()
        .map(|s| s.to_string())
        .or_else(|| payload.downcast_ref::<String>().cloned())
        .unwrap_or_else(|| "panic".into());
      Err(Error::Internal(what))
    }
  }
}

fn hex(bytes: &[u8]) -> String {
  bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn fixed<const N: usize>(bytes: &[u8], what: &str) -> Result<[u8; N], Error> {
  bytes.try_into().map_err(|_| Error::Input(format!("{what} is {} bytes, not {N}", bytes.len())))
}

/// A non-empty run of ASCII digits as a number: no sign, no space (`str::parse` accepts `+`).
fn number(s: &str) -> Option<u32> {
  if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) { None } else { s.parse().ok() }
}

fn days_in_month(year: u32, month: u32) -> u32 {
  match month {
    1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
    4 | 6 | 9 | 11 => 30,
    _ if year % 4 == 0 && (year % 100 != 0 || year % 400 == 0) => 29,
    _ => 28,
  }
}

/// Days since 1970-01-01 of a calendar date (civil_from_days's inverse, Howard Hinnant).
fn days(d: &Date) -> i64 {
  let (y, m, day) = (i64::from(d.year), i64::from(d.month), i64::from(d.day));
  let y = if m <= 2 { y - 1 } else { y };
  let era = y.div_euclid(400);
  let yoe = y - era * 400;
  let doy = (153 * (if m > 2 { m - 3 } else { m + 9 }) + 2) / 5 + day - 1;
  let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
  era * 146_097 + doe - 719_468
}

/// `YYYY-MM-DD`, a real calendar date with a year from 1 to 9999.
fn date(s: &str) -> Result<Date, Error> {
  let bad = || Error::Input(format!("not a date YYYY-MM-DD: {s:?}"));
  let b = s.as_bytes();
  if s.len() != 10 || !s.is_ascii() || b[4] != b'-' || b[7] != b'-' {
    return Err(bad());
  }
  match (number(&s[0..4]), number(&s[5..7]), number(&s[8..10])) {
    (Some(year), Some(month), Some(day))
      if year >= 1 && (1..=12).contains(&month) && (1..=days_in_month(year, month)).contains(&day) =>
    {
      Ok(Date { year, month, day })
    }
    _ => Err(bad()),
  }
}

fn time(s: &str) -> Result<Time, Error> {
  let bad = || Error::Input(format!("not a date-time YYYY-MM-DDThh:mm:ssZ: {s:?}"));
  if s.len() != 20 || !s.is_ascii() {
    return Err(bad());
  }
  let b = s.as_bytes();
  if b[10] != b'T' || b[13] != b':' || b[16] != b':' || b[19] != b'Z' {
    return Err(bad());
  }
  match (number(&s[11..13]), number(&s[14..16]), number(&s[17..19])) {
    (Some(hour), Some(minute), Some(second)) if hour < 24 && minute < 60 && second < 60 => {
      Ok(Time { date: date(&s[..10])?, hour, minute, second })
    }
    _ => Err(bad()),
  }
}

const NO_LOWER_BOUND: &str = "0000-00-00";
const NO_UPPER_BOUND: &str = "9999-12-31";

/// The rulebook's rule for the age range `[E, C]` (nym_auth rulebook, `age_check`): when both
/// bounds are given, the request is unsatisfiable if `C < E` or if `C - E + 1`, in days, is less
/// than [`MIN_WINDOW_DAYS`]. A one-day window would name a birth date outright. `0000-00-00` as E
/// and `9999-12-31` as C stand for an absent bound. [`prove`] and [`verify`] both apply it.
pub fn check_range(earliest: &str, cutoff: &str) -> Result<(), Error> {
  let (e, c) = (earliest != NO_LOWER_BOUND, cutoff != NO_UPPER_BOUND);
  let (earliest, cutoff) = (if e { Some(date(earliest)?) } else { None }, date(cutoff)?);
  if let (Some(earliest), true) = (earliest, c) {
    let window = days(&cutoff) - days(&earliest) + 1;
    if window < MIN_WINDOW_DAYS {
      return Err(Error::Input(format!(
        "the age range [{}, {}] spans {window} days; the rulebook requires at least {MIN_WINDOW_DAYS}",
        earliest.text(),
        cutoff.text()
      )));
    }
  }
  Ok(())
}

/// Checks that `(x, y)` is a point of P-256: both coordinates below the field prime and on the
/// curve. The circuit does not check the issuer key; see the module's note.
fn check_issuer_key(x: &[u8; 32], y: &[u8; 32]) -> Result<(), Error> {
  let coordinate = |be: &[u8; 32]| {
    let mut le = *be;
    le.reverse();
    Fp::from_bytes(&le).into_option()
  };
  let (x_is_zero, y_is_zero) = (x.iter().all(|b| *b == 0), y.iter().all(|b| *b == 0));
  let on_curve = match (coordinate(x), coordinate(y)) {
    // (0, 0) is how the curve library writes the point at infinity.
    (Some(x), Some(y)) if !(x_is_zero && y_is_zero) => bool::from(Secp256r1Affine::from_xy(x, y).is_some()),
    _ => false,
  };
  if on_curve { Ok(()) } else { Err(Error::Input("the issuer key is not a point of P-256".into())) }
}

/// The public values from a statement, validated: lengths, dates, the range rule, the issuer key.
fn public(statement: &Statement) -> Result<(Public, [u8; 32]), Error> {
  let x: [u8; 32] = fixed(statement.issuer_key_x, "issuer key x")?;
  let y: [u8; 32] = fixed(statement.issuer_key_y, "issuer key y")?;
  check_issuer_key(&x, &y)?;
  check_range(statement.earliest, statement.cutoff)?;
  let born_from =
    if statement.earliest == NO_LOWER_BOUND { None } else { Some(date(statement.earliest)?) };
  let public = Public {
    issuer_key: PublicKey { x, y },
    born_from,
    born_by: date(statement.cutoff)?,
    now: time(statement.time)?,
    challenge: fixed(statement.challenge_digest, "challenge digest")?,
    request: Request::mdoc(DOC_TYPE, BIRTH_DATE).map_err(Error::Input)?,
  };
  Ok((public, fixed(statement.verifier_input, "verifier input")?))
}

/// The parts of an IssuerSigned: the Sig_structure the issuer signed, its signature, and each
/// item's IssuerSignedItemBytes by element identifier.
struct Mdoc {
  sig_structure: Vec<u8>,
  r: [u8; 32],
  s: [u8; 32],
  items: Vec<(String, Vec<u8>)>,
}

fn mdoc(issuer_signed: &[u8]) -> Result<Mdoc, Error> {
  let take = |e: String| Error::Input(format!("IssuerSigned: {e}"));
  if issuer_signed.len() > MAX_ISSUER_SIGNED {
    return Err(Error::Input(format!(
      "IssuerSigned is {} bytes, more than {MAX_ISSUER_SIGNED}",
      issuer_signed.len()
    )));
  }
  let root = Item::read(issuer_signed).map_err(take)?;
  let auth = root.get(&text("issuerAuth")).map_err(take)?;
  let (protected, payload, signature) =
    (auth.at(0).map_err(take)?, auth.at(2).map_err(take)?, auth.at(3).map_err(take)?.content());
  let sig_structure = Value::Array(vec![
    text("Signature1"),
    Value::Bytes(protected.content().to_vec()),
    Value::Bytes(vec![]),
    Value::Bytes(payload.content().to_vec()),
  ])
  .encode();
  let signature: [u8; 64] = fixed(signature, "the issuer signature")?;
  let mut items = Vec::new();
  for entry in root.get(&text("nameSpaces")).map_err(take)?.try_children().map_err(take)?.chunks(2)
  {
    let [_, entries] = entry else { return Err(Error::Input("IssuerSigned: odd nameSpaces".into())) };
    for item in entries.try_children().map_err(take)? {
      let id = item.embedded().map_err(take)?.get(&text("elementIdentifier")).map_err(take)?;
      let id = String::from_utf8(id.content().to_vec())
        .map_err(|_| Error::Input("IssuerSigned: elementIdentifier is not UTF-8".into()))?;
      items.push((id, item.bytes.to_vec()));
    }
  }
  let (r, s) = signature.split_at(32);
  Ok(Mdoc { sig_structure, r: fixed(r, "r")?, s: fixed(s, "s")?, items })
}

impl Mdoc {
  /// The first item named `id`; the issuer profile gives every attribute a unique name.
  fn item(&self, id: &str) -> Result<&[u8], Error> {
    let found = self.items.iter().find(|(name, _)| name == id);
    found
      .map(|(_, bytes)| &bytes[..])
      .ok_or_else(|| Error::Input(format!("IssuerSigned has no item {id}")))
  }
}

/// Proves the statement for the verifier's values. Builds the witness (a few milliseconds),
/// prepares and proves. Returns the proof and the pseudonym the holder computes.
///
/// `statement`'s time, challenge digest and verifier_input must be the verifier's, not values the
/// holder chose (see the module's integration contract). The inputs are validated first
/// ([`check_range`], the issuer key, lengths and dates), then the circuit's rules are checked on
/// the witness: a failure is [`Error::Refused`] with a coarse [`RefusalCode`], and no proof is
/// made. The proof is verified before it is returned.
///
/// The seed is copied once and the copy zeroed before this returns. The witness's tables and
/// value lists are zeroed when dropped; the prover's own internal copies are not reachable from
/// here.
pub fn prove(keys: &Keys, statement: &Statement, holder: &Holder) -> Result<Proved, Error> {
  let seed: Zeroizing<[u8; SEED_BYTES]> = Zeroizing::new(fixed(holder.secret_seed, "secret_seed")?);
  guarded(|| {
    let (public, verifier_input) = public(statement)?;
    let device: [u8; 64] = fixed(holder.device_signature, "device signature")?;
    let device =
      Signature::from_rs(&fixed(&device[..32], "device r")?, &fixed(&device[32..], "device s")?);
    let m = mdoc(holder.issuer_signed)?;
    let pseudonym = pseudonym::pseudonym(&seed, &verifier_input);
    let messages =
      NymMessages { ssc: m.item(SSC)?, secret_seed: &seed, verifier_input: &verifier_input };
    let issuer = Signature::from_rs(&m.r, &m.s);
    let witness = MdocWitness::full(
      &m.sig_structure,
      m.item(BIRTH_DATE)?,
      messages,
      public.issuer_key,
      issuer,
    )
    .map_err(|e| Error::Refused(Refusal::new(RefusalCode::Credential, &e)))?;
    let table = witness.table.clone();
    let core_public = public.clone();
    let core = MdocNymCore {
      witness: Some(Arc::new(witness)),
      presentation: Some(Presentation { public, device_signature: device }),
      nym: Some(NymPublic { verifier_input, pseudonym }),
    };
    // The prover does not check the rules: it would commit to any values and produce a proof that
    // no verifier accepts. Find the first broken rule of the core here.
    if let Some(rule) = app::first_broken(&core)
      .map_err(|_| Error::Prover("the witness could not be synthesized".into()))?
    {
      return Err(Error::Refused(Refusal::of_rule(&rule)));
    }
    let assignment = app::witness(&app::steps(&table), &core)
      .map_err(|_| Error::Prover("the witness could not be synthesized".into()))?;
    let (steps, core) = (assignment.steps(), assignment.core());
    let prepared = app::prepare(&keys.prover, &steps, &core)
      .map_err(|e| Error::Prover(format!("prepare: {e:?}")))?;
    let (proof, _) = app::prove(&keys.prover, &steps, &core, prepared)
      .map_err(|e| Error::Prover(format!("prove: {e:?}")))?;
    // Never hand out a proof the verifier would refuse (a rule of a step instance, which the
    // check above does not cover, broken by the inputs).
    let mut expected = core_public.values(TimeEncoding::Digits);
    expected.extend(NymPublic::verifier_values(&verifier_input));
    app::accept_pseudonym(&FULL_MDOC, &keys.verifier, &proof, &expected)
      .map_err(|_| Error::Prover("the proof failed its own verification".into()))?;
    let proof = bincode::serialize(&proof).map_err(|e| Error::Prover(format!("encoding: {e}")))?;
    Ok(Proved { proof, pseudonym })
  })
}

/// Accepts a proof for the values the verifier named and returns the pseudonym it reveals.
///
/// `statement`'s time, challenge digest and verifier_input must be computed by the verifier from
/// its own clock, request and identifier, never read from the presentation (see the module's
/// integration contract). The same input validation as [`prove`] applies, the proof must be at
/// most [`MAX_PROOF`] bytes and have no bytes after its end.
pub fn verify(keys: &Keys, statement: &Statement, proof: &[u8]) -> Result<[u8; 32], Error> {
  guarded(|| {
    let (public, verifier_input) = public(statement)?;
    if proof.len() > MAX_PROOF {
      return Err(Error::Input(format!("the proof is {} bytes, more than {MAX_PROOF}", proof.len())));
    }
    let decoded: Proof =
      bincode::deserialize(proof).map_err(|e| Error::Input(format!("decoding the proof: {e}")))?;
    // bincode reads a prefix and ignores what follows: accept only a proof that is its own
    // encoding, with no trailing bytes.
    match bincode::serialized_size(&decoded) {
      Ok(n) if n == proof.len() as u64 => {}
      _ => return Err(Error::Input("the proof has bytes after its end".into())),
    }
    let mut expected = public.values(TimeEncoding::Digits);
    expected.extend(NymPublic::verifier_values(&verifier_input));
    app::accept_pseudonym(&FULL_MDOC, &keys.verifier, &decoded, &expected).map_err(|r| match r {
      Rejection::Invalid(e) => Error::ProofInvalid(format!("{e:?}")),
      Rejection::Position { instance, .. } => {
        Error::Mismatch(format!("step instance {instance} reports another position"))
      }
      Rejection::PublicValues { .. } => {
        Error::Mismatch("the proof's public values are not the named ones".into())
      }
    })
  })
}

/// The pseudonym the rulebook derives, for callers that check the prover's against it.
pub fn pseudonym_of(secret_seed: &[u8], verifier_input: &[u8]) -> Result<[u8; 32], Error> {
  let seed: Zeroizing<[u8; SEED_BYTES]> = Zeroizing::new(fixed(secret_seed, "secret_seed")?);
  Ok(pseudonym::pseudonym(&seed, &fixed(verifier_input, "verifier input")?))
}
