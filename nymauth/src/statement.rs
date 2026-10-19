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
//! No function here panics: a panic in the witness or the prover is caught and returned as
//! [`Error::Internal`]. The copy of `secret_seed` this module makes is zeroed on every path; the
//! witness builder holds its own copies of the seed's bytes while it runs, which the library
//! cannot reach.

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;

use zeroize::Zeroizing;

use crate::app::{self, Proof, ProverKey, Rejection, VerifierKey};
use crate::fixtures::cbor::{Item, Value, text};
use crate::gadgets::p256::{PublicKey, Signature};
use crate::mdoc::{MdocNymCore, MdocWitness};
use crate::presentation::{Date, Presentation, Public, Time, TimeEncoding};
use crate::pseudonym::{self, NymMessages, NymPublic};
use crate::request::Request;
use crate::table::FULL_MDOC;

/// The docType of a nym_auth mdoc.
pub const DOC_TYPE: &str = "eu.europa.ec.eudi.nym_auth.1";
/// The element that holds the birth date.
pub const BIRTH_DATE: &str = "birth_date";
/// The element that holds SHA-256(secret_seed).
pub const SSC: &str = "ssc";
/// The length of `secret_seed` in bytes.
pub const SEED_BYTES: usize = 16;

/// Why a statement could not be proved, or a proof was not accepted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
  /// An input is malformed: a length, a date, a time, or the credential's structure. The text
  /// names the input and never holds the seed.
  Input(String),
  /// The circuits as data (the shapes) are unreadable or past the budget.
  Shapes(String),
  /// The witness could not be built: the values do not satisfy the rules the witness builder
  /// checks natively (for instance a secret_seed that does not open `ssc`).
  Witness(String),
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
    let (kind, text) = match self {
      Error::Input(t) => ("invalid input", t),
      Error::Shapes(t) => ("invalid circuit shapes", t),
      Error::Witness(t) => ("witness refused", t),
      Error::Prover(t) => ("prover failed", t),
      Error::ProofInvalid(t) => ("proof invalid", t),
      Error::Mismatch(t) => ("proof does not match the named values", t),
      Error::Internal(t) => ("internal error", t),
    };
    write!(f, "{kind}: {text}")
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
  pub fn from_shapes(shapes: &[u8]) -> Result<Self, Error> {
    guarded(|| {
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

fn fixed<const N: usize>(bytes: &[u8], what: &str) -> Result<[u8; N], Error> {
  bytes.try_into().map_err(|_| Error::Input(format!("{what} is {} bytes, not {N}", bytes.len())))
}

fn date(s: &str) -> Result<Date, Error> {
  let n = |r: std::ops::Range<usize>| s.get(r).and_then(|t| t.parse::<u32>().ok());
  let digits = s.bytes().enumerate().all(|(i, b)| if i == 4 || i == 7 { b == b'-' } else { b.is_ascii_digit() });
  match (s.len(), digits, n(0..4), n(5..7), n(8..10)) {
    (10, true, Some(year), Some(month), Some(day)) => Ok(Date { year, month, day }),
    _ => Err(Error::Input(format!("not a date YYYY-MM-DD: {s:?}"))),
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
  let n = |r: std::ops::Range<usize>| s.get(r).and_then(|t| t.parse::<u32>().ok());
  match (n(11..13), n(14..16), n(17..19)) {
    (Some(hour), Some(minute), Some(second)) => {
      Ok(Time { date: date(&s[..10])?, hour, minute, second })
    }
    _ => Err(bad()),
  }
}

/// The public values from a statement.
fn public(statement: &Statement) -> Result<(Public, [u8; 32]), Error> {
  let issuer_key = PublicKey {
    x: fixed(statement.issuer_key_x, "issuer key x")?,
    y: fixed(statement.issuer_key_y, "issuer key y")?,
  };
  let born_from = if statement.earliest == "0000-00-00" { None } else { Some(date(statement.earliest)?) };
  let public = Public {
    issuer_key,
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
  for entry in root.get(&text("nameSpaces")).map_err(take)?.children().chunks(2) {
    let [_, entries] = entry else { return Err(Error::Input("IssuerSigned: odd nameSpaces".into())) };
    for item in entries.children() {
      let id = item.embedded().map_err(take)?.get(&text("elementIdentifier")).map_err(take)?;
      let id = String::from_utf8(id.content().to_vec())
        .map_err(|_| Error::Input("IssuerSigned: elementIdentifier is not UTF-8".into()))?;
      items.push((id, item.bytes.to_vec()));
    }
  }
  let (r, s) = signature.split_at(32);
  Ok(Mdoc {
    sig_structure,
    r: fixed(r, "r")?,
    s: fixed(s, "s")?,
    items,
  })
}

impl Mdoc {
  fn item(&self, id: &str) -> Result<&[u8], Error> {
    let found = self.items.iter().find(|(name, _)| name == id);
    found.map(|(_, bytes)| &bytes[..]).ok_or_else(|| Error::Input(format!("IssuerSigned has no item {id}")))
  }
}

/// Proves the statement for the verifier's values. Builds the witness (a few milliseconds),
/// prepares and proves. Returns the proof and the pseudonym the holder computes.
///
/// The seed is copied once and the copy zeroed before this returns.
pub fn prove(keys: &Keys, statement: &Statement, holder: &Holder) -> Result<Proved, Error> {
  let seed: Zeroizing<[u8; SEED_BYTES]> = Zeroizing::new(fixed(holder.secret_seed, "secret_seed")?);
  guarded(|| {
    let (public, verifier_input) = public(statement)?;
    let device: [u8; 64] = fixed(holder.device_signature, "device signature")?;
    let device = Signature::from_rs(
      &fixed(&device[..32], "device r")?,
      &fixed(&device[32..], "device s")?,
    );
    let m = mdoc(holder.issuer_signed)?;
    let pseudonym = pseudonym::pseudonym(&seed, &verifier_input);
    let messages = NymMessages { ssc: m.item(SSC)?, secret_seed: &*seed, verifier_input: &verifier_input };
    let issuer = Signature::from_rs(&m.r, &m.s);
    let witness = MdocWitness::full(&m.sig_structure, m.item(BIRTH_DATE)?, messages, public.issuer_key, issuer)
      .map_err(Error::Witness)?;
    let table = witness.table.clone();
    let core_public = public.clone();
    let core = MdocNymCore {
      witness: Some(Arc::new(witness)),
      presentation: Some(Presentation { public, device_signature: device }),
      nym: Some(NymPublic { verifier_input, pseudonym }),
    };
    // The prover does not check the rules: it would commit to any values and produce a proof that
    // no verifier accepts. Find the first broken rule of the core here, with its name.
    match app::first_broken(&core).map_err(|e| Error::Witness(format!("{e:?}")))? {
      Some(rule) => return Err(Error::Witness(format!("the credential or inputs break the rule {rule}"))),
      None => {}
    }
    let assignment =
      app::witness(&app::steps(&table), &core).map_err(|e| Error::Witness(format!("{e:?}")))?;
    let (steps, core) = (assignment.steps(), assignment.core());
    let prepared =
      app::prepare(&keys.prover, &steps, &core).map_err(|e| Error::Prover(format!("prepare: {e:?}")))?;
    let (proof, _) = app::prove(&keys.prover, &steps, &core, prepared)
      .map_err(|e| Error::Prover(format!("prove: {e:?}")))?;
    // Never hand out a proof the verifier would refuse (a rule of a step instance, which the
    // check above does not cover, broken by the inputs).
    let mut expected = core_public.values(TimeEncoding::Digits);
    expected.extend(NymPublic::verifier_values(&verifier_input));
    app::accept_pseudonym(&FULL_MDOC, &keys.verifier, &proof, &expected)
      .map_err(|r| Error::Prover(format!("the proof failed its own verification: {r:?}")))?;
    let proof = bincode::serialize(&proof).map_err(|e| Error::Prover(format!("encoding: {e}")))?;
    Ok(Proved { proof, pseudonym })
  })
}

/// Accepts a proof for the values the verifier named and returns the pseudonym it reveals.
pub fn verify(keys: &Keys, statement: &Statement, proof: &[u8]) -> Result<[u8; 32], Error> {
  guarded(|| {
    let (public, verifier_input) = public(statement)?;
    let proof: Proof =
      bincode::deserialize(proof).map_err(|e| Error::Input(format!("decoding the proof: {e}")))?;
    let mut expected = public.values(TimeEncoding::Digits);
    expected.extend(NymPublic::verifier_values(&verifier_input));
    app::accept_pseudonym(&FULL_MDOC, &keys.verifier, &proof, &expected).map_err(|r| match r {
      Rejection::Invalid(e) => Error::ProofInvalid(format!("{e:?}")),
      Rejection::Position { instance, .. } => {
        Error::Mismatch(format!("step instance {instance} reports another position"))
      }
      Rejection::PublicValues { .. } => Error::Mismatch("the proof's public values are not the named ones".into()),
    })
  })
}

/// The pseudonym the rulebook derives, for callers that check the prover's against it.
pub fn pseudonym_of(secret_seed: &[u8], verifier_input: &[u8]) -> Result<[u8; 32], Error> {
  let seed: Zeroizing<[u8; SEED_BYTES]> = Zeroizing::new(fixed(secret_seed, "secret_seed")?);
  Ok(pseudonym::pseudonym(&seed, &fixed(verifier_input, "verifier input")?))
}
