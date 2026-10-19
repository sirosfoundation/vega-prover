// SPDX-License-Identifier: MIT
//! Adversarial and hardening tests of `statement`: circuit pinning, shape validation, the range
//! rule, input parsing, the CBOR reader's limits, proof framing, coarse refusals and secret
//! residue. Credentials are synthetic (test issuer and device keys of `fixtures::KeyPair`), so
//! every honest control is a real signature. Several tests were adapted from the independent
//! red-team review of the first version.

use std::sync::OnceLock;

use serde::{Deserialize, Serialize};
use vega_nymauth::app;
use vega_nymauth::fixtures::cbor::{Item, MAX_DEPTH, MAX_INPUT, Value, record, text};
use vega_nymauth::fixtures::mdoc::{full_date, issue, item_bytes};
use vega_nymauth::fixtures::{KeyPair, VALID_UNTIL, salt};
use vega_nymauth::presentation::Date;
use vega_nymauth::statement::{
  self, APPROVED_SHAPES, DOC_TYPE, Error, Holder, Keys, MAX_PROOF, RefusalCode,
  Statement,
};
use vega_nymauth::table::{FULL_MDOC, sha256};
use vega_prover::provider::pt256::t256;

const VI: [u8; 32] = [7u8; 32];
const TIME: &str = "2026-10-07T12:00:00Z";
const MSG: &[u8] = b"hardening-challenge-message";

/// A synthetic credential and everything a verifier names for it.
#[derive(Clone)]
struct Case {
  issuer_signed: Vec<u8>,
  seed: [u8; 16],
  dev_rs: [u8; 64],
  qx: Vec<u8>,
  qy: Vec<u8>,
  e2: Vec<u8>,
  time: String,
  earliest: String,
  cutoff: String,
}

fn case(seed: [u8; 16]) -> Case {
  let issuer = KeyPair::from_label("hardening issuer");
  let device = KeyPair::from_label("hardening device");
  let items = vec![
    (
      "birth_date".to_string(),
      item_bytes(0, &salt("h b"), "birth_date", full_date(&Date { year: 1990, month: 5, day: 17 })),
    ),
    ("ssc".to_string(), item_bytes(1, &salt("h s"), "ssc", Value::Bytes(sha256(&seed).to_vec()))),
  ];
  let mdoc = issue(&issuer, &device.public, &VALID_UNTIL, DOC_TYPE, items);
  let payload = Item::read(&mdoc.sig_structure).unwrap().at(3).unwrap().content().to_vec();
  let mut sig = mdoc.signature.r.to_vec();
  sig.extend_from_slice(&mdoc.signature.s);
  let ns = Value::Map(vec![(
    text(DOC_TYPE),
    Value::Array(mdoc.items.iter().map(|(_, b)| Value::Encoded(b.clone())).collect()),
  )]);
  let auth = Value::Array(vec![
    Value::Bytes(vec![0xa1, 0x01, 0x26]),
    Value::Map(vec![]),
    Value::Bytes(payload),
    Value::Bytes(sig),
  ]);
  let issuer_signed = record(vec![("nameSpaces", ns), ("issuerAuth", auth)]).encode();
  let ds = device.sign(MSG);
  let mut dev_rs = [0u8; 64];
  dev_rs[..32].copy_from_slice(&ds.r);
  dev_rs[32..].copy_from_slice(&ds.s);
  Case {
    issuer_signed,
    seed,
    dev_rs,
    qx: issuer.public.x.to_vec(),
    qy: issuer.public.y.to_vec(),
    e2: sha256(MSG).to_vec(),
    time: TIME.into(),
    earliest: "0000-00-00".into(),
    cutoff: "2008-10-07".into(),
  }
}

impl Case {
  fn statement(&self) -> Statement<'_> {
    Statement {
      issuer_key_x: &self.qx,
      issuer_key_y: &self.qy,
      time: &self.time,
      earliest: &self.earliest,
      cutoff: &self.cutoff,
      challenge_digest: &self.e2,
      verifier_input: &VI,
    }
  }

  fn holder(&self) -> Holder<'_> {
    Holder { issuer_signed: &self.issuer_signed, secret_seed: &self.seed, device_signature: &self.dev_rs }
  }
}

fn shapes() -> &'static Vec<u8> {
  static S: OnceLock<Vec<u8>> = OnceLock::new();
  S.get_or_init(|| statement::shapes().unwrap())
}

fn keys() -> &'static Keys {
  static K: OnceLock<Keys> = OnceLock::new();
  K.get_or_init(|| Keys::from_shapes(shapes()).unwrap())
}

fn honest() -> &'static (Case, Vec<u8>) {
  static H: OnceLock<(Case, Vec<u8>)> = OnceLock::new();
  H.get_or_init(|| {
    let c = case(*b"hardening-seed-1");
    let proved = statement::prove(keys(), &c.statement(), &c.holder()).unwrap();
    (c, proved.proof)
  })
}

// ---- CIRCUIT-1: pinned shapes ------------------------------------------------------------

#[derive(Serialize, Deserialize, Clone)]
struct SMatrix {
  data: Vec<t256::Scalar>,
  indices: Vec<usize>,
  indptr: Vec<usize>,
  cols: usize,
}

#[derive(Serialize, Deserialize, Clone)]
struct SShape {
  num_cons: usize,
  num_cons_unpadded: usize,
  num_shared_unpadded: usize,
  num_precommitted_unpadded: usize,
  num_rest_unpadded: usize,
  num_shared: usize,
  num_precommitted: usize,
  num_rest: usize,
  num_public: usize,
  num_challenges: usize,
  a: SMatrix,
  b: SMatrix,
  c: SMatrix,
}

fn parse_shapes() -> (SShape, SShape) {
  bincode::deserialize(shapes()).expect("the mirror struct matches the layout")
}

fn hex(b: &[u8]) -> String {
  b.iter().map(|x| format!("{x:02x}")).collect()
}

#[test]
fn the_pinned_digest_is_the_circuit_built_from_source() {
  assert!(APPROVED_SHAPES.iter().any(|(_, d)| *d == hex(&sha256(shapes()))));
  assert_eq!(
    APPROVED_SHAPES[0].1,
    "4da5e73afb9be2682e70be793c9956a73304e21f31246aa10da0d3e95c926425"
  );
}

#[test]
fn weakened_shapes_are_refused_as_an_unknown_circuit() {
  let (step, core) = parse_shapes();
  assert_eq!(bincode::serialize(&(step.clone(), core.clone())).unwrap(), *shapes());
  // Drop every rule of the core: a verifier built from these accepts a wrong-seed proof.
  let mut weak = core.clone();
  for m in [&mut weak.a, &mut weak.b, &mut weak.c] {
    m.data.clear();
    m.indices.clear();
    m.indptr = vec![0; m.indptr.len()];
  }
  let weak_bytes = bincode::serialize(&(step, weak)).unwrap();
  // The shapes are well formed: the loader below the pin takes them.
  assert!(app::setup_from_shapes_in(&FULL_MDOC, &weak_bytes).is_ok());
  match Keys::from_shapes(&weak_bytes) {
    Err(Error::UnknownCircuit(digest)) => assert_eq!(digest, hex(&sha256(&weak_bytes))),
    other => panic!("expected UnknownCircuit, got {:?}", other.map(|_| ())),
  }
  let mut flipped = shapes().clone();
  let mid = flipped.len() / 2;
  flipped[mid] ^= 1;
  assert!(matches!(Keys::from_shapes(&flipped), Err(Error::UnknownCircuit(_))));
}

// ---- CIRCUIT-6: shape consistency ----------------------------------------------------------

fn shape_refused(edit: impl FnOnce(&mut SShape), what: &str) {
  let (step, mut core) = parse_shapes();
  edit(&mut core);
  let bytes = bincode::serialize(&(step, core)).unwrap();
  let t = std::time::Instant::now();
  let r = app::setup_from_shapes_in(&FULL_MDOC, &bytes);
  assert!(r.is_err(), "{what}: inconsistent shapes were accepted");
  assert!(t.elapsed().as_secs() < 5, "{what}: refusal was not immediate");
}

#[test]
fn inconsistent_shapes_are_refused_before_any_allocation() {
  shape_refused(|s| s.num_rest_unpadded = 1 << 34, "unpadded rest bomb");
  shape_refused(|s| s.num_cons_unpadded = 1 << 34, "unpadded constraint bomb");
  shape_refused(|s| s.num_shared_unpadded = s.num_shared + 1, "unpadded shared past padded");
  shape_refused(|s| s.a.indices[0] = s.a.cols, "index past the columns");
  shape_refused(
    |s| {
      let n = s.b.indptr.len() / 2;
      s.b.indptr.swap(n, n + 1);
    },
    "decreasing row pointers",
  );
  shape_refused(|s| s.c.indices.pop().map(|_| ()).unwrap_or(()), "indices shorter than data");
  shape_refused(|s| s.a.cols += 1, "wrong column count");
  // and the honest shapes pass the same validation
  assert!(app::setup_from_shapes_in(&FULL_MDOC, shapes()).is_ok());
}

// ---- CIRCUIT-2: the range rule -------------------------------------------------------------

#[test]
fn the_rulebook_range_rule_is_enforced_by_prove_and_verify() {
  let (c, proof) = honest();
  for (earliest, cutoff, what) in [
    ("1990-05-17", "1990-05-17", "a one-day window"),
    ("1990-05-17", "1991-05-15", "364 days"),
    ("2000-01-01", "1999-01-01", "le before ge"),
  ] {
    let mut t = c.clone();
    t.earliest = earliest.into();
    t.cutoff = cutoff.into();
    let r = statement::prove(keys(), &t.statement(), &t.holder());
    assert!(matches!(r, Err(Error::Input(ref m)) if m.contains("age range") || m.contains("rulebook")), "{what}: prove {r:?}");
    let r = statement::verify(keys(), &t.statement(), proof);
    assert!(matches!(r, Err(Error::Input(_))), "{what}: verify {r:?}");
  }
  // 365 days (1990-05-17 to 1991-05-16 inclusive) is the smallest allowed window.
  assert!(statement::check_range("1990-05-17", "1991-05-16").is_ok());
  assert!(statement::check_range("1990-05-17", "1991-05-15").is_err());
  // A leap year: 2020-02-29 to 2021-02-27 is 365 days.
  assert!(statement::check_range("2020-02-29", "2021-02-27").is_ok());
  // An open bound is not a window.
  assert!(statement::check_range("0000-00-00", "2008-10-07").is_ok());
  assert!(statement::check_range("1990-05-17", "9999-12-31").is_ok());
  assert!(statement::check_range("0000-00-00", "9999-12-31").is_ok());
}

// ---- CIRCUIT-9: digit-only, calendar-valid times and dates -----------------------------------

#[test]
fn times_and_dates_are_digits_only_and_real_calendar_values() {
  let (c, proof) = honest();
  for bad in [
    "2026-10-07T+1:00:00Z",
    "2026-10-07T 1:00:00Z",
    "2026-13-45T99:99:99Z",
    "2026-02-30T12:00:00Z",
    "2026-10-07T24:00:00Z",
    "2026-10-07T12:00:60Z",
    "+026-10-07T12:00:00Z",
  ] {
    let mut t = c.clone();
    t.time = bad.into();
    assert!(matches!(statement::verify(keys(), &t.statement(), proof), Err(Error::Input(_))), "{bad}");
  }
  for bad in ["2008-02-30", "2008-1-07x", "+008-10-07", "2008-10- 7", "0000-01-01"] {
    let mut t = c.clone();
    t.cutoff = bad.into();
    assert!(matches!(statement::verify(keys(), &t.statement(), proof), Err(Error::Input(_))), "{bad}");
  }
  // a valid leap day passes the parser
  let mut t = c.clone();
  t.cutoff = "2008-02-29".into();
  assert!(!matches!(statement::verify(keys(), &t.statement(), proof), Err(Error::Input(_))));
}

// ---- CIRCUIT-8: host-side issuer key validation ---------------------------------------------

#[test]
fn an_issuer_key_off_the_curve_or_out_of_range_is_refused() {
  let (c, proof) = honest();
  let refused = |t: &Case| {
    matches!(statement::verify(keys(), &t.statement(), proof), Err(Error::Input(ref m)) if m.contains("P-256"))
      && matches!(statement::prove(keys(), &t.statement(), &t.holder()), Err(Error::Input(ref m)) if m.contains("P-256"))
  };
  let mut t = c.clone();
  t.qy[31] ^= 1;
  assert!(refused(&t), "off the curve");
  let mut t = c.clone();
  t.qx = vec![0xff; 32];
  assert!(refused(&t), "x above the field prime");
  let mut t = c.clone();
  t.qx = vec![0; 32];
  t.qy = vec![0; 32];
  assert!(refused(&t), "the all-zero encoding");
  // The honest key passes.
  assert!(statement::verify(keys(), &c.statement(), proof).is_ok());
}

// ---- CIRCUIT-3: coarse refusals --------------------------------------------------------------

fn refusal(c: &Case) -> RefusalCode {
  match statement::prove(keys(), &c.statement(), &c.holder()) {
    Err(Error::Refused(r)) => {
      // The text the caller sees never carries a rule path.
      let shown = format!("{:?} {}", r.code, Error::Refused(r.clone()));
      assert!(!shown.contains('/') && !shown.contains("digest half"), "{shown}");
      #[cfg(feature = "debug-rules")]
      assert!(r.rule.contains('/'), "the debug feature carries the rule: {:?}", r.rule);
      #[cfg(not(feature = "debug-rules"))]
      assert!(!format!("{r:?}").contains('/'), "{r:?}");
      r.code
    }
    other => panic!("expected a refusal, got {:?}", other.map(|_| ())),
  }
}

#[test]
fn refusals_are_coarse_codes() {
  let (c, _) = honest();
  let mut t = c.clone();
  t.seed[0] ^= 1;
  assert_eq!(refusal(&t), RefusalCode::SeedMismatch);
  let mut t = c.clone();
  t.dev_rs[7] ^= 1;
  assert_eq!(refusal(&t), RefusalCode::DeviceSignature);
  let other = KeyPair::from_label("another issuer").public;
  let mut t = c.clone();
  t.qx = other.x.to_vec();
  t.qy = other.y.to_vec();
  assert_eq!(refusal(&t), RefusalCode::IssuerSignature);
}

// ---- CIRCUIT-5: the CBOR reader's limits -----------------------------------------------------

#[test]
fn hostile_cbor_is_an_error_not_a_crash() {
  let (c, _) = honest();
  // Nesting of a million arrays: the reader stops at MAX_DEPTH (and the input is under the cap).
  let mut bomb = vec![0x81u8; 1_000_000];
  bomb.push(0x00);
  assert!(bomb.len() < MAX_INPUT);
  let h = Holder { issuer_signed: &bomb, secret_seed: &c.seed, device_signature: &c.dev_rs };
  assert!(matches!(statement::prove(keys(), &c.statement(), &h), Err(Error::Input(_))));
  assert!(Item::read(&bomb).is_err());
  // Exactly the cap deep reads; one deeper does not.
  let mut ok = vec![0x81u8; MAX_DEPTH];
  ok.push(0x00);
  assert!(Item::read(&ok).is_ok());
  let mut deep = vec![0x81u8; MAX_DEPTH + 1];
  deep.push(0x00);
  assert!(Item::read(&deep).is_err());
  // A string length that overflows usize arithmetic, and one that merely exceeds the input.
  for head in [[0x5b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff], [0x5b, 0, 0, 0, 0, 0, 0, 1, 0]] {
    assert!(Item::read(&head).is_err());
  }
  // Input past the size cap.
  let big = vec![0u8; MAX_INPUT + 1];
  assert!(Item::read(&big).is_err());
  let big = vec![0u8; statement::MAX_ISSUER_SIGNED + 1];
  let h = Holder { issuer_signed: &big, secret_seed: &c.seed, device_signature: &c.dev_rs };
  assert!(matches!(statement::prove(keys(), &c.statement(), &h), Err(Error::Input(_))));
  // A map where an array is expected, and a byte string for nameSpaces: typed, not a panic.
  let odd = record(vec![("nameSpaces", Value::Bytes(vec![1])), ("issuerAuth", Value::Array(vec![]))]).encode();
  let h = Holder { issuer_signed: &odd, secret_seed: &c.seed, device_signature: &c.dev_rs };
  assert!(matches!(statement::prove(keys(), &c.statement(), &h), Err(Error::Input(_))));
}

// ---- CIRCUIT-6: proof framing ------------------------------------------------------------------

#[test]
fn a_proof_with_trailing_bytes_or_past_the_cap_is_refused() {
  let (c, proof) = honest();
  assert!(statement::verify(keys(), &c.statement(), proof).is_ok());
  let mut longer = proof.clone();
  longer.push(0);
  assert!(matches!(statement::verify(keys(), &c.statement(), &longer), Err(Error::Input(_))));
  let mut padded = proof.clone();
  padded.extend(std::iter::repeat_n(0u8, 1 << 20));
  assert!(matches!(statement::verify(keys(), &c.statement(), &padded), Err(Error::Input(_))));
  assert!(padded.len() > MAX_PROOF);
}

// ---- CIRCUIT-4: secret residue -----------------------------------------------------------------

/// Counts the occurrences of `needle` in this process's writable memory (Linux).
fn scan(needle: &[u8]) -> usize {
  use std::io::{Read, Seek, SeekFrom};
  let maps = std::fs::read_to_string("/proc/self/maps").unwrap();
  let mut mem = std::fs::File::open("/proc/self/mem").unwrap();
  let mut hits = 0;
  for line in maps.lines() {
    let mut it = line.split_whitespace();
    let (range, perms) = (it.next().unwrap(), it.next().unwrap());
    let name = line.split_whitespace().nth(5).unwrap_or("");
    if !perms.starts_with("rw") || name == "[vvar]" || name == "[vsyscall]" {
      continue;
    }
    let (a, b) = range.split_once('-').unwrap();
    let (a, b) = (u64::from_str_radix(a, 16).unwrap(), u64::from_str_radix(b, 16).unwrap());
    let (mut off, mut buf) = (a, vec![0u8; 1 << 20]);
    while off < b {
      let n = ((b - off) as usize).min(buf.len());
      if mem.seek(SeekFrom::Start(off)).is_err() || mem.read_exact(&mut buf[..n]).is_err() {
        break;
      }
      hits += buf[..n].windows(needle.len()).filter(|w| *w == needle).count();
      off += n as u64;
    }
  }
  hits
}

/// After `prove`, with the caller's own buffer zeroed, no copy of the seed should remain that the
/// call put there. The count is compared with a control taken just before (the test's own needle
/// and stale stack copies from building the credential); `prove` must add none. The prover's
/// internal state (commitment work, thread stacks) is not reachable from this crate, so a copy
/// there would show as an increase and fail this test: today there is none.
#[cfg(target_os = "linux")]
#[test]
fn prove_leaves_no_copy_of_the_seed_behind() {
  let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
  let needle: Vec<u8> = sha256(&nanos.to_le_bytes())[..16].to_vec();
  let mut c = case(needle.clone().try_into().unwrap());
  c.seed.fill(0);
  let _ = keys();
  // The caller's buffer, filled only for the call.
  let mut buffer = vec![0u8; 16];
  let control = scan(&needle);
  buffer.copy_from_slice(&needle);
  let holder = Holder { issuer_signed: &c.issuer_signed, secret_seed: &buffer, device_signature: &c.dev_rs };
  let during = scan(&needle);
  let proved = statement::prove(keys(), &c.statement(), &holder).expect("prove");
  buffer.fill(0);
  std::hint::black_box(&buffer);
  let after = scan(&needle);
  assert_eq!(proved.pseudonym, statement::pseudonym_of(&needle, &VI).unwrap());
  eprintln!("seed copies: control {control}, with the caller's buffer {during}, after prove and zeroing it {after}");
  assert!(after <= control, "prove left {} copies of the seed behind", after - control);
}
