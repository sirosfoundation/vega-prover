//! End to end over the reference credential (`tests/credential/`, from the nym_auth circuits
//! archive): a real proof verifies, the pseudonym is the archive's, and every tampered input is
//! refused. Keys and the one honest proof are built once.

use std::path::PathBuf;
use std::sync::OnceLock;

use serde_json::Value as Json;
use vega_nymauth::fixtures::cbor::Item;
use vega_nymauth::gadgets::base64;
use vega_nymauth::statement::{self, Error, Holder, Keys, Proved, Statement};

fn dir() -> PathBuf {
  PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/credential")
}

fn json(name: &str) -> Json {
  serde_json::from_slice(&std::fs::read(dir().join(name)).unwrap()).unwrap()
}

fn unhex(s: &str) -> Vec<u8> {
  (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect()
}

fn s<'a>(j: &'a Json, path: &[&str]) -> &'a str {
  path.iter().fold(j, |j, k| &j[*k]).as_str().unwrap()
}

/// Everything the first verifier of the fixtures names or holds.
#[derive(Clone)]
struct Inputs {
  qx: Vec<u8>,
  qy: Vec<u8>,
  time: String,
  earliest: String,
  cutoff: String,
  challenge: Vec<u8>,
  verifier_input: Vec<u8>,
  issuer_signed: Vec<u8>,
  seed: Vec<u8>,
  device_signature: Vec<u8>,
  pseudonym: Vec<u8>,
}

impl Inputs {
  fn load() -> Self {
    let (req, nym) = (json("verifier.json"), json("pseudonym.json"));
    let (x, y) = s(&req, &["issuer_key"]).split_once(',').unwrap();
    let v = &nym["verifiers"][0];
    let text = std::fs::read_to_string(dir().join("nym-auth-mdoc.txt")).unwrap();
    Inputs {
      qx: unhex(x),
      qy: unhex(y),
      time: s(&req, &["mdoc", "time"]).into(),
      earliest: s(&req, &["mdoc", "earliest"]).into(),
      cutoff: s(&req, &["mdoc", "cutoff"]).into(),
      challenge: unhex(s(v, &["mdoc", "challenge_digest"])),
      verifier_input: unhex(s(v, &["verifier_input"])),
      issuer_signed: base64::decode(text.trim().as_bytes()).unwrap(),
      seed: unhex(s(&nym, &["holder", "secret_seed"])),
      device_signature: unhex(s(v, &["mdoc", "device_signature"])),
      pseudonym: unhex(s(v, &["pseudonym"])),
    }
  }

  fn statement(&self) -> Statement<'_> {
    Statement {
      issuer_key_x: &self.qx,
      issuer_key_y: &self.qy,
      time: &self.time,
      earliest: &self.earliest,
      cutoff: &self.cutoff,
      challenge_digest: &self.challenge,
      verifier_input: &self.verifier_input,
    }
  }

  fn holder(&self) -> Holder<'_> {
    Holder {
      issuer_signed: &self.issuer_signed,
      secret_seed: &self.seed,
      device_signature: &self.device_signature,
    }
  }
}

fn keys() -> &'static Keys {
  static KEYS: OnceLock<Keys> = OnceLock::new();
  KEYS.get_or_init(|| Keys::from_shapes(&statement::shapes().unwrap()).unwrap())
}

fn honest() -> &'static (Inputs, Proved) {
  static HONEST: OnceLock<(Inputs, Proved)> = OnceLock::new();
  HONEST.get_or_init(|| {
    let i = Inputs::load();
    let proved = statement::prove(keys(), &i.statement(), &i.holder()).unwrap();
    (i, proved)
  })
}

#[test]
fn a_real_proof_verifies_and_reveals_the_fixture_pseudonym() {
  let (i, proved) = honest();
  assert_eq!(proved.pseudonym.to_vec(), i.pseudonym, "the prover's pseudonym");
  let revealed = statement::verify(keys(), &i.statement(), &proved.proof).unwrap();
  assert_eq!(revealed.to_vec(), i.pseudonym, "the pseudonym the verifier learns");
  assert_eq!(
    statement::pseudonym_of(&i.seed, &i.verifier_input).unwrap().to_vec(),
    i.pseudonym
  );
  assert!(proved.proof.len() > 90_000 && proved.proof.len() < 100_000, "proof size {}", proved.proof.len());
}

/// The reference archive's proof (`vega/mdoc/proof.bin`) was made by the pinned upstream
/// prover; ours must read and accept it: the circuits, keys and proof format agree.
#[test]
fn the_archives_own_proof_is_accepted() {
  let path = dir().join("reference-proof.bin");
  let proof = std::fs::read(path).unwrap();
  let i = Inputs::load();
  let revealed = statement::verify(keys(), &i.statement(), &proof).unwrap();
  assert_eq!(revealed.to_vec(), i.pseudonym);
}

#[test]
fn the_shapes_from_source_are_the_archives() {
  let archived = zstd::stream::decode_all(&std::fs::read(dir().join("reference-shapes.zst")).unwrap()[..]).unwrap();
  assert!(statement::shapes().unwrap() == archived, "the shapes built from source differ from the archive's");
}

fn assert_refused_by_verify(edit: impl FnOnce(&mut Inputs), what: &str) {
  let (i, proved) = honest();
  let mut t = i.clone();
  edit(&mut t);
  let result = statement::verify(keys(), &t.statement(), &proved.proof);
  assert!(
    matches!(result, Err(Error::Mismatch(_)) | Err(Error::ProofInvalid(_))),
    "{what}: expected a refusal, got {result:?}"
  );
}

#[test]
fn verify_refuses_another_verifier_input() {
  let other = unhex("5ff3c35cfed806981de9ad610c4a7fe100867aee4530485aed3a0cc6e71f22b1");
  assert_refused_by_verify(|t| t.verifier_input = other, "verifier input");
}

#[test]
fn verify_refuses_another_issuer_key() {
  assert_refused_by_verify(|t| t.qx[31] ^= 1, "Q.x");
  assert_refused_by_verify(|t| t.qy[0] ^= 1, "Q.y");
}

#[test]
fn verify_refuses_another_challenge_time_or_bounds() {
  assert_refused_by_verify(|t| t.challenge[0] ^= 1, "challenge");
  assert_refused_by_verify(|t| t.time = "2026-10-07T12:00:01Z".into(), "time");
  assert_refused_by_verify(|t| t.cutoff = "2008-10-08".into(), "cutoff");
  assert_refused_by_verify(|t| t.earliest = "1900-01-01".into(), "earliest");
}

#[test]
fn verify_refuses_a_damaged_proof() {
  let (i, proved) = honest();
  let mut p = proved.proof.clone();
  let mid = p.len() / 2;
  p[mid] ^= 0x01;
  let r = statement::verify(keys(), &i.statement(), &p);
  assert!(r.is_err(), "a flipped bit must not verify: {r:?}");
  assert!(statement::verify(keys(), &i.statement(), &p[..100]).is_err());
  assert!(statement::verify(keys(), &i.statement(), &[]).is_err());
}

/// A prover given a bad input either refuses (the witness builder checks natively) or produces
/// a proof that verification refuses; it never yields an accepted proof.
fn assert_cannot_prove(edit: impl FnOnce(&mut Inputs), what: &str) {
  let mut t = Inputs::load();
  edit(&mut t);
  match statement::prove(keys(), &t.statement(), &t.holder()) {
    Err(Error::Witness(rule)) => eprintln!("{what}: refused: {rule}"),
    Err(e) => panic!("{what}: unexpected {e:?}"),
    Ok(p) => {
      let honest_statement = Inputs::load();
      let r = statement::verify(keys(), &honest_statement.statement(), &p.proof);
      let r2 = statement::verify(keys(), &t.statement(), &p.proof);
      assert!(r.is_err() && r2.is_err(), "{what}: a proof from bad input was accepted");
    }
  }
}

#[test]
fn prove_with_the_wrong_seed_is_refused() {
  let mut t = Inputs::load();
  t.seed[0] ^= 1;
  let r = statement::prove(keys(), &t.statement(), &t.holder());
  assert!(matches!(&r, Err(Error::Witness(m)) if m.contains("seed digest")), "{r:?}");
}

#[test]
fn prove_with_the_wrong_device_signature_cannot_be_accepted() {
  assert_cannot_prove(|t| t.device_signature[5] ^= 1, "device signature");
}

#[test]
fn prove_with_the_wrong_issuer_key_cannot_be_accepted() {
  assert_cannot_prove(|t| t.qx[0] ^= 1, "Q");
}

#[test]
fn prove_with_the_wrong_verifier_input_cannot_be_accepted_for_the_other_verifier() {
  let (i, proved) = honest();
  // A proof for verifier 1 does not open verifier 2's pseudonym; checked by verify above.
  let other = unhex("5ff3c35cfed806981de9ad610c4a7fe100867aee4530485aed3a0cc6e71f22b1");
  let mut t = i.clone();
  t.verifier_input = other;
  assert!(statement::verify(keys(), &t.statement(), &proved.proof).is_err());
}

#[test]
fn malformed_inputs_are_typed_errors_not_panics() {
  let i = Inputs::load();
  let mut t = i.clone();
  t.issuer_signed = vec![0xff, 0x00];
  assert!(matches!(statement::prove(keys(), &t.statement(), &t.holder()), Err(Error::Input(_))));
  let mut t = i.clone();
  t.issuer_signed.truncate(40);
  assert!(statement::prove(keys(), &t.statement(), &t.holder()).is_err());
  let mut t = i.clone();
  t.seed.pop();
  assert!(matches!(statement::prove(keys(), &t.statement(), &t.holder()), Err(Error::Input(_))));
  let mut t = i.clone();
  t.device_signature.pop();
  assert!(matches!(statement::prove(keys(), &t.statement(), &t.holder()), Err(Error::Input(_))));
  for bad in ["2026-10-07 12:00:00Z", "2026-10-07T12:00:00+", "é026-10-07T12:00:00Z", ""] {
    let mut t = i.clone();
    t.time = bad.into();
    assert!(matches!(statement::verify(keys(), &t.statement(), &[0; 8]), Err(Error::Input(_))), "{bad}");
  }
  let mut t = i.clone();
  t.cutoff = "20081007xx".into();
  assert!(matches!(statement::verify(keys(), &t.statement(), &[0; 8]), Err(Error::Input(_))));
  assert!(matches!(Keys::from_shapes(&[1, 2, 3]), Err(Error::Shapes(_))));
  assert!(matches!(Keys::from_shapes(&[]), Err(Error::Shapes(_))));
  let _ = Item::read; // the CBOR reader is the one the statement uses
}
