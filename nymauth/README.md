# vega-nymauth

The nym_auth statement for mdoc credentials, proved with Vega: from an mdoc whose issuer signed
`birth_date` and `ssc`, the holder proves an age range and reveals a pseudonym specific to the
verifier, without showing the credential. Port of the reference `vega-age` crate and the
`nymauth-vega` reference program of the nym_auth circuits archive (`SPEC.md` V1 to V6).

This crate is a sibling of `vega-prover`, not a workspace member: it depends on the prover by path
(`vega-prover = { path = ".." }`) and no file of the prover is changed, so the prover's history
merges from upstream without conflicts.

- `statement`: the application API. `Keys::from_shapes(shapes)`, `prove`, `verify`, `shapes`.
- `app`, `table`, `step`, `mdoc`, `presentation`, `pseudonym`, `request`, `challenge`, `gadgets`:
  the circuits and the hand-written witness (see the archive's `SPEC.md`).
- `fixtures`: test credentials and a CBOR reader (the reader also parses real `IssuerSigned`).

Scope: mdoc, configuration `known-offender-matching-ssc`. SD-JWT VC circuits are in the crate
(`sdjwt`), but `statement` does not expose them: their challenge needs the verifier's nonce,
client_id and origin.

Tests (`cargo test --release` in this directory) prove and verify over the archive's reference
credential (`tests/credential/`), check the pseudonym against the archive's value, accept the
archive's own proof, pin the shapes built from source to the published ones, and refuse tampered
inputs.
