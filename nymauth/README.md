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

Provenance: the source is the `nym-auth-circuits` archive (`vega/vega-age`, `vega/reference`), our own
work, ported here with the changes listed in the pull request. Licence: MIT, as this repository
(`LICENSE`, SPDX headers in every file).

## Integration contract

The proof shows the statement for the values it is given, so the time `T`, the challenge digest
`e2` and `verifier_input` must come from the verifier (its clock, the request it issued, its own
identifier), never from the holder or the presentation. The issuer key `Q` must be the key the
verifier trusts for the issuer. `statement::verify` checks the rest.

- **Pinned circuit.** `Keys::from_shapes` accepts only shapes whose SHA-256 is in
  `statement::APPROVED_SHAPES`. To approve a new circuit version, append one `(name, digest)` line
  there (after checking `statement::shapes()` reproduces it); to retire one, delete its line.
- **Range rule.** `prove` and `verify` apply the nym_auth rulebook's `age_check` rule: with both
  bounds given, `C < E` or `C - E + 1 < 365` days is refused.
- **Refusals are coarse.** A failed prove returns `Error::Refused` with a `RefusalCode` (seed,
  issuer signature, device signature, credential); the first broken rule is only carried with
  `--features debug-rules`.
- **Issuer profile.** Attribute names are unique under the nym_auth issuance profile; the first
  item with a name is used. An issuer must not issue duplicates.
- **Issuer key.** The circuit does not check that `Q` is a P-256 point; this library does, on the
  host. (Gap for the circuit authors: a circuit-level check would not depend on the host.)
- **Memory.** The witness's tables and value lists are wiped when dropped and the seed copy is
  zeroed; copies inside the prover's own state are not reachable from this crate.
- **Limits.** `IssuerSigned` at most 64 KiB, CBOR depth at most 32, proofs at most 512 KiB with no
  trailing bytes, shapes validated for consistency before any allocation.

Scope: mdoc, configuration `known-offender-matching-ssc`. SD-JWT VC circuits are in the crate
(`sdjwt`), but `statement` does not expose them: their challenge needs the verifier's nonce,
client_id and origin.

Tests (`cargo test --release` in this directory; also with `--features debug-rules`) prove and verify over the archive's reference
credential (`tests/credential/`), check the pseudonym against the archive's value, accept the
archive's own proof, pin the shapes built from source to the published ones, and refuse tampered
inputs.
