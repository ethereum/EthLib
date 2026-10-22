import EthLib.Cryptography.Bls.HashToCurve
import EthLib.Cryptography.Bls.Pairing
import EthLib.Cryptography.Bls.Errors

/-!
# `Signatures`

BLS signature verification per IRTF draft-irtf-cfrg-bls-signature, plus
the Ethereum wrappers `eth_aggregate_pubkeys` and `eth_fast_aggregate_verify`.

The Ethereum consensus uses the proof-of-possession (POP) scheme with
G1 pubkeys / G2 signatures; the DST is fixed as
`BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_`.
-/

namespace EthLib.Cryptography.Bls.Signatures

open EthLib.Cryptography.Bls

/-- DST for the POP-scheme G2 hash-to-curve. -/
def DST : ByteArray :=
  String.toUTF8 "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_"

/-- Compressed-G2 encoding of the point at infinity (96 bytes; high
bits of byte 0 set to compressed+infinity). -/
def G2_POINT_AT_INFINITY : ByteArray := G2.infinityBytes

/-- IRTF `signature_subgroup_check`. Slow but correct. -/
private def signatureSubgroupCheck (sig : G2) : Bool := G2.inSubgroup sig

/-- IRTF `CoreVerify`: pairing-equation check `e(P, R) · e(-PK, Q) == 1`. -/
private def coreVerify
    (pkBytes : ByteArray) (msg : ByteArray) (sigBytes : ByteArray) : Bool :=
  -- Validate pubkey (subgroup, on-curve, not infinity).
  if pkBytes.size ≠ 48 || !(G1.keyValidate pkBytes).isOk then false
  else match G1.uncompress pkBytes with
  | .error _ => false
  | .ok pk =>
    -- Validate signature: decompress, on-curve (implicit), in subgroup.
    if sigBytes.size ≠ 96 then false
    else match G2.uncompress sigBytes with
    | .error _ => false
    | .ok sig =>
      if !signatureSubgroupCheck sig then false
      else
        match HashToCurve.hashToG2 msg DST with
        | .error _ => false
        | .ok q =>
          Bls.pairingCheck #[
            (G1.generator, sig),
            (G1.neg pk, q)
          ]

/-- IRTF `FastAggregateVerify` for a single message: aggregate pubkeys
then verify. Returns `false` on invalid encodings. -/
def fastAggregateVerify
    (pubkeys : Array ByteArray) (msg : ByteArray) (sigBytes : ByteArray) : Bool := Id.run do
  if pubkeys.isEmpty then return false
  let mut agg : G1 := G1.zero
  for pk in pubkeys do
    if pk.size ≠ 48 || !(G1.keyValidate pk).isOk then return false
    match G1.uncompress pk with
    | .error _ => return false
    | .ok p => agg := G1.add agg p
  let aggBytes := G1.compress agg
  return coreVerify aggBytes msg sigBytes

/-! ## Ethereum wrappers -/

/-- `eth_aggregate_pubkeys` — sum compressed G1 pubkeys after `KeyValidate`.
Fails with a `BlsError` on an empty list or any invalid pubkey. -/
def ethAggregatePubkeys (pubkeys : Array ByteArray) : Except BlsError ByteArray := do
  if pubkeys.isEmpty then
    throw .emptyPubkeyList
  let mut agg : G1 := G1.zero
  for i in [:pubkeys.size] do
    let pk := pubkeys[i]!
    if pk.size ≠ 48 then
      throw (.badPubkeySize pk.size)
    if !(G1.keyValidate pk).isOk then
      throw (.invalidPubkey (some i))
    match G1.uncompress pk with
    | .error _ => throw (.invalidPubkey (some i))
    | .ok p => agg := G1.add agg p
  return G1.compress agg

/-- `eth_fast_aggregate_verify` — Ethereum's special-cased FastAggregateVerify.
Returns `true` for empty pubkeys iff the signature is the G2 point at
infinity; otherwise delegates to `FastAggregateVerify`. -/
def ethFastAggregateVerify
    (pubkeys : Array ByteArray) (msg : ByteArray) (sigBytes : ByteArray) : Bool :=
  if pubkeys.isEmpty then
    sigBytes = G2_POINT_AT_INFINITY
  else
    fastAggregateVerify pubkeys msg sigBytes

end EthLib.Cryptography.Bls.Signatures
