import EthLib.Cryptography.Bls
import EthLib.Cryptography.Kzg.Constants
import EthLib.Cryptography.Kzg.TrustedSetupData

/-!
# `TrustedSetup`

Holder for the KZG trusted setup (Lagrange-basis G1, monomial-basis
G1, monomial-basis G2).

The compressed bytes are embedded directly in `TrustedSetupData` as
hex strings. At module-init we decode them, decompress to projective
points, and stash both forms in a global ref accessed via
`TrustedSetup.get!`.
-/

namespace EthLib.Cryptography.Kzg

/-- The KZG trusted setup. Each entry is stored as both the projective
G1/G2 point and its compressed-byte form; a few callers consume the
bytes directly. -/
structure TrustedSetup where
  g1Lagrange       : Array Bls.G1
  g1LagrangeBytes  : Array ByteArray
  g1Monomial       : Array Bls.G1
  g1MonomialBytes  : Array ByteArray
  g2Monomial       : Array Bls.G2
  g2MonomialBytes  : Array ByteArray
deriving Inhabited

namespace TrustedSetup

private def nibble (c : Char) : UInt8 :=
  let n := c.toNat
  if 0x30 ≤ n ∧ n ≤ 0x39 then UInt8.ofNat (n - 0x30)
  else if 0x61 ≤ n ∧ n ≤ 0x66 then UInt8.ofNat (n - 0x57)
  else if 0x41 ≤ n ∧ n ≤ 0x46 then UInt8.ofNat (n - 0x37)
  else panic! "invalid hex"

private def hexToBytesAux : List Char → ByteArray → ByteArray
  | [], acc => acc
  | [_], _ => panic! "invalid hex"
  | hi :: lo :: rest, acc =>
    hexToBytesAux rest (acc.push ((nibble hi <<< 4) ||| nibble lo))

private def hexToByteArray (s : String) : ByteArray :=
  hexToBytesAux s.toList ByteArray.empty

private def buildEmbedded : TrustedSetup :=
  let toG1 (b : ByteArray) : Bls.G1 :=
    match Bls.G1.uncompress b with
    | .ok p    => p
    | .error _ => panic! "trusted setup contains invalid G1 point"
  let toG2 (b : ByteArray) : Bls.G2 :=
    match Bls.G2.uncompress b with
    | .ok p    => p
    | .error _ => panic! "trusted setup contains invalid G2 point"
  let g1LagrangeBytes := TrustedSetupData.g1LagrangeHex.map hexToByteArray
  let g1MonomialBytes := TrustedSetupData.g1MonomialHex.map hexToByteArray
  let g2MonomialBytes := TrustedSetupData.g2MonomialHex.map hexToByteArray
  let g1Lagrange := g1LagrangeBytes.map toG1
  let g1Monomial := g1MonomialBytes.map toG1
  let g2Monomial := g2MonomialBytes.map toG2
  {
    g1Lagrange, g1LagrangeBytes,
    g1Monomial, g1MonomialBytes,
    g2Monomial, g2MonomialBytes,
  }

/-! ## Global slot

Seeded eagerly at module-init from the embedded bytes; callers never
have to check whether the setup is loaded. -/

initialize globalRef : IO.Ref TrustedSetup ← IO.mkRef buildEmbedded

/-- Retrieve the loaded setup. -/
@[inline] def get! : IO TrustedSetup := globalRef.get

end TrustedSetup

end EthLib.Cryptography.Kzg
