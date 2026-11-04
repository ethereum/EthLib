module

public import EthLib.Cryptography.Bls
public import EthLib.Cryptography.Kzg.Constants
public import EthLib.Cryptography.Kzg.Errors
public import EthLib.Cryptography.Kzg.TrustedSetupData

/-!
# `TrustedSetup`

The KZG trusted setup: Lagrange-basis G1 points, monomial-basis G1 points and G2 points.

Every operation that reads the setup takes it as an argument.

A setup decodes from compressed points, or from the embedded hex strings of the ceremony.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Kzg.Constants

/-- The KZG trusted setup.

Each entry is stored as both the decoded point and its compressed bytes.

A few callers consume the bytes directly. -/
structure TrustedSetup where
  g1Lagrange       : Array Bls.G1
  g1LagrangeBytes  : Array ByteArray
  g1Monomial       : Array Bls.G1
  g1MonomialBytes  : Array ByteArray
  g2Monomial       : Array Bls.G2
  g2MonomialBytes  : Array ByteArray
deriving Inhabited

namespace TrustedSetup

/-- The value of one hexadecimal digit, in either case. -/
def nibble? (c : Char) : Option UInt8 :=
  let n := c.toNat
  if 0x30 ≤ n ∧ n ≤ 0x39 then some (UInt8.ofNat (n - 0x30))
  else if 0x61 ≤ n ∧ n ≤ 0x66 then some (UInt8.ofNat (n - 0x57))
  else if 0x41 ≤ n ∧ n ≤ 0x46 then some (UInt8.ofNat (n - 0x37))
  else none

/-- Decode pairs of hexadecimal digits onto `acc`.

An odd number of digits, or a character that is not a digit, gives `none`. -/
def hexToBytesAux : List Char → ByteArray → Option ByteArray
  | [], acc => some acc
  | [_], _ => none
  | hi :: lo :: rest, acc => do
    hexToBytesAux rest (acc.push (((← nibble? hi) <<< 4) ||| (← nibble? lo)))

/-- Decode a hexadecimal string without a `0x` prefix. -/
def hexToBytes? (s : String) : Option ByteArray :=
  hexToBytesAux s.toList ByteArray.empty

/-- Decode a trusted setup from compressed points.

The Deneb specification fixes the lengths of the three lists: 4096, 4096 and 65.

A list of another length, or a point that does not decompress, is rejected.

Decompression checks that a point is on its curve, not that it is in the subgroup. -/
def ofBytes (g1LagrangeBytes g1MonomialBytes g2MonomialBytes : Array ByteArray) :
    Except KzgError TrustedSetup := do
  if g1LagrangeBytes.size ≠ FIELD_ELEMENTS_PER_BLOB ∨
      g1MonomialBytes.size ≠ FIELD_ELEMENTS_PER_BLOB ∨
      g2MonomialBytes.size ≠ KZG_SETUP_G2_LENGTH then
    throw .invalidTrustedSetup
  let toG1 (b : ByteArray) : Except KzgError Bls.G1 :=
    (Bls.G1.uncompress b).mapError fun _ => .invalidTrustedSetup
  let toG2 (b : ByteArray) : Except KzgError Bls.G2 :=
    (Bls.G2.uncompress b).mapError fun _ => .invalidTrustedSetup
  return {
    g1Lagrange := ← g1LagrangeBytes.mapM toG1, g1LagrangeBytes,
    g1Monomial := ← g1MonomialBytes.mapM toG1, g1MonomialBytes,
    g2Monomial := ← g2MonomialBytes.mapM toG2, g2MonomialBytes,
  }

/-- Decode the embedded setup of the mainnet ceremony.

A string that is not hexadecimal is rejected. -/
def ofHex : Except KzgError TrustedSetup := do
  let decode (hex : Array String) : Except KzgError (Array ByteArray) :=
    hex.mapM fun s => match hexToBytes? s with
      | some b => .ok b
      | none   => .error .invalidTrustedSetup
  ofBytes (← decode TrustedSetupData.g1LagrangeHex) (← decode TrustedSetupData.g1MonomialHex)
    (← decode TrustedSetupData.g2MonomialHex)

end TrustedSetup

end EthLib.Cryptography.Kzg
