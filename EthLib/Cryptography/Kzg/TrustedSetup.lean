module

public import EthLib.Cryptography.Bls
public import EthLib.Cryptography.Kzg.BitReversal
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
open EthLib.Base (exactBytes?)

/-- The KZG trusted setup, as decoded points. -/
structure TrustedSetup where
  /-- The Lagrange-basis G1 points, in bit-reversed order. -/
  g1LagrangeBrp : Vector Bls.G1 FIELD_ELEMENTS_PER_BLOB
  /-- The monomial-basis G1 points. -/
  g1Monomial : Vector Bls.G1 FIELD_ELEMENTS_PER_BLOB
  /-- The monomial-basis G2 points. -/
  g2Monomial : Vector Bls.G2 KZG_SETUP_G2_LENGTH

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

/-- Decode one compressed point of `G1` of the setup.

A string of another length than 48 bytes, or one that does not decompress, is rejected. -/
def decodeG1 (b : ByteArray) : Except KzgError Bls.G1 :=
  match exactBytes? 48 b with
  | some b => (Bls.G1.uncompress b).mapError fun _ => .invalidTrustedSetup
  | none => .error .invalidTrustedSetup

/-- Decode one compressed point of `G2` of the setup.

A string of another length than 96 bytes, or one that does not decompress, is rejected. -/
def decodeG2 (b : ByteArray) : Except KzgError Bls.G2 :=
  match exactBytes? 96 b with
  | some b => (Bls.G2.uncompress b).mapError fun _ => .invalidTrustedSetup
  | none => .error .invalidTrustedSetup

/-- Decode a trusted setup from compressed points.

The three lists have the lengths 4096, 4096 and 65.

A list of another length, or a point that does not decompress, is rejected.

Decompression checks that a point is on its curve, not that it is in the subgroup. -/
def ofBytes (g1LagrangeBytes g1MonomialBytes g2MonomialBytes : Array ByteArray) :
    Except KzgError TrustedSetup := do
  let g1Lagrange ← g1LagrangeBytes.mapM decodeG1
  let g1Monomial ← g1MonomialBytes.mapM decodeG1
  let g2Monomial ← g2MonomialBytes.mapM decodeG2
  if h₁ : g1Lagrange.size = FIELD_ELEMENTS_PER_BLOB then
    if h₂ : g1Monomial.size = FIELD_ELEMENTS_PER_BLOB then
      if h₃ : g2Monomial.size = KZG_SETUP_G2_LENGTH then
        -- The operations read the Lagrange points in bit-reversed order, so they are permuted here.
        return {
          g1LagrangeBrp := ⟨BitReversal.bitReversalPermutation g1Lagrange,
            (Array.size_ofFn ..).trans h₁⟩
          g1Monomial := ⟨g1Monomial, h₂⟩
          g2Monomial := ⟨g2Monomial, h₃⟩ }
  throw .invalidTrustedSetup

/-- Decode a list of hexadecimal strings, or reject the list if one string is malformed. -/
def hexListToBytes (hex : Array String) : Except KzgError (Array ByteArray) :=
  hex.mapM fun s => match hexToBytes? s with
    | some b => .ok b
    | none   => .error .invalidTrustedSetup

/-- Decode the `G2` point at position `i` of the embedded setup, and no other point.

A caller that needs one point reads it without decoding the 8192 points of `G1`.

A position past the 65 points gives the same error as a string that does not decode. -/
def g2MonomialOfHex (i : Nat) : Except KzgError Bls.G2 :=
  match TrustedSetupData.g2MonomialHex[i]? with
  | some hex =>
    match hexToBytes? hex with
    | some b => decodeG2 b
    | none => .error .invalidTrustedSetup
  | none => .error .invalidTrustedSetup

/-- Decode the embedded setup of the mainnet ceremony.

Compiled Lean evaluates each constant when its module is initialized.

The attribute below inlines this slow decode at each compiled use, so no module initializer runs it.

Every export reads the setup through one cached copy, so it decodes the setup once per process. -/
@[macro_inline]
def ofHex : Except KzgError TrustedSetup := do
  ofBytes (← hexListToBytes TrustedSetupData.g1LagrangeHex)
    (← hexListToBytes TrustedSetupData.g1MonomialHex)
    (← hexListToBytes TrustedSetupData.g2MonomialHex)

end TrustedSetup

end EthLib.Cryptography.Kzg
