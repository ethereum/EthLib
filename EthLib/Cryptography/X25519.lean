module

public import EthLib.Base.Bytes
public import EthLib.Base.LittleEndian

/-!
# X25519

The Montgomery ladder and byte encodings of [RFC 7748 §5][rfc].

This specification makes no constant-time claim.

Protocols that require rejection of an all-zero shared secret check that result themselves.

[rfc]: https://www.rfc-editor.org/rfc/rfc7748#section-5
-/

@[expose] public section

namespace EthLib.Cryptography.X25519

open EthLib.Base

/-- The field modulus of Curve25519, RFC 7748 §4.1. -/
def modulus : Nat := 2 ^ 255 - 19

instance : NeZero modulus := ⟨by decide⟩

/-- A field element, reduced modulo `2^255 - 19`. -/
abbrev Fp := Fin modulus

/-- A scalar or encoded Montgomery coordinate of RFC 7748 §5. -/
abbrev Key := Vector UInt8 32

/-- Clear the three low bits and high bit, and set bit 254, RFC 7748 §5. -/
def decodeScalar (key : Key) : Nat :=
  bytesToUint (Vector.ofFn fun i : Fin 32 =>
    if i.val = 0 then key[i] &&& 248
    else if i.val = 31 then (key[i] &&& 127) ||| 64
    else key[i])

/-- Mask bit 255, then reduce even a noncanonical coordinate, RFC 7748 §5. -/
def decodeUCoordinate (u : Key) : Fp :=
  Fin.ofNat modulus (bytesToUint (Vector.ofFn fun i : Fin 32 =>
    if i.val = 31 then u[i] &&& 127 else u[i]))

/-- Encode a reduced coordinate as 32 little-endian bytes, RFC 7748 §5. -/
def encodeUCoordinate (u : Fp) : Key := uintToBytes 32 u.val

/-- The two projective points of the ladder and its pending swap, RFC 7748 §5. -/
structure LadderState where
  x2 : Fp
  z2 : Fp
  x3 : Fp
  z3 : Fp
  swap : Bool

/-- Swap the projective points when the next scalar bit changes, RFC 7748 §5. -/
def conditionalSwap (swap : Bool) (s : LadderState) : LadderState :=
  if swap then ⟨s.x3, s.z3, s.x2, s.z2, s.swap⟩ else s

/-- One differential addition and doubling step, RFC 7748 §5. -/
def ladderStep (u : Fp) (bit : Bool) (state : LadderState) : LadderState :=
  let s := conditionalSwap (state.swap != bit) state
  let a := s.x2 + s.z2
  let aa := a * a
  let b := s.x2 - s.z2
  let bb := b * b
  let e := aa - bb
  let c := s.x3 + s.z3
  let d := s.x3 - s.z3
  let da := d * a
  let cb := c * b
  ⟨aa * bb, e * (aa + 121665 * e), (da + cb) * (da + cb),
    u * ((da - cb) * (da - cb)), bit⟩

/-- Read all 255 scalar bits from high to low, RFC 7748 §5. -/
def ladder (scalar : Nat) (u : Fp) : LadderState :=
  (List.range 255).foldl (fun s i =>
    ladderStep u (scalar.testBit (254 - i)) s) ⟨1, 0, u, 1, false⟩

/-- Scalar multiplication, including the zero result, RFC 7748 §5.

The inversion is the specified power `z^(p - 2)`.

The scalar is secret, and this specification makes no constant-time claim. -/
def x25519 (scalar u : Key) : Key :=
  let state := ladder (decodeScalar scalar) (decodeUCoordinate u)
  let s := conditionalSwap state.swap state
  encodeUCoordinate (Fin.ofNat modulus
    (s.x2.val * Nat.powMod s.z2.val (modulus - 2) modulus))

/-- The public key at Montgomery base point 9, RFC 7748 §6.1. -/
def publicKey (scalar : Key) : Key := x25519 scalar (uintToBytes 32 9)

end EthLib.Cryptography.X25519
