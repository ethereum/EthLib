module

public import EthLib.Base.Bytes
public import EthLib.Base.ByteOrder

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
  -- Clear the three low bits of byte 0 and bit 7 of byte 31, and set bit 6 of byte 31.
  --
  -- Then decode the 32 bytes in little-endian order.
  ByteOrder.ofLE (Vector.ofFn fun i : Fin 32 =>
    if i.val = 0 then key[i] &&& 248
    else if i.val = 31 then (key[i] &&& 127) ||| 64
    else key[i])

/-- Mask bit 255, then reduce even a noncanonical coordinate, RFC 7748 §5. -/
def decodeUCoordinate (u : Key) : Fp :=
  -- Keep the low `bits mod 8 = 7` bits of the last byte, with `bits = 255`.
  --
  -- Then decode the 32 bytes in little-endian order.
  --
  -- §5 asks to accept a non-canonical value as if reduced modulo `p`, so it is reduced here.
  Fin.ofNat modulus (ByteOrder.ofLE (Vector.ofFn fun i : Fin 32 =>
    if i.val = 31 then u[i] &&& 127 else u[i]))

/-- Encode a reduced coordinate as 32 little-endian bytes, RFC 7748 §5. -/
def encodeUCoordinate (u : Fp) : Key :=
  -- Reduce `u` modulo `p`, then write 32 bytes in little-endian order.
  --
  -- The element is already below `p`.
  ByteOrder.toLE 32 u.val

/-- The two projective points of the ladder and its pending swap, RFC 7748 §5. -/
structure LadderState where
  x2 : Fp
  z2 : Fp
  x3 : Fp
  z3 : Fp
  swap : Bool

/-- Swap the projective points when the next scalar bit changes, RFC 7748 §5. -/
def conditionalSwap (swap : Bool) (s : LadderState) : LadderState :=
  -- `(x_2, x_3) = cswap(swap, x_2, x_3)` and `(z_2, z_3) = cswap(swap, z_2, z_3)`.
  --
  -- §5 recommends a constant-time swap; this branch makes no constant-time claim.
  if swap then ⟨s.x3, s.z3, s.x2, s.z2, s.swap⟩ else s

/-- One differential addition and doubling step, RFC 7748 §5. -/
def ladderStep (u : Fp) (bit : Bool) (state : LadderState) : LadderState :=
  -- The conditional swap on `swap XOR k_t`, then `swap = k_t`.
  let s := conditionalSwap (state.swap != bit) state
  -- `A = x_2 + z_2`, `AA = A^2`, `B = x_2 - z_2`, `BB = B^2`, `E = AA - BB`.
  let a := s.x2 + s.z2
  let aa := a * a
  let b := s.x2 - s.z2
  let bb := b * b
  let e := aa - bb
  -- `C = x_3 + z_3`, `D = x_3 - z_3`, `DA = D * A`, `CB = C * B`.
  let c := s.x3 + s.z3
  let d := s.x3 - s.z3
  let da := d * a
  let cb := c * b
  -- `x_2 = AA * BB` and `z_2 = E * (AA + a24 * E)`, with `a24 = 121665`.
  --
  -- `x_3 = (DA + CB)^2` and `z_3 = x_1 * (DA - CB)^2`; the new swap flag is the bit `k_t`.
  ⟨aa * bb, e * (aa + 121665 * e), (da + cb) * (da + cb),
    u * ((da - cb) * (da - cb)), bit⟩

/-- Read all 255 scalar bits from high to low, RFC 7748 §5. -/
def ladder (scalar : Nat) (u : Fp) : LadderState :=
  -- `x_1 = u`, `x_2 = 1`, `z_2 = 0`, `x_3 = u`, `z_3 = 1`, `swap = 0`.
  --
  -- One step for each `t` from `bits - 1` down to `0`, with `bits = 255`.
  --
  -- `k_t` is bit `t` of `k`.
  (List.range 255).foldl (fun s i =>
    ladderStep u (scalar.testBit (254 - i)) s) ⟨1, 0, u, 1, false⟩

/-- Scalar multiplication, including the zero result, RFC 7748 §5.

The inversion is the specified power `z^(p - 2)`.

The scalar is secret, and this specification makes no constant-time claim. -/
def x25519 (scalar u : Key) : Key :=
  -- §5: first decode `k` and `u`, then run the ladder.
  let state := ladder (decodeScalar scalar) (decodeUCoordinate u)
  -- The final conditional swap.
  let s := conditionalSwap state.swap state
  -- The result is `x_2 * (z_2^(p - 2))`, encoded as 32 bytes.
  encodeUCoordinate (Fin.ofNat modulus
    (s.x2.val * Nat.powMod s.z2.val (modulus - 2) modulus))

/-- The public key at Montgomery base point 9, RFC 7748 §6.1. -/
def publicKey (scalar : Key) : Key :=
  -- §6.1: `X25519(a, 9)`, the u-coordinate of the base point being 9.
  x25519 scalar (ByteOrder.toLE 32 9)

end EthLib.Cryptography.X25519
