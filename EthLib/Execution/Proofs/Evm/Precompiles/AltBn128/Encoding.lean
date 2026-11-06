module

public import EthLib.Execution.Proofs.Evm.Precompiles.AltBn128.Basic

/-!
# Proofs: the encoding of a point of `G_1`

EIP-196 encodes a point as its two coordinates, each a 32-byte big-endian number below `p`.

The point at infinity is `(0, 0)`.

The decoder reads back every point on the curve from its 64 bytes.

Each 64 bytes that it accepts are the encoding of the point that it returns.

So the decoder accepts 64 bytes exactly when they encode a point on the curve.

The point `(0, 0)` is not on the curve, so it cannot be confused with the point at infinity.

Source: [EIP-196][eip196], section Encoding.

[eip196]: https://eips.ethereum.org/EIPS/eip-196#encoding
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.AltBn128

open EthLib.Cryptography.AltBn128
open EthLib.Base (bytesToNat natToBytes natToBytes_length bytesToNat_natToBytes
  bytesToNat_natToBytes_of_lt natToBytes_bytesToNat)

/-- Zero on `len` bytes is `len` zero bytes. -/
theorem natToBytes_zero (len : Nat) : natToBytes len 0 = List.replicate len 0 := by
  induction len with
  | zero => rfl
  | succ len ih => rw [natToBytes, Nat.zero_div, ih, List.replicate_succ']; rfl

/-- The point `(0, 0)` is not on the curve, since `0 ≠ 3` in `Fp`. -/
theorem isOnCurve_affine_zero : (Point.affine 0 0).isOnCurve = false := by decide

/-- A coordinate fits in 32 bytes, since `p < 2^256`. -/
theorem val_lt_two_pow (x : Fp) : x.val < 256 ^ 32 :=
  Nat.lt_trans x.isLt (by decide)

/-- The decoder reads back each point on the curve from its 64 bytes. -/
theorem bytesToG1_g1ToBytes {p : Point} (hp : p.isOnCurve = true) :
    bytesToG1 (g1ToBytes p) = .ok p := by
  cases p with
  | infinity =>
    -- Both halves are 32 zero bytes, which read as `(0, 0)`.
    have hhalf : bytesToNat (natToBytes 32 0) = 0 := bytesToNat_natToBytes_of_lt (by decide)
    have hbytes : g1ToBytes .infinity = natToBytes 32 0 ++ natToBytes 32 0 := by
      rw [natToBytes_zero, List.replicate_append_replicate]
      rfl
    have hpos : 0 < Fp.modulus := by decide
    simp only [bytesToG1, hbytes, List.take_left' (natToBytes_length 32 0),
      List.drop_left' (natToBytes_length 32 0), hhalf, hpos, and_self, dite_true, ite_true,
      pure, Except.pure]
  | affine x y =>
    have hx : (g1ToBytes (.affine x y)).take 32 = natToBytes 32 x.val := by
      simp [g1ToBytes, natToBytes_length]
    have hy : (g1ToBytes (.affine x y)).drop 32 = natToBytes 32 y.val := by
      simp [g1ToBytes, natToBytes_length]
    -- The point is on the curve, so it is not `(0, 0)`.
    have hzero : ¬(x.val = 0 ∧ y.val = 0) := by
      rintro ⟨h0, h1⟩
      have : x = 0 ∧ y = 0 := ⟨Fin.ext h0, Fin.ext h1⟩
      rw [this.1, this.2, isOnCurve_affine_zero] at hp
      cases hp
    simp only [bytesToG1, hx, hy, bytesToNat_natToBytes_of_lt (val_lt_two_pow x),
      bytesToNat_natToBytes_of_lt (val_lt_two_pow y), x.isLt, y.isLt, hzero, hp, dite_true,
      ite_false, ite_true, pure, Except.pure]

/-- Each 64 bytes that the decoder accepts are the encoding of the point that it returns. -/
theorem g1ToBytes_of_bytesToG1 {raw : List UInt8} {p : Point} (hlen : raw.length = 64)
    (h : bytesToG1 raw = .ok p) : g1ToBytes p = raw := by
  -- Each half has 32 bytes, so it is its value written on 32 bytes.
  have htake : natToBytes 32 (bytesToNat (raw.take 32)) = raw.take 32 := by
    have := natToBytes_bytesToNat (raw.take 32)
    rwa [List.length_take, hlen] at this
  have hdrop : natToBytes 32 (bytesToNat (raw.drop 32)) = raw.drop 32 := by
    have := natToBytes_bytesToNat (raw.drop 32)
    rwa [List.length_drop, hlen] at this
  have hsplit := List.take_append_drop 32 raw
  simp only [bytesToG1, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · split at h
    · split at h
      · rename_i hzero
        cases h
        rw [hzero.1] at htake
        rw [hzero.2] at hdrop
        rw [← hsplit, ← htake, ← hdrop, natToBytes_zero, List.replicate_append_replicate]
        rfl
      · split at h
        · cases h
          show natToBytes 32 _ ++ natToBytes 32 _ = raw
          rw [htake, hdrop, hsplit]
        · cases h
    · cases h
  · cases h

/-- 64 bytes decode to a point exactly when the point is on the curve and the bytes encode it. -/
theorem bytesToG1_eq_ok_iff {raw : List UInt8} (hlen : raw.length = 64) (p : Point) :
    bytesToG1 raw = .ok p ↔ p.isOnCurve = true ∧ g1ToBytes p = raw :=
  ⟨fun h => ⟨bytesToG1_isOnCurve h, g1ToBytes_of_bytesToG1 hlen h⟩,
    fun ⟨hp, hraw⟩ => hraw ▸ bytesToG1_g1ToBytes hp⟩

end EthLib.Execution.Evm.Precompiles.AltBn128
