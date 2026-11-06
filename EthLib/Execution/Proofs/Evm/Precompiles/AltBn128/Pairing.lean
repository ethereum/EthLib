module

public import EthLib.Execution.Proofs.Evm.Precompiles.AltBn128.Basic
public import EthLib.Cryptography.Proofs.AltBn128.Order
public import EthLib.Cryptography.Proofs.AltBn128.Twist

/-!
# Proofs: the pairs of ECPAIRING

EIP-197 asks each pair of ECPAIRING to hold a point of `G_1` and a point of `G_2`.

For `G_1`, it says that the encoding and the curve equation are enough.

The curve over `Fp` has `q` points, so `q P = O` for each of them.

So the check `q P = O` that the code also makes on the first point never fails.

For `G_2`, EIP-197 also asks that the order of the point be `q`.

The code computes `q Q` by double and add.

The result is `O` exactly when `q` kills the group element of `Q`.

So the check accepts each point whose order divides `q`, including `O`.

EIP-197 encodes `O` as zeros.

EIP-197 says that these points form `G_2`, and no theorem here proves it.

So a pair decodes exactly when its first point decodes, its second point decodes, and `q Q = O`.

Source: [EIP-197][eip197], section Specification.

[eip197]: https://eips.ethereum.org/EIPS/eip-197#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.AltBn128

open EthLib.Cryptography.AltBn128
open EthLib.Base (bind_ok_iff)
open EthLib.Execution.Evm (bufferRead)

/-- A decoded point of the twist is on the twist. -/
theorem bytesToG2_isOnCurve {raw : List UInt8} {q : Point2} (h : bytesToG2 raw = .ok q) :
    q.isOnCurve = true := by
  simp only [bytesToG2, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  split at h
  · cases h
    rfl
  · split at h
    · cases h
      assumption
    · cases h

/-- A pair decodes exactly when both points decode and `q` kills the point of the twist.

The check `q P = O` on the point of `G_1` passes for every point that decodes. -/
theorem decodePair_eq_ok_iff (data : ByteArray) (index : Nat) (p : Point) (q : Point2) :
    decodePair data index = .ok (p, q) ↔
      bytesToG1 (bufferRead data (192 * index) 64) = .ok p ∧
        bytesToG2 (bufferRead data (192 * index + 64) 128) = .ok q ∧
        Fr.modulus • Point2.toPoint q = 0 := by
  unfold decodePair
  cases hp : bytesToG1 (bufferRead data (192 * index) 64) with
  | error e => simp [bind, Except.bind]
  | ok p' =>
    cases hq : bytesToG2 (bufferRead data (192 * index + 64) 128) with
    | error e => simp [bind, Except.bind]
    | ok q' =>
      -- Every point of the curve over `Fp` passes its check, since the curve has `q` points.
      have hp' := Point.mulBits_order (bytesToG1_isOnCurve hp)
      have hq' := Point2.mulBits_order_eq_infinity_iff (bytesToG2_isOnCurve hq)
      by_cases hsub : Point2.mulBits 256 Fr.modulus q' = .infinity
      · simp only [bind, Except.bind, pure, Except.pure, hp', hsub, ne_eq, not_true_eq_false,
          ↓reduceIte, Except.ok.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, hq'.mp hsub⟩
        · rintro ⟨rfl, rfl, -⟩
          exact ⟨rfl, rfl⟩
      · simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, hp', hsub, ne_eq,
          not_true_eq_false, not_false_eq_true, ↓reduceIte, reduceCtorEq, Except.ok.injEq,
          false_iff, not_and]
        rintro - rfl
        exact fun h => hsub (hq'.mpr h)

end EthLib.Execution.Evm.Precompiles.AltBn128
