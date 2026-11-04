module

public import EthLib.Cryptography.Proofs.AltBn128.Twist

/-!
# Proofs: the order of `P2`

[EIP-197](https://eips.ethereum.org/EIPS/eip-197) §"Definition of the groups" gives the generator `P2`.

It lies on the twist and is not the point at infinity.

The kernel computes `q P2 = O` by double and add, so `P2` has the prime order `q`.

EIP-197 says that `G_2` is the only group of order `q` on the twist, so `P2` generates it.
-/

@[expose] public section

namespace EthLib.Cryptography.AltBn128

-- The kernel computes multiples of a point over `Fp2`, deeper than the default.
set_option maxRecDepth 8000

namespace Point2

/-- `P2` is on the twist. -/
theorem isOnCurve_generator : generator.isOnCurve = true := by decide +kernel

/-- `P2` is not the point at infinity. -/
theorem generator_ne_infinity : generator ≠ infinity := by decide

/-- `q P2 = O`, as the kernel computes it by double and add. -/
theorem mulBits_order_generator : mulBits 256 Fr.modulus generator = infinity := by
  decide +kernel

/-- `P2` has order `q`, a prime. -/
theorem addOrderOf_generator : addOrderOf (toPoint generator) = Fr.modulus := by
  refine addOrderOf_eq_prime ?_ fun h =>
    generator_ne_infinity ((toPoint_eq_zero isOnCurve_generator).mp h)
  rw [← toPoint_mulBits 256 _ isOnCurve_generator (by decide), mulBits_order_generator]
  rfl

end Point2

end EthLib.Cryptography.AltBn128
