module

/-!
# `Base.BlobSchedule`

The blob parameters of a block: the target, the maximum and the update fraction.

[EIP-7892][eip-7892] makes them chain configuration.

So a chain can change them at an activation of its own.

[EIP-7840][eip-7840] names them in the configuration file of a client.

[eip-7840]: https://eips.ethereum.org/EIPS/eip-7840#specification
[eip-7892]: https://eips.ethereum.org/EIPS/eip-7892#blob-schedule-configuration
-/

@[expose] public section

namespace EthLib.Base

/-- The blob parameters of one fork, or of one change that a chain configures.

Source: [EIP-7892](https://eips.ethereum.org/EIPS/eip-7892#blob-base-fee-computations).

The bounds exclude the schedules that would divide by 0 or subtract below 0.

For a schedule written in numbers, `decide` proves them. -/
structure BlobSchedule where
  /-- The blobs per block that the fee aims for. -/
  target : Nat
  /-- The most blobs a block may carry. -/
  max : Nat
  /-- The excess that multiplies the fee by about e. -/
  baseFeeUpdateFraction : Nat
  /-- The target is at most the maximum, so the subtraction `max - target` never truncates. -/
  target_le_max : target ≤ max := by decide
  /-- The maximum is positive, so the reserve price rule never divides by 0. -/
  max_pos : 0 < max := by decide
  /-- The update fraction is positive, so the exponential never divides by 0. -/
  baseFeeUpdateFraction_pos : 0 < baseFeeUpdateFraction := by decide
  deriving Repr, DecidableEq

end EthLib.Base
