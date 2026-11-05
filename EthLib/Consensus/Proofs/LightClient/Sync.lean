module

public import EthLib.Consensus.LightClient.Sync

/-!
# Proofs: the light client sync protocol

Each error of the light client has its own code.

No update ranks above itself, so the best update changes only for a strictly better one.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

/-- Two errors with one code come from one constructor. -/
theorem LightClientError.code_injective (e₁ e₂ : LightClientError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [LightClientError.code] at h; exact absurd h (by decide))

/-- A check passes exactly when its condition holds. -/
theorem LightClientError.require_ok {condition : Prop} [Decidable condition]
    {error : LightClientError} {done : Unit} : require condition error = .ok done ↔ condition := by
  unfold require
  split <;> simp_all

/-- A root lifted into the errors of the light client is the root it was. -/
theorem LightClientError.liftRoot_ok {α : Type} {result : Except Err α} {value : α} :
    liftRoot result = .ok value ↔ result = .ok value := by
  cases result <;> simp [liftRoot, Except.mapError]

/-- No update ranks above itself. -/
theorem isBetterUpdate_self {preset : Preset} {fork : Fork}
    (update : LightClientUpdate preset fork) : isBetterUpdate update update = false := by
  simp [isBetterUpdate]

end EthLib.Consensus
