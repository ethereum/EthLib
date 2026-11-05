module

public import EthLib.Consensus.LightClient.Sync

/-!
# Proofs: the light client sync protocol

Each error of the light client has its own code.

No update ranks above itself, so the best update changes only for a strictly better one.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

/-- Two errors with one code come from one constructor. -/
theorem LightClientError.code_injective (e₁ e₂ : LightClientError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [LightClientError.code] at h; exact absurd h (by decide))

/-- No update ranks above itself. -/
theorem isBetterUpdate_self {preset : Preset} {fork : Fork}
    (update : LightClientUpdate preset fork) : isBetterUpdate update update = false := by
  simp [isBetterUpdate]

end EthLib.Consensus
