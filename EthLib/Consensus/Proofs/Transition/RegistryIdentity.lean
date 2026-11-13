module

public import EthLib.Consensus.Proofs.Transition.Invariants

/-!
# Registry identity through transitions

Existing public keys remain at their positions, and new keys do not duplicate earlier ones.

The relation may cross a fork boundary, so the two states can have different forks.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Fork} {state after : BeaconState preset fork}

/-- Keys form an unchanged prefix, and new keys do not duplicate earlier ones. -/
structure RegistryIdentity {fork fork' : Fork} (s : BeaconState preset fork)
    (t : BeaconState preset fork') : Prop where
  kept : validatorKeys s <+: validatorKeys t
  unique : (validatorKeys s).Nodup → (validatorKeys t).Nodup

theorem Frame.registryIdentity (frame : Frame state after) : RegistryIdentity state after :=
  ⟨frame.pubkeysPrefix, frame.pubkeysDistinct⟩

namespace RegistryIdentity

theorem refl (s : BeaconState preset fork) : RegistryIdentity s s :=
  ⟨List.prefix_refl _, id⟩

theorem trans {f₁ f₂ f₃ : Fork} {s : BeaconState preset f₁}
    {t : BeaconState preset f₂} {u : BeaconState preset f₃}
    (one : RegistryIdentity s t) (two : RegistryIdentity t u) : RegistryIdentity s u :=
  ⟨one.kept.trans two.kept, two.unique ∘ one.unique⟩

/-- A state of any fork with the same validators. -/
theorem of_validators {fork' : Fork} {s : BeaconState preset fork}
    {t : BeaconState preset fork'} (same : t.validators.data = s.validators.data := by rfl) :
    RegistryIdentity s t := by
  have keys : validatorKeys t = validatorKeys s := by simp only [validatorKeys, same]
  exact ⟨keys ▸ List.prefix_refl _, keys ▸ id⟩

end RegistryIdentity

end EthLib.Consensus
