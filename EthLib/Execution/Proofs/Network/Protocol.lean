module

public import EthLib.Execution.Network.Protocol

/-!
# Proofs: the versions of the eth capability

A version and its number determine each other.

So the number that a node announces in Hello or in Status names at most one version.

The order of the versions is the order of their numbers.

The eth count of message IDs is nonzero exactly on the capabilities of the eth versions.
-/

@[expose] public section

namespace EthLib.Execution.Network

namespace EthVersion

/-- The number of a version reads back to that version. -/
theorem ofNumber?_number (v : EthVersion) : ofNumber? v.number = some v := by
  cases v <;> rfl

/-- A number reads to a version exactly when it is the number of that version. -/
theorem ofNumber?_eq_some_iff {n : Nat} {v : EthVersion} : ofNumber? n = some v ↔ v.number = n := by
  constructor
  · intro h
    unfold ofNumber? at h
    split at h <;> cases h <;> rfl
  · rintro rfl
    exact ofNumber?_number v

/-- Two versions with one number are one version. -/
theorem number_injective : Function.Injective number := fun a b h => by
  have := ofNumber?_number a
  rwa [h, ofNumber?_number, Option.some.injEq, eq_comm] at this

/-- A version is at or before another exactly when its number is at most the other's. -/
theorem le_iff_number_le {a b : EthVersion} : a ≤ b ↔ a.number ≤ b.number := by
  cases a <;> cases b <;> decide

/-- A version is before another exactly when its number is below the other's. -/
theorem lt_iff_number_lt {a b : EthVersion} : a < b ↔ a.number < b.number := by
  cases a <;> cases b <;> decide

/-- Every version has at least one message ID. -/
theorem messageCount_pos (v : EthVersion) : 0 < v.messageCount := by
  cases v <;> decide

end EthVersion

/-- The multiplexing of RLPx gives an eth capability the message count of its version. -/
theorem ethLength_capability (v : EthVersion) : ethLength v.capability = v.messageCount := by
  cases v <;> rfl

/-- The eth count of message IDs is nonzero exactly on the capability of an eth version. -/
theorem ethLength_ne_zero_iff {c : Networking.Devp2p.Capability} :
    ethLength c ≠ 0 ↔ ∃ v : EthVersion, v.capability = c := by
  constructor
  · intro h
    unfold ethLength at h
    split at h
    next hname =>
      cases hv : EthVersion.ofNumber? c.version with
      | none => simp [hv] at h
      | some v =>
        refine ⟨v, ?_⟩
        cases c
        simp only [EthVersion.capability, Networking.Devp2p.Capability.mk.injEq]
        exact ⟨hname.symm, EthVersion.ofNumber?_eq_some_iff.mp hv⟩
    · exact absurd rfl h
  · rintro ⟨v, rfl⟩
    rw [ethLength_capability]
    exact Nat.pos_iff_ne_zero.mp (EthVersion.messageCount_pos v)

end EthLib.Execution.Network
