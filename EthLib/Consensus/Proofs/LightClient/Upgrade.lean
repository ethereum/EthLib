module

public import EthLib.Consensus.LightClient.Upgrade
public import EthLib.Serialization.Proofs.Ssz.Type.ValueEquality

/-!
# Proofs: the upgrade of light client data to a later fork

An upgrade keeps the beacon header of a light client header.

So the upgrade of a store keeps its finalized and optimistic beacon headers, and their slots.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- The Gloas header of an Electra header keeps the beacon header. -/
theorem LightClientHeader.toGloas_beacon {config : Config} {post : Fork}
    {gloas : .glamsterdam ≤ post} {header : LightClientHeader preset .pectra}
    {upgraded : LightClientHeader preset post}
    (computed : header.toGloas config gloas = .ok upgraded) :
    upgraded.beacon = header.beacon := by
  unfold LightClientHeader.toGloas at computed
  split at computed
  · -- The empty header stays empty, and an Electra header equal to it has its beacon header.
    rename_i empty
    cases computed
    -- The SSZ value of a header starts with the fields of its beacon header.
    have values := beq_iff_eq.mp empty
    simp only [SszType.toValue, SszFields.toValues, Value.seq.injEq, List.cons.injEq] at values
    obtain ⟨⟨slot, proposer, parent, state, body, -⟩, -⟩ := values
    simp only [Value.uint.injEq, Value.bytes.injEq, UInt64.toNat_inj, Vector.toArray_inj]
      at slot proposer parent state body
    cases beacon : header.beacon
    simp_all [LightClientHeader.empty]
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; rfl)

/-- An upgraded header keeps the beacon header. -/
theorem LightClientHeader.upgrade_beacon {config : Config} {pre post : Fork}
    {later : pre ≤ post} {header : LightClientHeader preset pre}
    {upgraded : LightClientHeader preset post}
    (computed : header.upgrade config post later = .ok upgraded) :
    upgraded.beacon = header.beacon := by
  unfold LightClientHeader.upgrade at computed
  split at computed
  · cases computed
    rfl
  split at computed
  · exact (toGloas_beacon computed).trans rfl
  · cases computed
    rfl

/-- An upgraded store keeps its finalized and optimistic beacon headers.

So it keeps their slots, and the order between them. -/
theorem LightClientStore.upgrade_beacon {config : Config} {pre post : Fork}
    {later : pre ≤ post} {store : LightClientStore preset pre}
    {upgraded : LightClientStore preset post}
    (computed : store.upgrade config post later = .ok upgraded) :
    upgraded.finalizedHeader.beacon = store.finalizedHeader.beacon ∧
      upgraded.optimisticHeader.beacon = store.optimisticHeader.beacon := by
  unfold LightClientStore.upgrade at computed
  obtain ⟨finalized, finalizedOk, rest⟩ := Base.bind_ok_iff.mp computed
  obtain ⟨_, _, rest⟩ := Base.bind_ok_iff.mp rest
  obtain ⟨optimistic, optimisticOk, rest⟩ := Base.bind_ok_iff.mp rest
  cases rest
  exact ⟨LightClientHeader.upgrade_beacon finalizedOk,
    LightClientHeader.upgrade_beacon optimisticOk⟩

end EthLib.Consensus
