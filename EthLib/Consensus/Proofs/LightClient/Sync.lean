module

public import EthLib.Consensus.LightClient.Sync

/-!
# Proofs: the light client sync protocol

Each error of the light client has its own code.

No update ranks above itself, so the best update changes only for a strictly better one.

The finalized and optimistic slots of a store never move back.

A new store starts with one header for both.

The finalized header then stays at or below the optimistic header.
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

section Slots

variable {preset : Preset} {fork : Fork}

/-- A new store starts with one header as both its finalized and its optimistic header.

That header is the header of the bootstrap. -/
theorem initializeLightClientStore_headers {config : Config} {trustedBlockRoot : Root}
    {bootstrap : LightClientBootstrap preset fork} {store : LightClientStore preset fork}
    (computed : initializeLightClientStore config trustedBlockRoot bootstrap = .ok store) :
    store.finalizedHeader = bootstrap.header ∧ store.optimisticHeader = bootstrap.header := by
  unfold initializeLightClientStore at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact ⟨rfl, rfl⟩)

/-- Applying an update moves the finalized and optimistic slots forward, never back.

A finalized slot at or below the optimistic slot stays at or below it. -/
theorem applyLightClientUpdate_slots {store after : LightClientStore preset fork}
    {update : LightClientUpdate preset fork}
    (computed : applyLightClientUpdate store update = .ok after) :
    store.finalizedHeader.beacon.slot ≤ after.finalizedHeader.beacon.slot ∧
      store.optimisticHeader.beacon.slot ≤ after.optimisticHeader.beacon.slot ∧
      (store.finalizedHeader.beacon.slot ≤ store.optimisticHeader.beacon.slot →
        after.finalizedHeader.beacon.slot ≤ after.optimisticHeader.beacon.slot) := by
  unfold applyLightClientUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure, LightClientError.require,
    LightClientError.requireFork] at computed
  -- Each branch either fails or rebuilds the store from known headers.
  repeat' split at computed
  all_goals
    cases computed
    try dsimp only
    try refine ⟨?_, ?_, fun _ => ?_⟩
    all_goals
      simp only [gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at *
      omega

/-- Processing an update moves the finalized and optimistic slots forward, never back.

A finalized slot at or below the optimistic slot stays at or below it. -/
theorem processLightClientUpdate_slots {config : Config} {checks : SignatureChecks}
    {store after : LightClientStore preset fork} {update : LightClientUpdate preset fork}
    {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (computed : processLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok after) :
    store.finalizedHeader.beacon.slot ≤ after.finalizedHeader.beacon.slot ∧
      store.optimisticHeader.beacon.slot ≤ after.optimisticHeader.beacon.slot ∧
      (store.finalizedHeader.beacon.slot ≤ store.optimisticHeader.beacon.slot →
        after.finalizedHeader.beacon.slot ≤ after.optimisticHeader.beacon.slot) := by
  unfold processLightClientUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  -- The optimistic header only moves to a later attested header before the update applies.
  repeat' split at computed
  all_goals
    try have applied := applyLightClientUpdate_slots ‹applyLightClientUpdate _ _ = .ok _›
    cases computed
    try dsimp only at *
    try refine ⟨?_, ?_, fun _ => ?_⟩
    all_goals
      simp only [gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at *
      omega

/-- A forced update moves the finalized and optimistic slots forward, never back.

A finalized slot at or below the optimistic slot stays at or below it. -/
theorem processLightClientStoreForceUpdate_slots {store after : LightClientStore preset fork}
    {currentSlot : Slot}
    (computed : processLightClientStoreForceUpdate store currentSlot = .ok after) :
    store.finalizedHeader.beacon.slot ≤ after.finalizedHeader.beacon.slot ∧
      store.optimisticHeader.beacon.slot ≤ after.optimisticHeader.beacon.slot ∧
      (store.finalizedHeader.beacon.slot ≤ store.optimisticHeader.beacon.slot →
        after.finalizedHeader.beacon.slot ≤ after.optimisticHeader.beacon.slot) := by
  unfold processLightClientStoreForceUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure, LightClientError.require,
    LightClientError.requireFork] at computed
  repeat' split at computed
  all_goals
    try have applied := applyLightClientUpdate_slots ‹applyLightClientUpdate _ _ = .ok _›
    cases computed
    try dsimp only at *
    try refine ⟨?_, ?_, fun _ => ?_⟩
    all_goals
      simp only [gt_iff_lt, UInt64.le_iff_toNat_le] at *
      omega

end Slots

end EthLib.Consensus
