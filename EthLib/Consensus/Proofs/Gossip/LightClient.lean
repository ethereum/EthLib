module

public import EthLib.Consensus.Gossip.LightClient

/-!
# Proofs: the outcomes of the light client topics

A node accepts an update exactly when every check of its role passes.

So an accepted update is newer than every update of its topic forwarded before.

A full node accepts only the update that the latest update it supplies gives.

A light client accepts only an update that its store accepts.

That update must also move the store forward, or repeat the latest forwarded finality update.

Once an update is forwarded, every update that is not newer is ignored.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Networking.Gossip

namespace LightClientForwarded

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {genesisTimeMs currentTimeMs : UInt64} {forwarded : LightClientForwarded preset fork}
  {store : LightClientStore preset fork} {genesisValidatorsRoot : Root}

/-! ## Finality updates -/

section Finality

variable {update : LightClientFinalityUpdate preset fork}

/-- Every node accepts a finality update exactly when both of its checks pass.

Each update forwarded before finalizes an earlier slot, or the same slot without a supermajority.

At that same slot, a supermajority signed the new update.

The sync committee messages of the signature slot are also due by the clock. -/
theorem validateFinalityUpdate_eq_accept :
    forwarded.validateFinalityUpdate config genesisTimeMs update currentTimeMs = .ok .accept ↔
      (∀ prior ∈ forwarded.finalityUpdates,
        prior.finalizedHeader.beacon.slot < update.finalizedHeader.beacon.slot ∨
          (prior.finalizedHeader.beacon.slot = update.finalizedHeader.beacon.slot ∧
            update.syncAggregate.hasSupermajority = true ∧
            prior.syncAggregate.hasSupermajority = false)) ∧
      isSyncMessageDue config preset genesisTimeMs update.signatureSlot currentTimeMs =
        .ok true := by
  have newer : forwarded.finalityUpdates.all update.isNewerThan = true ↔
      ∀ prior ∈ forwarded.finalityUpdates,
        prior.finalizedHeader.beacon.slot < update.finalizedHeader.beacon.slot ∨
          (prior.finalizedHeader.beacon.slot = update.finalizedHeader.beacon.slot ∧
            update.syncAggregate.hasSupermajority = true ∧
            prior.syncAggregate.hasSupermajority = false) := by
    simp [LightClientFinalityUpdate.isNewerThan, and_assoc]
  rw [← newer]
  unfold validateFinalityUpdate
  cases forwarded.finalityUpdates.all update.isNewerThan <;>
    cases isSyncMessageDue config preset genesisTimeMs update.signatureSlot currentTimeMs <;>
    rename_i due <;> try cases due
  all_goals simp [ignoreUnless, ValidationResult.andThenM, bind, Except.bind, pure, Except.pure]

/-- A full node accepts a finality update exactly when the common checks pass on it.

The update must also be the one that the latest update of the node gives. -/
theorem validateFinalityUpdateAtFullNode_eq_accept
    {latest : Option (LightClientUpdate preset fork)} :
    forwarded.validateFinalityUpdateAtFullNode config genesisTimeMs latest update
        currentTimeMs = .ok .accept ↔
      forwarded.validateFinalityUpdate config genesisTimeMs update currentTimeMs = .ok .accept ∧
        latest.map createLightClientFinalityUpdate = some update := by
  unfold validateFinalityUpdateAtFullNode
  cases forwarded.validateFinalityUpdate config genesisTimeMs update currentTimeMs with
  | error => simp [bind, Except.bind]
  | ok first =>
    cases first <;> by_cases same : latest.map createLightClientFinalityUpdate = some update <;>
      simp [same, ignoreUnless, ValidationResult.andThen, bind, Except.bind, pure, Except.pure]

/-- A light client accepts a finality update exactly when the common checks pass on it.

Its store must also process the update at the slot of the clock.

The store after it must have a newer finalized header. -/
theorem validateFinalityUpdateAtLightClient_eq_accept :
    forwarded.validateFinalityUpdateAtLightClient config genesisTimeMs checks store
        genesisValidatorsRoot update currentTimeMs = .ok .accept ↔
      forwarded.validateFinalityUpdate config genesisTimeMs update currentTimeMs = .ok .accept ∧
        ∃ currentSlot next,
          computeSlotAtTimeMs config genesisTimeMs currentTimeMs = .ok currentSlot ∧
          processLightClientFinalityUpdate config checks store update currentSlot
            genesisValidatorsRoot = .ok next ∧
          store.finalizedHeader.beacon.slot < next.finalizedHeader.beacon.slot := by
  unfold validateFinalityUpdateAtLightClient
  cases forwarded.validateFinalityUpdate config genesisTimeMs update currentTimeMs with
  | error => simp [bind, Except.bind]
  | ok first =>
    cases first with
    | ignore => simp [bind, Except.bind, ValidationResult.andThenM, pure, Except.pure]
    | reject => simp [bind, Except.bind, ValidationResult.andThenM, pure, Except.pure]
    | accept =>
      cases clock : computeSlotAtTimeMs config genesisTimeMs currentTimeMs with
      | error => simp [bind, Except.bind, ValidationResult.andThenM]
      | ok currentSlot =>
        cases processed : processLightClientFinalityUpdate config checks store update currentSlot
            genesisValidatorsRoot with
        | error =>
          simp [processed, bind, Except.bind, ValidationResult.andThenM, pure, Except.pure]
        | ok next =>
          simp [processed, ignoreUnless, bind, Except.bind, ValidationResult.andThenM, pure,
            Except.pure]

/-- A light client rejects a finality update that its store refuses.

That check comes after the common checks and the slot of the clock. -/
theorem validateFinalityUpdateAtLightClient_of_error {currentSlot : Slot}
    {error : LightClientError}
    (common : forwarded.validateFinalityUpdate config genesisTimeMs update currentTimeMs =
      .ok .accept)
    (clock : computeSlotAtTimeMs config genesisTimeMs currentTimeMs = .ok currentSlot)
    (refused : processLightClientFinalityUpdate config checks store update currentSlot
      genesisValidatorsRoot = .error error) :
    forwarded.validateFinalityUpdateAtLightClient config genesisTimeMs checks store
        genesisValidatorsRoot update currentTimeMs =
      .ok (.reject "finality update is invalid") := by
  simp [validateFinalityUpdateAtLightClient, common, clock, refused, bind, Except.bind,
    ValidationResult.andThenM, pure, Except.pure]

/-- Once a finality update is forwarded, every node ignores an update that is not newer. -/
theorem validateFinalityUpdate_recordFinalityUpdate {prior : LightClientFinalityUpdate preset fork}
    (stale : update.isNewerThan prior = false) :
    (forwarded.recordFinalityUpdate prior).validateFinalityUpdate config genesisTimeMs update
        currentTimeMs = .ok (.ignore "finality update is not newer than a forwarded one") := by
  simp [validateFinalityUpdate, recordFinalityUpdate, stale, ignoreUnless,
    ValidationResult.andThenM, pure, Except.pure]

/-- No finality update is newer than itself. -/
theorem _root_.EthLib.Consensus.LightClientFinalityUpdate.isNewerThan_self :
    update.isNewerThan update = false := by
  simp [LightClientFinalityUpdate.isNewerThan]

end Finality

/-! ## Optimistic updates -/

section Optimistic

variable {update : LightClientOptimisticUpdate preset fork}

/-- Every node accepts an optimistic update exactly when both of its checks pass.

Each update forwarded before attests an earlier slot.

The sync committee messages of the signature slot are also due by the clock. -/
theorem validateOptimisticUpdate_eq_accept :
    forwarded.validateOptimisticUpdate config genesisTimeMs update currentTimeMs = .ok .accept ↔
      (∀ prior ∈ forwarded.optimisticUpdates,
        prior.attestedHeader.beacon.slot < update.attestedHeader.beacon.slot) ∧
      isSyncMessageDue config preset genesisTimeMs update.signatureSlot currentTimeMs =
        .ok true := by
  have newer : (forwarded.optimisticUpdates.all fun prior =>
        prior.attestedHeader.beacon.slot < update.attestedHeader.beacon.slot) = true ↔
      ∀ prior ∈ forwarded.optimisticUpdates,
        prior.attestedHeader.beacon.slot < update.attestedHeader.beacon.slot := by
    simp
  rw [← newer]
  unfold validateOptimisticUpdate
  cases forwarded.optimisticUpdates.all _ <;>
    cases isSyncMessageDue config preset genesisTimeMs update.signatureSlot currentTimeMs <;>
    rename_i due <;> try cases due
  all_goals simp [ignoreUnless, ValidationResult.andThenM, bind, Except.bind, pure, Except.pure]

/-- A full node accepts an optimistic update exactly when the common checks pass on it.

The update must also be the one that the latest update of the node gives. -/
theorem validateOptimisticUpdateAtFullNode_eq_accept
    {latest : Option (LightClientUpdate preset fork)} :
    forwarded.validateOptimisticUpdateAtFullNode config genesisTimeMs latest update
        currentTimeMs = .ok .accept ↔
      forwarded.validateOptimisticUpdate config genesisTimeMs update currentTimeMs = .ok .accept ∧
        latest.map createLightClientOptimisticUpdate = some update := by
  unfold validateOptimisticUpdateAtFullNode
  cases forwarded.validateOptimisticUpdate config genesisTimeMs update currentTimeMs with
  | error => simp [bind, Except.bind]
  | ok first =>
    cases first <;> by_cases same : latest.map createLightClientOptimisticUpdate = some update <;>
      simp [same, ignoreUnless, ValidationResult.andThen, bind, Except.bind, pure, Except.pure]

/-- A light client accepts an optimistic update exactly when the common checks pass on it.

Its store must also process the update at the slot of the clock.

The update must repeat the latest forwarded finality update, or advance the optimistic header. -/
theorem validateOptimisticUpdateAtLightClient_eq_accept :
    forwarded.validateOptimisticUpdateAtLightClient config genesisTimeMs checks store
        genesisValidatorsRoot update currentTimeMs = .ok .accept ↔
      forwarded.validateOptimisticUpdate config genesisTimeMs update currentTimeMs =
          .ok .accept ∧
        ∃ currentSlot next,
          computeSlotAtTimeMs config genesisTimeMs currentTimeMs = .ok currentSlot ∧
          processLightClientOptimisticUpdate config checks store update currentSlot
            genesisValidatorsRoot = .ok next ∧
          (forwarded.finalityUpdates.head?.map (·.toOptimisticUpdate) = some update ∨
            store.optimisticHeader.beacon.slot < next.optimisticHeader.beacon.slot) := by
  unfold validateOptimisticUpdateAtLightClient
  cases forwarded.validateOptimisticUpdate config genesisTimeMs update currentTimeMs with
  | error => simp [bind, Except.bind]
  | ok first =>
    cases first with
    | ignore => simp [bind, Except.bind, ValidationResult.andThenM, pure, Except.pure]
    | reject => simp [bind, Except.bind, ValidationResult.andThenM, pure, Except.pure]
    | accept =>
      cases clock : computeSlotAtTimeMs config genesisTimeMs currentTimeMs with
      | error => simp [bind, Except.bind, ValidationResult.andThenM]
      | ok currentSlot =>
        cases processed : processLightClientOptimisticUpdate config checks store update currentSlot
            genesisValidatorsRoot with
        | error =>
          simp [processed, bind, Except.bind, ValidationResult.andThenM, pure, Except.pure]
        | ok next =>
          simp [processed, ignoreUnless, bind, Except.bind, ValidationResult.andThenM, pure,
            Except.pure, Classical.or_iff_not_imp_left]

/-- A light client rejects an optimistic update that its store refuses.

That check comes after the common checks and the slot of the clock. -/
theorem validateOptimisticUpdateAtLightClient_of_error {currentSlot : Slot}
    {error : LightClientError}
    (common : forwarded.validateOptimisticUpdate config genesisTimeMs update currentTimeMs =
      .ok .accept)
    (clock : computeSlotAtTimeMs config genesisTimeMs currentTimeMs = .ok currentSlot)
    (refused : processLightClientOptimisticUpdate config checks store update currentSlot
      genesisValidatorsRoot = .error error) :
    forwarded.validateOptimisticUpdateAtLightClient config genesisTimeMs checks store
        genesisValidatorsRoot update currentTimeMs =
      .ok (.reject "optimistic update is invalid") := by
  simp [validateOptimisticUpdateAtLightClient, common, clock, refused, bind, Except.bind,
    ValidationResult.andThenM, pure, Except.pure]

/-- Once an optimistic update is forwarded, every node ignores an update of no later slot. -/
theorem validateOptimisticUpdate_recordOptimisticUpdate
    {prior : LightClientOptimisticUpdate preset fork}
    (stale : update.attestedHeader.beacon.slot ≤ prior.attestedHeader.beacon.slot) :
    (forwarded.recordOptimisticUpdate prior).validateOptimisticUpdate config genesisTimeMs
        update currentTimeMs =
      .ok (.ignore "optimistic update is not newer than a forwarded one") := by
  simp [validateOptimisticUpdate, recordOptimisticUpdate, UInt64.not_lt.mpr stale, ignoreUnless,
    ValidationResult.andThenM, pure, Except.pure]

end Optimistic

end LightClientForwarded

end EthLib.Consensus
