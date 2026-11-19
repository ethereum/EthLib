module

public import EthLib.Consensus.Proofs.ForkChoice.Reachable
import EthLib.Consensus.Proofs.Time

/-!
# Proofs: stores whose clock never goes back

A tick of the fork choice sets the time of the store, even to an earlier time.

The clock of an honest node only moves forward, so its ticks never go back.

A store is reachable with a forward clock when the handlers build it and no tick sets it back.

Such a store is reachable, so every result on reachable stores applies to it.

A tick to a time no earlier than that of the store does not lower its current slot.

An honest node also runs every handler with one setting of the signature checks.

A store built that way is also reachable with a forward clock.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Fork}

namespace Store

/-- A store that the handlers build from an anchor, where no tick sets the time back.

It has one case for each case of a reachable store, and only its tick asks more. -/
inductive ForwardReachable (config : Config) (anchorState : BeaconState preset fork)
    (anchorBlock : BeaconBlock preset fork) : Store preset fork → Prop where
  /-- The store built from the anchor. -/
  | anchor {store : Store preset fork} :
    getForkchoiceStore config anchorState anchorBlock = .ok store →
      ForwardReachable config anchorState anchorBlock store
  /-- The store after a tick to a time no earlier than its own. -/
  | tick {store after : Store preset fork} {timeMs : UInt64} :
    ForwardReachable config anchorState anchorBlock store → store.timeMs ≤ timeMs →
      store.onTick config timeMs = .ok after → ForwardReachable config anchorState anchorBlock after
  /-- The store after a signed block. -/
  | block {store after : Store preset fork} {checks : SignatureChecks}
      {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork} :
    ForwardReachable config anchorState anchorBlock store →
      store.onBlock config checks sources signed = .ok after →
      ForwardReachable config anchorState anchorBlock after
  /-- The store after an attestation, from the wire or from a block. -/
  | attestation {store after : Store preset fork} {checks : SignatureChecks}
      {attestation : Attestation preset fork} {isFromBlock : Bool} :
    ForwardReachable config anchorState anchorBlock store →
      store.onAttestation config checks attestation isFromBlock = .ok after →
      ForwardReachable config anchorState anchorBlock after
  /-- The store after an attester slashing. -/
  | attesterSlashing {store after : Store preset fork} {checks : SignatureChecks}
      {slashing : AttesterSlashing preset fork} :
    ForwardReachable config anchorState anchorBlock store →
      store.onAttesterSlashing config checks slashing = .ok after →
      ForwardReachable config anchorState anchorBlock after
  /-- From Gloas, the store after a vote of a member of the payload committee. -/
  | payloadAttestation {store after : Store preset fork} {checks : SignatureChecks}
      {gloas : .glamsterdam ≤ fork} {message : PayloadAttestationMessage} {isFromBlock : Bool} :
    ForwardReachable config anchorState anchorBlock store →
      store.onPayloadAttestationMessage config checks gloas message isFromBlock = .ok after →
      ForwardReachable config anchorState anchorBlock after
  /-- From Gloas, the store after a signed envelope. -/
  | envelope {store after : Store preset fork} {checks : SignatureChecks}
      {sources : BlockSources preset fork} {gloas : .glamsterdam ≤ fork}
      {signed : SignedExecutionPayloadEnvelope preset fork} :
    ForwardReachable config anchorState anchorBlock store →
      store.onExecutionPayloadEnvelope config checks sources gloas signed = .ok after →
      ForwardReachable config anchorState anchorBlock after
  /-- From Heze, the store after an inclusion list. -/
  | inclusionList {store after : Store preset fork} {checks : SignatureChecks}
      {heze : .hegota ≤ fork} {signed : SignedInclusionList} :
    ForwardReachable config anchorState anchorBlock store →
      store.onInclusionList config checks heze signed = .ok after →
      ForwardReachable config anchorState anchorBlock after

/-- A store that the handlers build from an anchor with one setting of the signature checks.

No tick sets its time back, as for a store with a forward clock.

Every handler runs with the same setting, as on an honest node.

A block reads that setting: it skips a deposit for a new key with a bad signature.

From Electra the epoch step reads it too, so the setting can change the states of the store. -/
inductive ForwardReachableWith (config : Config) (checks : SignatureChecks)
    (anchorState : BeaconState preset fork) (anchorBlock : BeaconBlock preset fork) :
    Store preset fork → Prop where
  /-- The store built from the anchor. -/
  | anchor {store : Store preset fork} :
    getForkchoiceStore config anchorState anchorBlock = .ok store →
      ForwardReachableWith config checks anchorState anchorBlock store
  /-- The store after a tick to a time no earlier than its own. -/
  | tick {store after : Store preset fork} {timeMs : UInt64} :
    ForwardReachableWith config checks anchorState anchorBlock store → store.timeMs ≤ timeMs →
      store.onTick config timeMs = .ok after →
      ForwardReachableWith config checks anchorState anchorBlock after
  /-- The store after a signed block. -/
  | block {store after : Store preset fork} {sources : BlockSources preset fork}
      {signed : SignedBeaconBlock preset fork} :
    ForwardReachableWith config checks anchorState anchorBlock store →
      store.onBlock config checks sources signed = .ok after →
      ForwardReachableWith config checks anchorState anchorBlock after
  /-- The store after an attestation, from the wire or from a block. -/
  | attestation {store after : Store preset fork} {attestation : Attestation preset fork}
      {isFromBlock : Bool} :
    ForwardReachableWith config checks anchorState anchorBlock store →
      store.onAttestation config checks attestation isFromBlock = .ok after →
      ForwardReachableWith config checks anchorState anchorBlock after
  /-- The store after an attester slashing. -/
  | attesterSlashing {store after : Store preset fork} {slashing : AttesterSlashing preset fork} :
    ForwardReachableWith config checks anchorState anchorBlock store →
      store.onAttesterSlashing config checks slashing = .ok after →
      ForwardReachableWith config checks anchorState anchorBlock after
  /-- From Gloas, the store after a vote of a member of the payload committee. -/
  | payloadAttestation {store after : Store preset fork} {gloas : .glamsterdam ≤ fork}
      {message : PayloadAttestationMessage} {isFromBlock : Bool} :
    ForwardReachableWith config checks anchorState anchorBlock store →
      store.onPayloadAttestationMessage config checks gloas message isFromBlock = .ok after →
      ForwardReachableWith config checks anchorState anchorBlock after
  /-- From Gloas, the store after a signed envelope. -/
  | envelope {store after : Store preset fork} {sources : BlockSources preset fork}
      {gloas : .glamsterdam ≤ fork} {signed : SignedExecutionPayloadEnvelope preset fork} :
    ForwardReachableWith config checks anchorState anchorBlock store →
      store.onExecutionPayloadEnvelope config checks sources gloas signed = .ok after →
      ForwardReachableWith config checks anchorState anchorBlock after
  /-- From Heze, the store after an inclusion list. -/
  | inclusionList {store after : Store preset fork} {heze : .hegota ≤ fork}
      {signed : SignedInclusionList} :
    ForwardReachableWith config checks anchorState anchorBlock store →
      store.onInclusionList config checks heze signed = .ok after →
      ForwardReachableWith config checks anchorState anchorBlock after

variable {config : Config} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {store after : Store preset fork}

/-- A store with a forward clock is reachable. -/
theorem ForwardReachable.reachable
    (forward : ForwardReachable config anchorState anchorBlock store) :
    Reachable config anchorState anchorBlock store := by
  induction forward with
  | anchor made => exact .anchor made
  | tick _ _ ticked holds => exact holds.tick ticked
  | block _ added holds => exact holds.block added
  | attestation _ attested holds => exact holds.attestation attested
  | attesterSlashing _ slashed holds => exact holds.attesterSlashing slashed
  | payloadAttestation _ voted holds => exact holds.payloadAttestation voted
  | envelope _ accepted holds => exact holds.envelope accepted
  | inclusionList _ accepted holds => exact holds.inclusionList accepted

/-- A store built with one setting of the checks has a forward clock. -/
theorem ForwardReachableWith.forwardReachable {checks : SignatureChecks}
    (reached : ForwardReachableWith config checks anchorState anchorBlock store) :
    ForwardReachable config anchorState anchorBlock store := by
  induction reached with
  | anchor made => exact .anchor made
  | tick _ forward ticked holds => exact holds.tick forward ticked
  | block _ added holds => exact holds.block added
  | attestation _ attested holds => exact holds.attestation attested
  | attesterSlashing _ slashed holds => exact holds.attesterSlashing slashed
  | payloadAttestation _ voted holds => exact holds.payloadAttestation voted
  | envelope _ accepted holds => exact holds.envelope accepted
  | inclusionList _ accepted holds => exact holds.inclusionList accepted

/-- A store built with one setting of the checks is reachable. -/
theorem ForwardReachableWith.reachable {checks : SignatureChecks}
    (reached : ForwardReachableWith config checks anchorState anchorBlock store) :
    Reachable config anchorState anchorBlock store :=
  reached.forwardReachable.reachable

/-- A tick to a time no earlier than that of the store does not lower its current slot. -/
theorem getCurrentSlot_le_of_onTick {timeMs : UInt64} {slot later : Slot}
    (forward : store.timeMs ≤ timeMs) (ticked : store.onTick config timeMs = .ok after)
    (current : store.getCurrentSlot config = .ok slot)
    (next : after.getCurrentSlot config = .ok later) : slot ≤ later := by
  rw [getCurrentSlot_onTick ticked] at next
  unfold Store.getCurrentSlot at current
  exact computeSlotAtTimeMs_mono forward (mapError_ok_iff.mp current) (mapError_ok_iff.mp next)

/-- A tick to a time no earlier than that of the store keeps the current slot defined.

It does not lower that slot. -/
theorem exists_getCurrentSlot_onTick_ge {timeMs : UInt64} {current : Slot}
    (forward : store.timeMs ≤ timeMs) (ticked : store.onTick config timeMs = .ok after)
    (slotOk : store.getCurrentSlot config = .ok current) :
    ∃ later, after.getCurrentSlot config = .ok later ∧ current ≤ later := by
  obtain ⟨tickSlot, _, tickOk, -⟩ := onTick_ok ticked
  refine ⟨tickSlot, ?_, ?_⟩
  · rw [getCurrentSlot_onTick ticked, tickOk]
  · exact getCurrentSlot_le_of_onTick forward ticked slotOk
      (by rw [getCurrentSlot_onTick ticked, tickOk])

/-- A forward store has a defined current slot when the slot duration is positive. -/
theorem ForwardReachable.exists_getCurrentSlot
    (forward : ForwardReachable config anchorState anchorBlock store)
    (positive : 0 < config.SLOT_DURATION_MS) :
    ∃ current, store.getCurrentSlot config = .ok current := by
  induction forward with
  | anchor made =>
    exact ⟨_, getCurrentSlot_getForkchoiceStore positive made⟩
  | tick _ forward ticked holds =>
    obtain ⟨current, currentOk⟩ := holds
    obtain ⟨later, laterOk, -⟩ := exists_getCurrentSlot_onTick_ge forward ticked currentOk
    exact ⟨later, laterOk⟩
  | block _ step holds =>
    simpa only [(onBlock_sameClock step).getCurrentSlot] using holds
  | attestation _ step holds =>
    simpa only [(onAttestation_sameClock step).getCurrentSlot] using holds
  | attesterSlashing _ step holds =>
    simpa only [(onAttesterSlashing_sameClock step).getCurrentSlot] using holds
  | payloadAttestation _ step holds =>
    simpa only [(onPayloadAttestationMessage_sameClock step).getCurrentSlot] using holds
  | envelope _ step holds =>
    simpa only [(onExecutionPayloadEnvelope_sameClock step).getCurrentSlot] using holds
  | inclusionList _ step holds =>
    simpa only [(onInclusionList_sameClock step).getCurrentSlot] using holds

open Uint64 in
/-- The slot after one before a store's current slot exists, and starts by the store's clock.

The store must follow the model's time of genesis. -/
theorem nextSlotStart_le_clock {config : Config} {genesisTimeMs : UInt64}
    {store : Store preset fork}
    (genesisEq : store.genesisTimeMs = genesisTimeMs) {current slot : Slot}
    (currentOk : store.getCurrentSlot config = .ok current) (before : slot < current) :
    addChecked slot 1 = .ok (slot + 1) ∧ ∃ following,
      computeTimeAtSlotMs config genesisTimeMs (slot + 1) = .ok following ∧
      following.toNat ≤ store.timeMs.toNat := by
  have read := mapError_ok_iff.mp currentOk
  change computeSlotAtTimeMs config _ _ = .ok current at read
  rw [genesisEq] at read
  exact nextSlotStart_le_of_slotAtTime read before

end Store

end EthLib.Consensus
