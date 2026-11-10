module

public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Transition.Genesis

/-!
# Proofs: the genesis of the beacon chain

A candidate genesis state exists only before Altair.

It satisfies the invariant that each valid block keeps.

Its registry and balances have one entry for each validator.

Each of its validators may withdraw no earlier than it exits.

Its checkpoints all have the genesis epoch, so they are in order and settled.

A candidate state launches the chain exactly when it is late enough.

It must also have enough active validators.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- The empty state before the deposits satisfies the invariant. -/
theorem emptyGenesisState_invariant (before : fork < .altair) (genesisTime : UInt64)
    (eth1BlockHash : Hash32) (depositCount : UInt64) (bodyRoot : Root) :
    Invariant (emptyGenesisState (preset := preset) config before genesisTime eth1BlockHash
      depositCount bodyRoot) where
  balancesMatch := rfl
  exitsOrdered := fun _ member => by simp [emptyGenesisState] at member
  ordered := ⟨UInt64.le_refl _, UInt64.le_refl _⟩
  settled := UInt64.zero_le
  aligned _ _ member := by simp [emptyGenesisState] at member

theorem frame_genesisDeposit {before : fork < .hegota} {leaves : Array DepositData}
    {entry : Deposit × Nat}
    (computed : genesisDeposit config checks before leaves state entry = .ok after) :
    Frame state after := by
  simp only [genesisDeposit, bind_ok_iff] at computed
  obtain ⟨depositRoot, _, deposited⟩ := computed
  exact (Frame.of_validators (state := state)
    (after := { state with eth1Data := fun _ => { state.eth1Data before with depositRoot } })
    ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl rfl).trans (frame_processDeposit deposited).toFrame

/-- Setting the effective balance and the activation at genesis changes no exit. -/
theorem frame_activateAtGenesis {index : Nat}
    (computed : activateAtGenesis state index = .ok after) : Frame state after := by
  simp only [activateAtGenesis, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, _, _, set⟩ := computed
  refine (frame_setValidatorAt_of_whole set (fun ordered => ?_)
    fun maxAligned _ => ?_).toFrame
  · have le := ordered validator (mem_of_getValidatorAt found)
    split <;> exact le
  · split <;> exact min_sub_mod_mod_self _ maxAligned.1

/-- A new genesis validators root keeps the invariant.

The invariant reads no such root. -/
private theorem Invariant.withGenesisValidatorsRoot {root : Root} (holds : Invariant state) :
    Invariant { state with genesisValidatorsRoot := root } :=
  ⟨holds.balancesMatch, holds.exitsOrdered, holds.ordered, holds.settled, holds.aligned⟩

/-- The genesis state built from deposits, one stage at a time.

Its fork is before Altair.

It starts from an empty genesis state with the block hash and the deposit count.

It adds each deposit, then activates the validators.

The result then takes some genesis validators root. -/
theorem initializeBeaconStateFromEth1_ok {eth1BlockHash : Hash32} {eth1Timestamp : UInt64}
    {deposits : Array Deposit} {after : BeaconState preset fork}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok after) :
    ∃ (before : fork < .altair) (genesisTime : UInt64) (bodyRoot : Root)
      (deposited activated : BeaconState preset fork) (root : Root),
      deposits.toList.zipIdx.foldlM
          (genesisDeposit config checks (Nat.lt_trans before (by decide)) (deposits.map (·.data)))
          (emptyGenesisState config before genesisTime eth1BlockHash deposits.size.toUInt64
            bodyRoot) = .ok deposited ∧
        (List.range deposited.validators.data.size).foldlM activateAtGenesis deposited =
          .ok activated ∧
        after = { activated with genesisValidatorsRoot := root } := by
  unfold initializeBeaconStateFromEth1 at computed
  split at computed
  · cases computed
  rename_i altair
  simp only [bind_ok_iff, ensure_ok_iff, liftSsz_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨genesisTime, _, _, _, bodyRoot, _, deposited, depositedOk, activated, activatedOk, root,
    _, rfl⟩ := computed
  exact ⟨Nat.lt_of_not_le altair, genesisTime, bodyRoot, deposited, activated, root, depositedOk,
    activatedOk, rfl⟩

/-- The genesis state built from deposits keeps the frame of the empty state that it starts from.

Its fork is before Altair.

The empty state has the block hash and the deposit count.

The deposits and the activations keep the frame.

The result then takes some genesis validators root. -/
theorem initializeBeaconStateFromEth1_frame {eth1BlockHash : Hash32} {eth1Timestamp : UInt64}
    {deposits : Array Deposit} {after : BeaconState preset fork}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok after) :
    ∃ (before : fork < .altair) (genesisTime : UInt64) (bodyRoot : Root)
      (activated : BeaconState preset fork) (root : Root),
      Frame (emptyGenesisState config before genesisTime eth1BlockHash deposits.size.toUInt64
          bodyRoot) activated ∧
        after = { activated with genesisValidatorsRoot := root } := by
  obtain ⟨before, genesisTime, bodyRoot, _, activated, root, depositedOk, activatedOk, rfl⟩ :=
    initializeBeaconStateFromEth1_ok computed
  exact ⟨before, genesisTime, bodyRoot, activated, root,
    (Frame.foldlM (fun _ _ _ ok => frame_genesisDeposit ok) depositedOk).trans
      (Frame.foldlM (fun _ _ _ ok => frame_activateAtGenesis ok) activatedOk), rfl⟩

/-- The genesis state built from deposits is at the genesis slot.

Its two justified checkpoints are the genesis epoch with the zero root. -/
theorem initializeBeaconStateFromEth1_checkpoints {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit} {after : BeaconState preset fork}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok after) :
    after.slot = GENESIS_SLOT ∧
      after.previousJustifiedCheckpoint = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∧
      after.currentJustifiedCheckpoint = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ := by
  obtain ⟨_, _, _, _, _, frame, rfl⟩ := initializeBeaconStateFromEth1_frame computed
  exact ⟨frame.slot, frame.previousJustified, frame.currentJustified⟩

/-- The genesis state built from deposits has every bit of justification clear.

Its finalized checkpoint is the genesis epoch with the zero root. -/
theorem initializeBeaconStateFromEth1_finality {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit} {after : BeaconState preset fork}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok after) :
    after.justificationBits.bits = Vector.replicate _ false ∧
      after.finalizedCheckpoint = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ := by
  obtain ⟨_, _, _, _, _, frame, rfl⟩ := initializeBeaconStateFromEth1_frame computed
  exact ⟨congrArg (·.bits) frame.justificationBits, frame.finalized⟩

/-- A candidate genesis state exists only before Altair.

It satisfies the invariant that each valid block keeps.

The theorems on the state transition then apply to its chain, up to the first upgrade. -/
theorem initializeBeaconStateFromEth1_invariant {eth1BlockHash : Hash32} {eth1Timestamp : UInt64}
    {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok after) :
    fork < .altair ∧ Invariant after := by
  obtain ⟨before, _, _, _, _, frame, rfl⟩ := initializeBeaconStateFromEth1_frame computed
  exact ⟨before,
    (frame.invariant (emptyGenesisState_invariant before _ _ _ _)).withGenesisValidatorsRoot⟩

/-- A candidate state launches the chain exactly when it is late enough.

It must also have enough validators active at the genesis epoch. -/
theorem isValidGenesisState_iff :
    isValidGenesisState config state = true ↔
      config.MIN_GENESIS_TIME ≤ state.genesisTime ∧
        config.MIN_GENESIS_ACTIVE_VALIDATOR_COUNT.toNat ≤
          (getActiveValidatorIndices state GENESIS_EPOCH).length := by
  simp [isValidGenesisState]

end EthLib.Consensus
