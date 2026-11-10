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
  refine (frame_setValidator set found (by split <;> rfl) fun ordered => ?_).toFrame
  have le := ordered validator (mem_of_getValidator found)
  split <;> exact le

/-- A new genesis validators root keeps the invariant.

The invariant reads no such root. -/
private theorem Invariant.withGenesisValidatorsRoot {root : Root} (holds : Invariant state) :
    Invariant { state with genesisValidatorsRoot := root } :=
  ⟨holds.balancesMatch, holds.exitsOrdered, holds.ordered, holds.settled⟩

/-- A candidate genesis state exists only before Altair.

It satisfies the invariant that each valid block keeps.

The theorems on the state transition then apply to its chain, up to the first upgrade. -/
theorem initializeBeaconStateFromEth1_invariant {eth1BlockHash : Hash32} {eth1Timestamp : UInt64}
    {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok after) :
    fork < .altair ∧ Invariant after := by
  unfold initializeBeaconStateFromEth1 at computed
  split at computed
  · cases computed
  rename_i altair
  simp only [bind_ok_iff, ensure_ok_iff, liftSsz_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, deposited, depositedOk, activated, activatedOk, root, _, rfl⟩ :=
    computed
  have before : fork < .altair := Nat.lt_of_not_le altair
  refine ⟨before, ?_⟩
  have frame := (Frame.foldlM (fun _ _ _ ok => frame_genesisDeposit ok) depositedOk).trans
    (Frame.foldlM (fun _ _ _ ok => frame_activateAtGenesis ok) activatedOk)
  exact (frame.invariant (emptyGenesisState_invariant before _ _ _ _)).withGenesisValidatorsRoot

/-- A candidate state launches the chain exactly when it is late enough.

It must also have enough validators active at the genesis epoch. -/
theorem isValidGenesisState_iff :
    isValidGenesisState config state = true ↔
      config.MIN_GENESIS_TIME ≤ state.genesisTime ∧
        config.MIN_GENESIS_ACTIVE_VALIDATOR_COUNT.toNat ≤
          (getActiveValidatorIndices state GENESIS_EPOCH).length := by
  simp [isValidGenesisState]

end EthLib.Consensus
