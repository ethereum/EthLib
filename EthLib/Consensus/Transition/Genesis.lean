module

public import EthLib.Consensus.Transition.Operations

/-!
# `Consensus.Transition.Genesis`

The genesis of the beacon chain, from a block of the proof-of-work chain and its deposits.

The candidate state starts empty at the genesis fork version.

Its genesis time is the time of the block plus a fixed delay.

Every RANDAO mix is the block hash.

The deposits then run in order.

Before each one, the vote on the deposit contract takes the root of the deposits up to it.

A validator whose balance reaches the largest effective balance is active from the genesis epoch.

The root of the registry then tells this chain apart from others.

A candidate state launches the chain once it is late enough and has enough active validators.

Altair and later forks start from a state of their own, which EthLib does not yet have here.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Serialization.Ssz.SszType Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork}

/-- A field that Altair or a later fork adds has no value before Altair. -/
theorem not_since_of_before_altair {added : Base.Fork} (before : fork < .altair)
    (later : .altair ≤ added) (since : added ≤ fork) : False :=
  Nat.lt_irrefl _ (Nat.lt_of_lt_of_le before (Nat.le_trans later since))

/-- The empty body of a block before Altair, whose root the empty genesis header holds. -/
def emptyBody (before : fork < .altair) : BeaconBlockBody preset fork where
  randaoReveal := Vector.replicate 96 0
  eth1Data := fun _ => ⟨Vector.replicate 32 0, 0, Vector.replicate 32 0⟩
  graffiti := Vector.replicate 32 0
  proposerSlashings := ⟨#[], fun _ => by simp⟩
  attesterSlashings := ⟨#[], fun _ => by simp⟩
  attestations := ⟨#[], fun _ => by simp⟩
  deposits := fun _ => ⟨#[], fun _ => by simp⟩
  voluntaryExits := ⟨#[], fun _ => by simp⟩
  syncAggregate := fun since => (not_since_of_before_altair before (by decide) since).elim
  executionPayload := fun during =>
    (not_since_of_before_altair before (by decide) during.1).elim
  blsToExecutionChanges := fun since =>
    (not_since_of_before_altair before (by decide) since).elim
  blobKzgCommitments := fun during =>
    (not_since_of_before_altair before (by decide) during.1).elim
  executionRequests := fun during =>
    (not_since_of_before_altair before (by decide) during.1).elim
  signedExecutionPayloadBid := fun since =>
    (not_since_of_before_altair before (by decide) since).elim
  payloadAttestations := fun since =>
    (not_since_of_before_altair before (by decide) since).elim
  parentExecutionRequests := fun since =>
    (not_since_of_before_altair before (by decide) since).elim

/-- The empty state before Altair from which genesis starts.

It holds the genesis time and the genesis fork version.

Its vote holds the deposit count and the block hash, and its header the root of the empty body.

Every RANDAO mix is the block hash.

Everything else is zero or empty. -/
def emptyGenesisState (config : Config) (before : fork < .altair) (genesisTime : UInt64)
    (eth1BlockHash : Hash32) (depositCount : UInt64) (bodyRoot : Root) :
    BeaconState preset fork where
  genesisTime
  genesisValidatorsRoot := Vector.replicate 32 0
  slot := GENESIS_SLOT
  forkVersions := ⟨config.GENESIS_FORK_VERSION, config.GENESIS_FORK_VERSION, GENESIS_EPOCH⟩
  latestBlockHeader := ⟨0, 0, Vector.replicate 32 0, Vector.replicate 32 0, bodyRoot⟩
  blockRoots := .ofVector (Vector.replicate _ (Vector.replicate 32 0))
  stateRoots := .ofVector (Vector.replicate _ (Vector.replicate 32 0))
  historicalRoots := ⟨#[], by simp⟩
  eth1Data := fun _ => ⟨Vector.replicate 32 0, depositCount, eth1BlockHash⟩
  eth1DataVotes := fun _ => ⟨#[], by simp⟩
  eth1DepositIndex := fun _ => 0
  validators := .ofData #[] fun _ => by simp
  balances := ⟨#[], fun _ => by simp⟩
  randaoMixes := .ofVector (Vector.replicate _ eth1BlockHash)
  slashings := .ofVector (Vector.replicate _ 0)
  previousEpochAttestations := fun _ => ⟨#[], by simp⟩
  currentEpochAttestations := fun _ => ⟨#[], by simp⟩
  previousEpochParticipation := fun since =>
    (not_since_of_before_altair before (by decide) since).elim
  currentEpochParticipation := fun since =>
    (not_since_of_before_altair before (by decide) since).elim
  justificationBits := ⟨Vector.replicate _ false⟩
  previousJustifiedCheckpoint := ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩
  currentJustifiedCheckpoint := ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩
  finalizedCheckpoint := ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩
  inactivityScores := fun since => (not_since_of_before_altair before (by decide) since).elim
  currentSyncCommittee := fun since => (not_since_of_before_altair before (by decide) since).elim
  nextSyncCommittee := fun since => (not_since_of_before_altair before (by decide) since).elim
  latestExecutionPayloadHeader := fun during =>
    (not_since_of_before_altair before (by decide) during.1).elim
  latestBlockHash := fun since => (not_since_of_before_altair before (by decide) since).elim
  nextWithdrawalIndex := fun since => (not_since_of_before_altair before (by decide) since).elim
  nextWithdrawalValidatorIndex := fun since =>
    (not_since_of_before_altair before (by decide) since).elim
  historicalSummaries := fun since => (not_since_of_before_altair before (by decide) since).elim
  depositRequestsStartIndex := fun during =>
    (not_since_of_before_altair before (by decide) during.1).elim
  depositBalanceToConsume := fun since =>
    (not_since_of_before_altair before (by decide) since).elim
  exitBalanceToConsume := fun since => (not_since_of_before_altair before (by decide) since).elim
  earliestExitEpoch := fun since => (not_since_of_before_altair before (by decide) since).elim
  consolidationBalanceToConsume := fun since =>
    (not_since_of_before_altair before (by decide) since).elim
  earliestConsolidationEpoch := fun since =>
    (not_since_of_before_altair before (by decide) since).elim
  pendingDeposits := fun since => (not_since_of_before_altair before (by decide) since).elim
  pendingPartialWithdrawals := fun since =>
    (not_since_of_before_altair before (by decide) since).elim
  pendingConsolidations := fun since =>
    (not_since_of_before_altair before (by decide) since).elim
  proposerLookahead := fun since => (not_since_of_before_altair before (by decide) since).elim
  builders := fun since => (not_since_of_before_altair before (by decide) since).elim
  nextWithdrawalBuilderIndex := fun since =>
    (not_since_of_before_altair before (by decide) since).elim
  executionPayloadAvailability := fun since =>
    (not_since_of_before_altair before (by decide) since).elim
  builderPendingPayments := fun since =>
    (not_since_of_before_altair before (by decide) since).elim
  builderPendingWithdrawals := fun since =>
    (not_since_of_before_altair before (by decide) since).elim
  latestExecutionPayloadBid := fun since =>
    (not_since_of_before_altair before (by decide) since).elim
  payloadExpectedWithdrawals := fun since =>
    (not_since_of_before_altair before (by decide) since).elim
  ptcWindow := fun since => (not_since_of_before_altair before (by decide) since).elim

/-- The largest number of deposits that the deposit contract holds: two to the depth of its tree.
-/
abbrev DEPOSIT_CONTRACT_LIMIT : Nat := 2 ^ DEPOSIT_CONTRACT_TREE_DEPTH.toNat

/-- The root of the first deposits, as a list of deposit data within the limit of the contract.

More deposits than the contract holds are an error. -/
def depositRootOf (leaves : Array DepositData) (count : Nat) : Except TransitionError Root :=
  let first := leaves.extract 0 count
  if bound : first.size ≤ DEPOSIT_CONTRACT_LIMIT then
    liftSsz (hashTreeRoot (⟨first, bound⟩ : SszList DepositData DEPOSIT_CONTRACT_LIMIT))
  else throw (.ssz (.merkleizeLimit first.size DEPOSIT_CONTRACT_LIMIT))

/-- The state after one deposit at genesis.

The vote on the deposit contract first takes the root of the deposits up to this one. -/
def genesisDeposit (config : Config) (checks : SignatureChecks) (before : fork < .hegota)
    (leaves : Array DepositData) (state : BeaconState preset fork) (entry : Deposit × Nat) :
    Except TransitionError (BeaconState preset fork) := do
  let (deposit, index) := entry
  let depositRoot ← depositRootOf leaves (index + 1)
  let eth1Data := { state.eth1Data before with depositRoot }
  processDeposit config checks before { state with eth1Data := fun _ => eth1Data } deposit

/-- The state in which one validator has its effective balance from its balance at genesis.

A validator with the largest effective balance is eligible and active from the genesis epoch. -/
def activateAtGenesis (state : BeaconState preset fork) (index : Nat) :
    Except TransitionError (BeaconState preset fork) := do
  let validator ← liftAccessor (getValidatorAt state index)
  let balance ← liftAccessor (getBalanceAt state index)
  let effectiveBalance := min (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT)
    preset.MAX_EFFECTIVE_BALANCE
  let validator := { validator with effectiveBalance }
  let validator :=
    if effectiveBalance = preset.MAX_EFFECTIVE_BALANCE then
      { validator with
        activationEligibilityEpoch := GENESIS_EPOCH, activationEpoch := GENESIS_EPOCH }
    else validator
  liftAccessor (state.setValidatorAt index validator)

/-- The candidate genesis state of a block of the proof-of-work chain, before Altair.

It takes the hash and the time of the block, and every deposit up to and including the block.

The genesis time and the deposit count must fit in 64 bits, and every deposit must be valid. -/
def initializeBeaconStateFromEth1 (config : Config) (checks : SignatureChecks)
    (eth1BlockHash : Hash32) (eth1Timestamp : UInt64) (deposits : Array Deposit) :
    Except TransitionError (BeaconState preset fork) :=
  if altair : .altair ≤ fork then throw (.accessor (.forkNotYetSpecified fork))
  else do
    have before : fork < .altair := Nat.lt_of_not_le altair
    have beforeHeze : fork < .hegota := Nat.lt_trans before (by decide)
    let genesisTime ← liftAccessor (liftArith (addChecked eth1Timestamp config.GENESIS_DELAY))
    ensure (deposits.size < 2 ^ 64) (.accessor (.arith .overflow))
    let bodyRoot ← liftSsz (hashTreeRoot (emptyBody (preset := preset) before))
    let state := emptyGenesisState config before genesisTime eth1BlockHash
      deposits.size.toUInt64 bodyRoot
    let leaves := deposits.map (·.data)
    let state ← deposits.toList.zipIdx.foldlM (genesisDeposit config checks beforeHeze leaves)
      state
    let state ← (List.range state.validators.data.size).foldlM activateAtGenesis state
    let genesisValidatorsRoot ← liftSsz (hashTreeRoot state.validators)
    return { state with genesisValidatorsRoot }

/-- Whether a candidate state launches the chain.

Its genesis time must be at least the earliest one.

Enough validators must be active at the genesis epoch. -/
def isValidGenesisState (config : Config) (state : BeaconState preset fork) : Bool :=
  config.MIN_GENESIS_TIME ≤ state.genesisTime &&
    config.MIN_GENESIS_ACTIVE_VALIDATOR_COUNT.toNat ≤
      (getActiveValidatorIndices state GENESIS_EPOCH).length

end EthLib.Consensus
