module

public import EthLib.Consensus.PayloadTimeliness
public import EthLib.Consensus.Transition.BuilderRequests

/-!
# `Consensus.Transition.Upgrade`

From Gloas: the upgrade of a Fulu state to a Gloas state, at the first slot of the fork epoch.

The Gloas state keeps every Fulu field but the latest payload header.

The hash of that header becomes the latest block hash, and its fields seed the latest bid.

That bid is a self-build for the slot of the latest block, with no value.

The new builder fields start empty, and every payload of the recent slots counts as available.

The window of payload committees is computed for the current epoch and the lookahead.

Last, the pending deposits with builder credentials become builders.

A deposit stays in the queue when a validator holds its key or a valid pending deposit names it.

A deposit for a key that is already a builder adds to that builder's balance.

A builder deposit with an invalid signature is dropped.

Every other pending deposit stays in the queue, in its order.

A 64-bit overflow of a builder balance is an error.

[EIP-7732] adds the fields, and [EIP-8282] the onboarding of builders.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#specification
[EIP-8282]: https://eips.ethereum.org/EIPS/eip-8282#fork-transition-onboarding
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz

variable {preset : Preset}

/-- Whether a queue of deposits holds one for a key with a valid signature. -/
def isPendingValidator (config : Config) (checks : SignatureChecks)
    (pending : List PendingDeposit) (pubkey : BLSPubkey) : Except TransitionError Bool :=
  pending.anyM fun deposit =>
    if deposit.pubkey = pubkey then
      isValidDepositSignature config checks deposit.pubkey deposit.withdrawalCredentials
        deposit.amount deposit.signature
    else pure false

/-- One pending deposit at the fork: it stays in the queue, funds a builder, or is dropped.

The keys of the validators are fixed for the whole onboarding. -/
def onboardDeposit (config : Config) (checks : SignatureChecks)
    (validatorKeys : List BLSPubkey)
    (step : BeaconState preset .glamsterdam × Array PendingDeposit)
    (deposit : PendingDeposit) :
    Except TransitionError (BeaconState preset .glamsterdam × Array PendingDeposit) := do
  let (state, kept) := step
  let gloas : Fork.glamsterdam ≤ .glamsterdam := by decide
  if deposit.pubkey ∈ validatorKeys then return (state, kept.push deposit)
  match findBuilderByPubkey state gloas deposit.pubkey with
  | some index =>
    let builder := (state.builders gloas).data[index]
    let balance ← liftAccessor (liftArith (addChecked builder.balance deposit.amount))
    return (state.setBuilder index { builder with balance }, kept)
  | none =>
    if isBuilderWithdrawalCredential deposit.withdrawalCredentials = false then
      return (state, kept.push deposit)
    if ← isPendingValidator config checks kept.toList deposit.pubkey then
      return (state, kept.push deposit)
    if ← isValidDepositSignature config checks deposit.pubkey deposit.withdrawalCredentials
        deposit.amount deposit.signature then
      return (addBuilderToRegistry state gloas deposit.pubkey PAYLOAD_BUILDER_VERSION
        (credentialAddress deposit.withdrawalCredentials) deposit.amount deposit.slot, kept)
    else return (state, kept)

/-- The state after the pending deposits of builders become builders, at the fork. -/
def onboardBuildersFromPendingDeposits (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset .glamsterdam) :
    Except TransitionError (BeaconState preset .glamsterdam) := do
  let gloas : Fork.glamsterdam ≤ .glamsterdam := by decide
  let validatorKeys := (state.validators.data.map (·.pubkey)).toList
  let (state, kept) ← (state.pendingDeposits (by decide)).data.foldlM
    (onboardDeposit config checks validatorKeys) (state, #[])
  return { state with pendingDeposits := fun _ => ⟨kept, fun before => absurd before (by decide)⟩ }

/-- A list of a Fulu state as the same list of a Gloas state, whose type has no limit. -/
def toGloasList {α : Type} {limit : Nat} (list : ForkList .glamsterdam .fusaka α limit) :
    ForkList .glamsterdam .glamsterdam α limit :=
  ⟨list.data, fun before => absurd before (by decide)⟩

/-- The latest bid of a fresh Gloas state: the latest payload, built by its proposer.

It has the slot of the latest block, no value, no blobs and the root of no requests. -/
def upgradeBid (pre : BeaconState preset .fusaka) (requestsRoot : Root) :
    ExecutionPayloadBid preset .glamsterdam :=
  let header := pre.latestExecutionPayloadHeader (by decide)
  { parentBlockHash := header.parentHash
    parentBlockRoot := pre.latestBlockHeader.parentRoot
    blockHash := header.blockHash
    prevRandao := header.prevRandao
    feeRecipient := Vector.replicate 20 0
    gasLimit := header.gasLimit
    builderIndex := BUILDER_INDEX_SELF_BUILD
    slot := pre.latestBlockHeader.slot
    value := 0
    executionPayment := 0
    blobKzgCommitments := ⟨#[], fun before => absurd before (by decide)⟩
    executionRequestsRoot := requestsRoot
    inclusionListBits := fun later => absurd later (by decide) }

/-- The requests of a payload with no request. -/
def ExecutionRequests.empty (preset : Preset) : ExecutionRequests preset .glamsterdam where
  deposits := ⟨#[], fun before => absurd before (by decide)⟩
  withdrawals := ⟨#[], fun before => absurd before (by decide)⟩
  consolidations := ⟨#[], fun before => absurd before (by decide)⟩
  builderDeposits := fun _ => ⟨#[]⟩
  builderExits := fun _ => ⟨#[]⟩

/-- The Gloas state of a Fulu state, with its fields carried over and the new fields added.

The new fields are those of an empty registry of builders and of a self-built latest payload. -/
def upgradeFields (config : Config) (pre : BeaconState preset .fusaka) (requestsRoot : Root) :
    BeaconState preset .glamsterdam :=
  let header := pre.latestExecutionPayloadHeader (by decide)
  { genesisTime := pre.genesisTime
    genesisValidatorsRoot := pre.genesisValidatorsRoot
    slot := pre.slot
    forkVersions :=
      { previousVersion := pre.forkVersions.currentVersion
        currentVersion := config.GLOAS_FORK_VERSION
        epoch := getCurrentEpoch pre }
    latestBlockHeader := pre.latestBlockHeader
    blockRoots := pre.blockRoots
    stateRoots := pre.stateRoots
    historicalRoots := pre.historicalRoots
    eth1Data := fun _ => pre.eth1Data (by decide)
    eth1DataVotes := fun _ => pre.eth1DataVotes (by decide)
    eth1DepositIndex := fun _ => pre.eth1DepositIndex (by decide)
    validators := toGloasList pre.validators
    balances := toGloasList pre.balances
    randaoMixes := pre.randaoMixes
    slashings := pre.slashings
    previousEpochAttestations := fun before => absurd before (by decide)
    currentEpochAttestations := fun before => absurd before (by decide)
    previousEpochParticipation := fun _ => toGloasList (pre.previousEpochParticipation (by decide))
    currentEpochParticipation := fun _ => toGloasList (pre.currentEpochParticipation (by decide))
    justificationBits := pre.justificationBits
    previousJustifiedCheckpoint := pre.previousJustifiedCheckpoint
    currentJustifiedCheckpoint := pre.currentJustifiedCheckpoint
    finalizedCheckpoint := pre.finalizedCheckpoint
    inactivityScores := fun _ => toGloasList (pre.inactivityScores (by decide))
    currentSyncCommittee := fun _ => pre.currentSyncCommittee (by decide)
    nextSyncCommittee := fun _ => pre.nextSyncCommittee (by decide)
    latestExecutionPayloadHeader := fun during => absurd during.2 (by decide)
    latestBlockHash := fun _ => header.blockHash
    nextWithdrawalIndex := fun _ => pre.nextWithdrawalIndex (by decide)
    nextWithdrawalValidatorIndex := fun _ => pre.nextWithdrawalValidatorIndex (by decide)
    historicalSummaries := fun _ => pre.historicalSummaries (by decide)
    depositRequestsStartIndex := fun _ => pre.depositRequestsStartIndex (by decide)
    depositBalanceToConsume := fun _ => pre.depositBalanceToConsume (by decide)
    exitBalanceToConsume := fun _ => pre.exitBalanceToConsume (by decide)
    earliestExitEpoch := fun _ => pre.earliestExitEpoch (by decide)
    consolidationBalanceToConsume := fun _ => pre.consolidationBalanceToConsume (by decide)
    earliestConsolidationEpoch := fun _ => pre.earliestConsolidationEpoch (by decide)
    pendingDeposits := fun _ => toGloasList (pre.pendingDeposits (by decide))
    pendingPartialWithdrawals := fun _ => toGloasList (pre.pendingPartialWithdrawals (by decide))
    pendingConsolidations := fun _ => toGloasList (pre.pendingConsolidations (by decide))
    proposerLookahead := fun _ => pre.proposerLookahead (by decide)
    builders := fun _ => ⟨#[]⟩
    nextWithdrawalBuilderIndex := fun _ => 0
    executionPayloadAvailability := fun _ => ⟨Vector.replicate _ true⟩
    builderPendingPayments := fun _ => Vector.replicate _ BuilderPendingPayment.empty
    builderPendingWithdrawals := fun _ => ⟨#[]⟩
    latestExecutionPayloadBid := fun _ => upgradeBid pre requestsRoot
    payloadExpectedWithdrawals := fun _ => ⟨#[], fun before => absurd before (by decide)⟩
    ptcWindow := fun _ => Vector.replicate _ (Vector.replicate _ 0) }

/-- The Gloas state of a Fulu state, at the first slot of the fork epoch.

The fields carry over, and the window of payload committees is computed.

Then the pending deposits of builders become builders. -/
def upgradeToGloas (config : Config) (checks : SignatureChecks) (pre : BeaconState preset .fusaka) :
    Except TransitionError (BeaconState preset .glamsterdam) := do
  let requestsRoot ← liftSsz (SszType.hashTreeRoot (ExecutionRequests.empty preset))
  let post := upgradeFields config pre requestsRoot
  let window ← liftAccessor (initializePtcWindow post)
  onboardBuildersFromPendingDeposits config checks { post with ptcWindow := fun _ => window }

end EthLib.Consensus
