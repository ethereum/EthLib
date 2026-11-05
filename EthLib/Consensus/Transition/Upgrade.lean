module

public import EthLib.Consensus.Credentials
public import EthLib.Consensus.ForkSchedule
public import EthLib.Consensus.PayloadTimeliness
public import EthLib.Consensus.Proposers
public import EthLib.Consensus.SyncCommittee
public import EthLib.Consensus.Transition.BuilderRequests
public import EthLib.Consensus.Transition.EpochJustification

/-!
# `Consensus.Transition.Upgrade`

The upgrade of a state to the next consensus fork, at the first slot of the fork epoch.

Up to Fulu, an upgrade carries every field and starts each new one at zero or empty.

Altair then turns the pending attestations of the previous epoch into flags.

It also fills both sync committees with the next sync committee.

Electra sets its churns and queues the balances of the validators that are not yet active.

It also queues the excess balance of each validator with compounding credentials.

Fulu computes the proposers of the current epoch and of the lookahead.

From Gloas: the upgrade of a Fulu state to a Gloas state.

From Heze: the upgrade of a Gloas state to a Heze state, at the first slot of its fork epoch.

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

The upgrade to Heze first asserts that the state has processed every deposit of the contract.

That holds when the count of processed deposits equals the index of the first deposit request.

The Heze state then keeps every Gloas field but those that [EIP-8015] removes.

These are the deposit contract data, its votes and the two deposit indices.

The latest bid stays, with the inclusion list bits of [EIP-7805] all unset.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#specification
[EIP-8282]: https://eips.ethereum.org/EIPS/eip-8282#fork-transition-onboarding
[EIP-8015]: https://eips.ethereum.org/EIPS/eip-8015#activation-conditions
[EIP-7805]: https://eips.ethereum.org/EIPS/eip-7805#consensus-layer
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz

variable {preset : Preset}

/-- A list of a state as the same list at a later fork before Gloas. -/
def carryList {fork post : Fork} {α : Type} {limit : Nat} (upgrade : fork < post)
    (list : ForkList .glamsterdam fork α limit) : ForkList .glamsterdam post α limit :=
  ⟨list.data, fun before => list.bound (Nat.lt_trans upgrade before)⟩

/-- A list with one zero for each validator of a state, at a later fork before Gloas. -/
def zeroPerValidator {fork post : Fork} {α : Type} [OfNat α 0] {limit : Nat}
    (upgrade : fork < post) (validators : ForkList .glamsterdam fork Validator limit) :
    ForkList .glamsterdam post α limit :=
  ⟨Array.replicate validators.data.size 0, fun before => by
    simpa using validators.bound (Nat.lt_trans upgrade before)⟩

/-- The state of a later fork before Gloas, with the fields of a state of an earlier fork.

The fork version moves to that of the later fork, at the current epoch.

Every field that both forks hold carries over.

A field that only the later fork holds starts at its initial value.

The flags and inactivity scores start at zero for each validator.

The latest payload header has zero in each field that the earlier header lacks.

The index of the first deposit request starts unset, as `2^64 - 1`.

Every other new field is zero or empty, and the upgrade to each fork computes those it needs. -/
def carryFields (config : Config) (post : Fork) {fork : Fork} (pre : BeaconState preset fork)
    (upgrade : fork < post) (before : post < .glamsterdam) : BeaconState preset post :=
  have early : fork < .glamsterdam := Nat.lt_trans upgrade before
  have beforeHeze : fork < .hegota := Nat.lt_trans early (by decide)
  { genesisTime := pre.genesisTime
    genesisValidatorsRoot := pre.genesisValidatorsRoot
    slot := pre.slot
    forkVersions :=
      { previousVersion := pre.forkVersions.currentVersion
        currentVersion := config.forkVersion post
        epoch := getCurrentEpoch pre }
    latestBlockHeader := pre.latestBlockHeader
    blockRoots := pre.blockRoots
    stateRoots := pre.stateRoots
    historicalRoots := pre.historicalRoots
    eth1Data := fun _ => pre.eth1Data beforeHeze
    eth1DataVotes := fun _ => pre.eth1DataVotes beforeHeze
    eth1DepositIndex := fun _ => pre.eth1DepositIndex beforeHeze
    validators := carryList upgrade pre.validators
    balances := carryList upgrade pre.balances
    randaoMixes := pre.randaoMixes
    slashings := pre.slashings
    previousEpochAttestations := fun phase0 =>
      pre.previousEpochAttestations (Nat.lt_trans upgrade phase0)
    currentEpochAttestations := fun phase0 =>
      pre.currentEpochAttestations (Nat.lt_trans upgrade phase0)
    previousEpochParticipation := fun _ =>
      if altair : .altair ≤ fork then carryList upgrade (pre.previousEpochParticipation altair)
      else zeroPerValidator upgrade pre.validators
    currentEpochParticipation := fun _ =>
      if altair : .altair ≤ fork then carryList upgrade (pre.currentEpochParticipation altair)
      else zeroPerValidator upgrade pre.validators
    justificationBits := pre.justificationBits
    previousJustifiedCheckpoint := pre.previousJustifiedCheckpoint
    currentJustifiedCheckpoint := pre.currentJustifiedCheckpoint
    finalizedCheckpoint := pre.finalizedCheckpoint
    inactivityScores := fun _ =>
      if altair : .altair ≤ fork then carryList upgrade (pre.inactivityScores altair)
      else zeroPerValidator upgrade pre.validators
    currentSyncCommittee := fun _ =>
      if altair : .altair ≤ fork then pre.currentSyncCommittee altair
      else SyncCommittee.empty preset
    nextSyncCommittee := fun _ =>
      if altair : .altair ≤ fork then pre.nextSyncCommittee altair
      else SyncCommittee.empty preset
    latestExecutionPayloadHeader := fun _ =>
      if bellatrix : .bellatrix ≤ fork then
        (pre.latestExecutionPayloadHeader ⟨bellatrix, early⟩).upgrade post
      else ExecutionPayloadHeader.empty preset post
    latestBlockHash := fun gloas => absurd gloas (Nat.not_le_of_lt before)
    nextWithdrawalIndex := fun _ =>
      if capella : .shapella ≤ fork then pre.nextWithdrawalIndex capella else 0
    nextWithdrawalValidatorIndex := fun _ =>
      if capella : .shapella ≤ fork then pre.nextWithdrawalValidatorIndex capella else 0
    historicalSummaries := fun _ =>
      if capella : .shapella ≤ fork then pre.historicalSummaries capella
      else ⟨#[], Nat.zero_le _⟩
    depositRequestsStartIndex := fun _ =>
      if electra : .pectra ≤ fork then pre.depositRequestsStartIndex ⟨electra, beforeHeze⟩
      else UNSET_DEPOSIT_REQUESTS_START_INDEX
    depositBalanceToConsume := fun _ =>
      if electra : .pectra ≤ fork then pre.depositBalanceToConsume electra else 0
    exitBalanceToConsume := fun _ =>
      if electra : .pectra ≤ fork then pre.exitBalanceToConsume electra else 0
    earliestExitEpoch := fun _ =>
      if electra : .pectra ≤ fork then pre.earliestExitEpoch electra else 0
    consolidationBalanceToConsume := fun _ =>
      if electra : .pectra ≤ fork then pre.consolidationBalanceToConsume electra else 0
    earliestConsolidationEpoch := fun _ =>
      if electra : .pectra ≤ fork then pre.earliestConsolidationEpoch electra else 0
    pendingDeposits := fun _ =>
      if electra : .pectra ≤ fork then carryList upgrade (pre.pendingDeposits electra)
      else ⟨#[], fun _ => Nat.zero_le _⟩
    pendingPartialWithdrawals := fun _ =>
      if electra : .pectra ≤ fork then carryList upgrade (pre.pendingPartialWithdrawals electra)
      else ⟨#[], fun _ => Nat.zero_le _⟩
    pendingConsolidations := fun _ =>
      if electra : .pectra ≤ fork then carryList upgrade (pre.pendingConsolidations electra)
      else ⟨#[], fun _ => Nat.zero_le _⟩
    proposerLookahead := fun _ =>
      if fulu : .fusaka ≤ fork then pre.proposerLookahead fulu else Vector.replicate _ 0
    builders := fun gloas => absurd gloas (Nat.not_le_of_lt before)
    nextWithdrawalBuilderIndex := fun gloas => absurd gloas (Nat.not_le_of_lt before)
    executionPayloadAvailability := fun gloas => absurd gloas (Nat.not_le_of_lt before)
    builderPendingPayments := fun gloas => absurd gloas (Nat.not_le_of_lt before)
    builderPendingWithdrawals := fun gloas => absurd gloas (Nat.not_le_of_lt before)
    latestExecutionPayloadBid := fun gloas => absurd gloas (Nat.not_le_of_lt before)
    payloadExpectedWithdrawals := fun gloas => absurd gloas (Nat.not_le_of_lt before)
    ptcWindow := fun gloas => absurd gloas (Nat.not_le_of_lt before) }

/-- From Altair: the state with the flags that one pending attestation of Phase 0 earned.

The attestation earns the flags of its source, target and head, at its inclusion delay.

Each member of its committee whose bit is set gets those flags for the previous epoch. -/
def translateAttestation {fork : Fork} (state : BeaconState preset fork)
    (altair : .altair ≤ fork) (attestation : PendingAttestation preset) :
    Except TransitionError (BeaconState preset fork) := do
  let flags ← liftAccessor (getAttestationParticipationFlagIndices state attestation.data
    attestation.inclusionDelay)
  let attesters ← liftAccessor (getPendingAttestingIndices state attestation)
  let participation ← attesters.foldlM (init := state.previousEpochParticipation altair)
    fun participation index => do
      let some old := participation.data[index.toNat]?
        | throw (.accessor (.indexOutOfRange index))
      return ⟨participation.data.set! index.toNat (flags.foldl addFlag old),
        fun before => by simpa using participation.bound before⟩
  return { state with previousEpochParticipation := fun _ => participation }

/-- The Altair state of a Phase 0 state, at the first slot of the fork epoch.

The fields carry over, and the pending attestations of the previous epoch become flags.

Both sync committees are then the next sync committee of that state. -/
def upgradeToAltair (config : Config) (pre : BeaconState preset .phase0) :
    Except TransitionError (BeaconState preset .altair) := do
  let post := carryFields config .altair pre (by decide) (by decide)
  let post ← (pre.previousEpochAttestations (by decide)).data.foldlM
    (fun state attestation => translateAttestation state (by decide) attestation) post
  let committee ← liftAccessor (getNextSyncCommittee post)
  return { post with
    currentSyncCommittee := fun _ => committee
    nextSyncCommittee := fun _ => committee }

/-- From Electra: the state in which a validator that is not yet active waits as a deposit.

Its balance and its effective balance become zero, and its eligibility is reset.

Its whole balance waits as a pending deposit, with the signature of the point at infinity.

The genesis slot tells that deposit apart from one that comes as a request. -/
def queuePreActivation {fork : Fork} (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (index : ValidatorIndex) : Except TransitionError (BeaconState preset fork) := do
  let validator ← liftAccessor (getValidator state index)
  let balance ← liftAccessor (getBalance state index)
  let deposit : PendingDeposit := ⟨validator.pubkey, validator.withdrawalCredentials, balance,
    Cryptography.Bls.Signatures.infinitySignature, GENESIS_SLOT⟩
  let pending ← liftAccessor (appendWithinLimit (state.pendingDeposits electra) deposit)
  let validator := { validator with
    effectiveBalance := 0, activationEligibilityEpoch := FAR_FUTURE_EPOCH }
  return { (state.setBalance index.toNat 0).setValidator index.toNat validator with
    pendingDeposits := fun _ => pending }

/-- The validators of a state that are not yet active.

They come in order of their eligibility epoch, and of their index within one epoch. -/
def preActivationIndices {fork : Fork} (state : BeaconState preset fork) : List ValidatorIndex :=
  let waiting := state.validators.data.toList.zipIdx.filter
    fun (validator, _) => validator.activationEpoch = FAR_FUTURE_EPOCH
  let sorted := waiting.mergeSort fun (first, i) (second, j) =>
    first.activationEligibilityEpoch < second.activationEligibilityEpoch ||
      (first.activationEligibilityEpoch == second.activationEligibilityEpoch && i ≤ j)
  sorted.map (·.2.toUInt64)

/-- From Electra: the state after the queueing of the excess balance of one validator.

Only a validator with compounding credentials queues its balance above the activation balance.
-/
def queueCompoundingExcess {fork : Fork} (state : BeaconState preset fork)
    (electra : .pectra ≤ fork) (index : Nat) : Except TransitionError (BeaconState preset fork) :=
  match state.validators.data[index]? with
  | some validator =>
    if hasCompoundingWithdrawalCredential validator then
      liftAccessor (queueExcessActiveBalance state electra index.toUInt64)
    else pure state
  | none => pure state

/-- The Electra state of a Deneb state, at the first slot of the fork epoch.

The earliest exit epoch is one after the latest of the activation exit epoch and every exit.

The earliest consolidation epoch is the activation exit epoch.

The churns of exits and of consolidations start full.

Each validator that is not yet active then waits as a pending deposit, in order of eligibility.

Last, each validator with compounding credentials queues its balance above the activation balance.

[EIP-7251] specifies these steps, and [EIP-6110] the unset index of the first deposit request.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
[EIP-6110]: https://eips.ethereum.org/EIPS/eip-6110#consensus-layer -/
def upgradeToElectra (config : Config) (pre : BeaconState preset .dencun) :
    Except TransitionError (BeaconState preset .pectra) := do
  let activationExit ← liftAccessor (liftArith (computeActivationExitEpoch preset
    (getCurrentEpoch pre)))
  let latestExit := pre.validators.data.foldl (init := activationExit) fun latest validator =>
    if validator.exitEpoch = FAR_FUTURE_EPOCH then latest else max latest validator.exitEpoch
  let earliestExit ← liftAccessor (liftArith (addChecked latestExit 1))
  let post := carryFields config .pectra pre (by decide) (by decide)
  let post := { post with
    earliestExitEpoch := fun _ => earliestExit
    earliestConsolidationEpoch := fun _ => activationExit }
  let exitChurn ← liftAccessor (getActivationExitChurnLimit config post)
  let post := { post with exitBalanceToConsume := fun _ => exitChurn }
  let consolidationChurn ← liftAccessor (getConsolidationChurnLimit config post)
  let post := { post with consolidationBalanceToConsume := fun _ => consolidationChurn }
  let post ← (preActivationIndices post).foldlM
    (fun state index => queuePreActivation state (by decide) index) post
  (List.range post.validators.data.size).foldlM
    (fun state index => queueCompoundingExcess state (by decide) index) post

/-- The Fulu state of an Electra state, at the first slot of the fork epoch.

The fields carry over, and the proposers of the current epoch and the lookahead are computed.

[EIP-7917] specifies the lookahead.

[EIP-7917]: https://eips.ethereum.org/EIPS/eip-7917#specification -/
def upgradeToFulu (config : Config) (pre : BeaconState preset .pectra) :
    Except TransitionError (BeaconState preset .fusaka) := do
  let post := carryFields config .fusaka pre (by decide) (by decide)
  let lookahead ← liftAccessor (initializeProposerLookahead post)
  return { post with proposerLookahead := fun _ => lookahead }

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

/-- A list of a Gloas state as the same list of a Heze state. -/
def toHezeList {α : Type} {limit : Nat} (list : ForkList .glamsterdam .glamsterdam α limit) :
    ForkList .glamsterdam .hegota α limit :=
  ⟨list.data, fun before => absurd before (by decide)⟩

/-- The latest bid of a fresh Heze state: the Gloas bid, with no inclusion list seen. -/
def upgradeBidToHeze (bid : ExecutionPayloadBid preset .glamsterdam) :
    ExecutionPayloadBid preset .hegota :=
  { parentBlockHash := bid.parentBlockHash
    parentBlockRoot := bid.parentBlockRoot
    blockHash := bid.blockHash
    prevRandao := bid.prevRandao
    feeRecipient := bid.feeRecipient
    gasLimit := bid.gasLimit
    builderIndex := bid.builderIndex
    slot := bid.slot
    value := bid.value
    executionPayment := bid.executionPayment
    blobKzgCommitments := toHezeList bid.blobKzgCommitments
    executionRequestsRoot := bid.executionRequestsRoot
    inclusionListBits := fun _ => ⟨Vector.replicate _ false⟩ }

/-- The Heze state of a Gloas state, with the fields of the deposit contract removed.

Every other field carries over, and the latest bid has no inclusion list bit set. -/
def upgradeHezeFields (config : Config) (pre : BeaconState preset .glamsterdam) :
    BeaconState preset .hegota :=
  { genesisTime := pre.genesisTime
    genesisValidatorsRoot := pre.genesisValidatorsRoot
    slot := pre.slot
    forkVersions :=
      { previousVersion := pre.forkVersions.currentVersion
        currentVersion := config.HEZE_FORK_VERSION
        epoch := getCurrentEpoch pre }
    latestBlockHeader := pre.latestBlockHeader
    blockRoots := pre.blockRoots
    stateRoots := pre.stateRoots
    historicalRoots := pre.historicalRoots
    eth1Data := fun before => absurd before (by decide)
    eth1DataVotes := fun before => absurd before (by decide)
    eth1DepositIndex := fun before => absurd before (by decide)
    validators := toHezeList pre.validators
    balances := toHezeList pre.balances
    randaoMixes := pre.randaoMixes
    slashings := pre.slashings
    previousEpochAttestations := fun before => absurd before (by decide)
    currentEpochAttestations := fun before => absurd before (by decide)
    previousEpochParticipation := fun _ => toHezeList (pre.previousEpochParticipation (by decide))
    currentEpochParticipation := fun _ => toHezeList (pre.currentEpochParticipation (by decide))
    justificationBits := pre.justificationBits
    previousJustifiedCheckpoint := pre.previousJustifiedCheckpoint
    currentJustifiedCheckpoint := pre.currentJustifiedCheckpoint
    finalizedCheckpoint := pre.finalizedCheckpoint
    inactivityScores := fun _ => toHezeList (pre.inactivityScores (by decide))
    currentSyncCommittee := fun _ => pre.currentSyncCommittee (by decide)
    nextSyncCommittee := fun _ => pre.nextSyncCommittee (by decide)
    latestExecutionPayloadHeader := fun during => absurd during.2 (by decide)
    latestBlockHash := fun _ => pre.latestBlockHash (by decide)
    nextWithdrawalIndex := fun _ => pre.nextWithdrawalIndex (by decide)
    nextWithdrawalValidatorIndex := fun _ => pre.nextWithdrawalValidatorIndex (by decide)
    historicalSummaries := fun _ => pre.historicalSummaries (by decide)
    depositRequestsStartIndex := fun during => absurd during.2 (by decide)
    depositBalanceToConsume := fun _ => pre.depositBalanceToConsume (by decide)
    exitBalanceToConsume := fun _ => pre.exitBalanceToConsume (by decide)
    earliestExitEpoch := fun _ => pre.earliestExitEpoch (by decide)
    consolidationBalanceToConsume := fun _ => pre.consolidationBalanceToConsume (by decide)
    earliestConsolidationEpoch := fun _ => pre.earliestConsolidationEpoch (by decide)
    pendingDeposits := fun _ => toHezeList (pre.pendingDeposits (by decide))
    pendingPartialWithdrawals := fun _ => toHezeList (pre.pendingPartialWithdrawals (by decide))
    pendingConsolidations := fun _ => toHezeList (pre.pendingConsolidations (by decide))
    proposerLookahead := fun _ => pre.proposerLookahead (by decide)
    builders := fun _ => pre.builders (by decide)
    nextWithdrawalBuilderIndex := fun _ => pre.nextWithdrawalBuilderIndex (by decide)
    executionPayloadAvailability := fun _ => pre.executionPayloadAvailability (by decide)
    builderPendingPayments := fun _ => pre.builderPendingPayments (by decide)
    builderPendingWithdrawals := fun _ => pre.builderPendingWithdrawals (by decide)
    latestExecutionPayloadBid := fun _ =>
      upgradeBidToHeze (pre.latestExecutionPayloadBid (by decide))
    payloadExpectedWithdrawals := fun _ => toHezeList (pre.payloadExpectedWithdrawals (by decide))
    ptcWindow := fun _ => pre.ptcWindow (by decide) }

/-- The Heze state of a Gloas state, at the first slot of the fork epoch.

It fails when the count of processed deposits differs from the first deposit request's index.
-/
def upgradeToHeze (config : Config) (pre : BeaconState preset .glamsterdam) :
    Except TransitionError (BeaconState preset .hegota) := do
  let processed := pre.eth1DepositIndex (by decide)
  let startIndex := pre.depositRequestsStartIndex (by decide)
  ensure (processed = startIndex) (.depositIndicesDiffer processed startIndex)
  return upgradeHezeFields config pre

end EthLib.Consensus
