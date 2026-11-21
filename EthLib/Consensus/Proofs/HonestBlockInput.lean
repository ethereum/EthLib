module

public import EthLib.Consensus.Proofs.HonestValidator
public import EthLib.Consensus.Proofs.Transition.Committees
public import EthLib.Consensus.Proofs.Transition.Totality.Bound
public import EthLib.Consensus.Transition.StateTransition
public import EthLib.Serialization.Proofs.Ssz.Typed.Root
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.BalanceNotRaisedBlock
import EthLib.Consensus.Proofs.Transition.Block
import EthLib.Consensus.Proofs.Transition.Invariants
import EthLib.Consensus.Proofs.Transition.MixesKept
import EthLib.Consensus.Proofs.Transition.PayloadInputs
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle

/-!
# Proofs: the block of an honest proposer passes the steps before its operations

An honest proposer builds its block at the slot of the state, on the latest block.

It signs the epoch with its key for the RANDAO reveal.

It repeats the vote on the deposit contract that the state holds.

It carries no slashing, deposit, exit, change of credentials or request.

Its sync aggregate is empty, and its payload and attestations are given.

These are choices that an honest proposer may make, when no deposit is due.

Before Gloas, the steps of such a block before its operations pass.

That needs the execution part of the block to pass on the state after its header.

That part checks the payload against the state and asks the execution layer to accept it.

Both are assumptions of this file, since the execution layer builds the payload.

From Altair, the state they reach agrees with the first on what the attestations read.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz Serialization.Ssz.SszType

variable {preset : Preset} {fork : Base.Fork} {config : Config}

/-- A block that an honest proposer may build at the slot of a state, with its secret key.

It leaves out each operation it need not carry, so it fits a state with no deposit due.

It is at the slot of the state and names the proposer of that slot.

Its parent is the latest block header of the state.

Its RANDAO reveal is the signature of the epoch of its slot by the key.

Before Heze it repeats the vote on the deposit contract that the state already holds.

It carries no slashing, deposit, exit, change of credentials or request of the execution layer.

From Altair its sync aggregate sets no bit and carries the signature of the point at infinity.

Its graffiti, its payload, its blob commitments and its attestations are free.

So are the fields that only Gloas has, since the definition is for the blocks before Gloas. -/
structure HonestBlock (config : Config) (state : BeaconState preset fork)
    (key : Signatures.SecretKey) (block : BeaconBlock preset fork) : Prop where
  /-- The block is at the slot of the state. -/
  slot : block.slot = state.slot
  /-- It names the proposer of that slot. -/
  proposer : getBeaconProposerIndex state = .ok block.proposerIndex
  /-- Its parent is the latest block header of the state. -/
  parent : hashTreeRoot state.latestBlockHeader = .ok block.parentRoot
  /-- Its RANDAO reveal is the signature of its epoch by the key. -/
  reveal : getEpochSignature config state block key = .ok block.body.randaoReveal
  /-- Before Heze it votes for the deposit contract data of the state. -/
  eth1 : ∀ before : fork < .hegota, block.body.eth1Data before = state.eth1Data before
  /-- It carries no proposer slashing. -/
  proposerSlashings : block.body.proposerSlashings.data = #[]
  /-- It carries no attester slashing. -/
  attesterSlashings : block.body.attesterSlashings.data = #[]
  /-- Before Heze it carries no deposit. -/
  deposits : ∀ before : fork < .hegota, (block.body.deposits before).data = #[]
  /-- It carries no voluntary exit. -/
  voluntaryExits : block.body.voluntaryExits.data = #[]
  /-- From Capella it carries no change of withdrawal credentials. -/
  changes : ∀ capella : .shapella ≤ fork, (block.body.blsToExecutionChanges capella).data = #[]
  /-- From Electra to Fulu it carries no request of the execution layer. -/
  requests : ∀ electra : .pectra ≤ fork ∧ fork < .glamsterdam,
    (block.body.executionRequests electra).deposits.data = #[] ∧
      (block.body.executionRequests electra).withdrawals.data = #[] ∧
      (block.body.executionRequests electra).consolidations.data = #[]
  /-- From Altair its sync aggregate sets no bit. -/
  syncBits : ∀ altair : .altair ≤ fork,
    ∀ bit ∈ (block.body.syncAggregate altair).syncCommitteeBits.bits.toList, bit = false
  /-- From Altair its sync aggregate carries the signature of the point at infinity. -/
  syncSignature : ∀ altair : .altair ≤ fork,
    (block.body.syncAggregate altair).syncCommitteeSignature = Signatures.G2_POINT_AT_INFINITY

/-- Two states agree on what the attestations of a block read from Altair, and on its deposits.

They have the same slot, registry, justified checkpoints and buffer of block roots.

They have the same flags of participation, fork versions and genesis validators root.

They have the same committees in the previous and the current epoch.

They expect the same number of deposits, and hold the same current sync committee.

Every budget that bounds the first state bounds the second. -/
structure AttestationReadsKept (state input : BeaconState preset fork) : Prop where
  /-- The slot is the same. -/
  slot : input.slot = state.slot
  /-- The registry is the same. -/
  validators : input.validators = state.validators
  /-- The previous justified checkpoint is the same. -/
  previousJustified : input.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint
  /-- The current justified checkpoint is the same. -/
  currentJustified : input.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint
  /-- The buffer of block roots is the same. -/
  blockRoots : input.blockRoots = state.blockRoots
  /-- The flags of the previous epoch are the same. -/
  previousParticipation : input.previousEpochParticipation = state.previousEpochParticipation
  /-- The flags of the current epoch are the same. -/
  currentParticipation : input.currentEpochParticipation = state.currentEpochParticipation
  /-- The fork versions are the same. -/
  forkVersions : input.forkVersions = state.forkVersions
  /-- The genesis validators root is the same. -/
  genesisValidatorsRoot : input.genesisValidatorsRoot = state.genesisValidatorsRoot
  /-- The committees of the previous and of the current epoch are the same. -/
  committees : ∀ epoch, getPreviousEpoch state ≤ epoch → epoch ≤ getCurrentEpoch state →
    CommitteesKept epoch state input
  /-- Before Heze, the number of deposits that a block must carry is the same. -/
  deposits : ∀ before : fork < .hegota,
    expectedDepositCount input before = expectedDepositCount state before
  /-- The current sync committee is the same. -/
  syncCommittee : input.currentSyncCommittee = state.currentSyncCommittee
  /-- Every budget of the first state is a budget of the second. -/
  budget : ∀ budget scoreBound, WithinBudget budget scoreBound state →
    WithinBudget budget scoreBound input

/-! ## The fields that the steps before the operations keep -/

/-- The fields of a state that the header and the execution part of a block keep. -/
private def keptOf (state : BeaconState preset fork) :=
  (state.slot, state.validators, state.previousJustifiedCheckpoint,
    state.currentJustifiedCheckpoint, state.blockRoots, state.previousEpochParticipation,
    state.currentEpochParticipation, state.forkVersions, state.genesisValidatorsRoot,
    state.currentSyncCommittee, state.randaoMixes, state.proposerLookahead, state.eth1Data,
    state.eth1DataVotes, state.eth1DepositIndex, state.depositRequestsStartIndex,
    state.pendingDeposits, state.slashings, state.inactivityScores,
    state.depositBalanceToConsume, state.exitBalanceToConsume)

/-- The execution part of a block keeps those fields. -/
private theorem keptOf_processBlockExecution {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    keptOf after = keptOf state := by
  refine processBlockExecution_of (fun s t => keptOf t = keptOf s) (fun _ => rfl)
    (fun one two => two.trans one) (fun ok => ?_) (fun ok => ?_) (fun ok => ?_) computed
  -- The payload writes only the header of the latest payload.
  · obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
    rfl
  -- The bid writes only the payments of builders and the latest bid.
  · obtain ⟨_, rfl⟩ := processExecutionPayloadBid_eq ok
    rfl
  -- The withdrawals write only balances, builders and the bookkeeping of withdrawals.
  · refine processWithdrawals_of (fun s t => keptOf t = keptOf s) rfl (fun _ applied => ?_) ok
    refine applyExpectedWithdrawals_of_setters (fun s t => keptOf t = keptOf s) (fun _ => rfl)
      (fun one two => two.trans one) (fun withdrawn => ?_) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) applied
    rw [applyWithdrawal_eq withdrawn]
    rfl

/-! ## Each step passes -/

/-- The header of an honest block passes, when the proposer is not slashed. -/
private theorem processBlockHeader_honest [LawfulSszType (BeaconBlockBody preset fork)]
    {state : BeaconState preset fork} {key : Signatures.SecretKey}
    {block : BeaconBlock preset fork} (honest : HonestBlock config state key block)
    {validator : Validator} (found : getValidator state block.proposerIndex = .ok validator)
    (notSlashed : validator.slashed = false)
    (fresh : state.latestBlockHeader.slot < state.slot) :
    ∃ headed, processBlockHeader state block = .ok headed := by
  obtain ⟨bodyRoot, rooted⟩ := hashTreeRoot_total block.body
  simp only [processBlockHeader, ensure, honest.slot, fresh, honest.proposer, honest.parent,
    rooted, found, notSlashed, liftAccessor, liftSsz, Except.mapError, bind, Except.bind, pure,
    Except.pure, ↓reduceIte]
  exact ⟨_, rfl⟩

/-- The RANDAO reveal of the proposer passes, when the ring of mixes is not empty.

The block must be for a slot of the current epoch, and the proposer must have the public key. -/
private theorem processRandao_honest {state : BeaconState preset fork}
    {block : BeaconBlock preset fork} {key : Signatures.SecretKey}
    {proposerIndex : ValidatorIndex} {proposer : Validator}
    (nonzero : preset.EPOCHS_PER_HISTORICAL_VECTOR ≠ 0)
    (proposes : getBeaconProposerIndex state = .ok proposerIndex)
    (registered : getValidator state proposerIndex = .ok proposer)
    (owned : proposer.pubkey = Signatures.skToPk key)
    (current : computeEpochAtSlot preset block.slot = getCurrentEpoch state)
    (signedBy : getEpochSignature config state block key = .ok block.body.randaoReveal) :
    ∃ after, processRandao config .bls state block.body = .ok after := by
  unfold getEpochSignature at signedBy
  simp only [current] at signedBy
  -- Split the signature with its lemma, so the kernel never evaluates it.
  obtain ⟨domain, root, domained, rooted, verifies⟩ := signAtEpoch_verifies signedBy
  have domainDefault : getDomain config state DOMAIN_RANDAO = .ok domain := domained
  unfold processRandao getRandaoMix readCircular writeCircularRooted
  simp only [liftAccessor, liftSsz, proposes, registered, domainDefault, rooted, Except.mapError,
    bind, Except.bind, pure, Except.pure, owned, SignatureChecks.bls, verifies, ensure,
    ↓reduceIte, nonzero, ↓reduceDIte]
  exact ⟨_, rfl⟩

/-- The vote on the deposit contract passes when the votes leave room for one more. -/
private theorem processEth1Data_room (before : fork < .hegota) {state : BeaconState preset fork}
    {body : BeaconBlockBody preset fork}
    (room : (state.eth1DataVotes before).data.size <
      preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (fits : preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64) :
    ∃ after, processEth1Data before state body = .ok after := by
  -- The length of the period is a product that does not overflow.
  have product : Uint64.mulChecked preset.EPOCHS_PER_ETH1_VOTING_PERIOD preset.SLOTS_PER_EPOCH =
      .ok (preset.EPOCHS_PER_ETH1_VOTING_PERIOD * preset.SLOTS_PER_EPOCH) :=
    Uint64.mulChecked_ok_iff.mpr ⟨fits, by rw [UInt64.toNat_mul]; omega⟩
  have bound : ((state.eth1DataVotes before).data.push (body.eth1Data before)).size ≤
      preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * preset.SLOTS_PER_EPOCH.toNat := by
    rw [Array.size_push]
    omega
  unfold processEth1Data
  simp only [bound, ↓reduceDIte, liftAccessor, liftArith, product, Except.mapError, bind,
    Except.bind, pure, Except.pure]
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-! ## The budget -/

/-- A sum read in step with balances does not rise when no balance rises. -/
private theorem sum_zipWith_max_le :
    ∀ (items : List Validator) (low high : List UInt64), low.length = high.length →
      (∀ i (lt : i < low.length) (lt' : i < high.length), low[i] ≤ high[i]) →
      (items.zipWith (fun v b => max v.effectiveBalance.toNat b.toNat) low).sum ≤
        (items.zipWith (fun v b => max v.effectiveBalance.toNat b.toNat) high).sum
  | [], _, _, _, _ => by simp
  | _ :: _, [], [], _, _ => by simp
  | _ :: _, [], _ :: _, same, _ => by simp at same
  | _ :: _, _ :: _, [], same, _ => by simp at same
  | v :: items, l :: low, h :: high, same, le => by
    simp only [List.zipWith_cons_cons, List.sum_cons]
    have head := UInt64.le_iff_toNat_le.mp (le 0 (by simp) (by simp))
    have tail := sum_zipWith_max_le items low high (by simpa using same)
      (fun i lt lt' => le (i + 1) (by simp; omega) (by simp; omega))
    simp only [List.getElem_cons_zero] at head
    omega

/-- A step that keeps the registry and the number of balances, and raises no balance.

It does not raise the stake sum. -/
private theorem stakeSum_le {state after : BeaconState preset fork}
    (validators : after.validators = state.validators)
    (sizes : after.balances.data.size = state.balances.data.size)
    (down : ∀ index, BalanceDown index state after) : stakeSum after ≤ stakeSum state := by
  unfold stakeSum
  rw [validators]
  refine sum_zipWith_max_le _ _ _ (by simpa using sizes) fun i lt lt' => ?_
  -- The balance at the position after the step is at most the one before.
  obtain ⟨later, found, le⟩ := down i _ (Array.getElem?_eq_getElem (by simpa using lt'))
  simp only [Array.getElem_toList]
  rw [Array.getElem?_eq_getElem (by simpa using lt), Option.some.injEq] at found
  rw [found]
  exact le

/-- A step that keeps the registry and raises no balance keeps every budget.

It must also keep the sizes of the balances, the pending deposits and the slashings.

It must keep the inactivity scores and the balances left to consume. -/
private theorem withinBudget_kept {state input : BeaconState preset fork} {budget scoreBound : Nat}
    (validators : input.validators = state.validators)
    (matching : BalancesMatch state → BalancesMatch input)
    (down : ∀ index, BalanceDown index state input)
    (pendingI : input.pendingDeposits = state.pendingDeposits)
    (slashingsI : input.slashings = state.slashings)
    (scoresI : input.inactivityScores = state.inactivityScores)
    (depositI : input.depositBalanceToConsume = state.depositBalanceToConsume)
    (exitI : input.exitBalanceToConsume = state.exitBalanceToConsume)
    (holds : WithinBudget budget scoreBound state) : WithinBudget budget scoreBound input := by
  have matched := matching holds.matched
  have sizes : input.balances.data.size = state.balances.data.size := by
    have before := holds.matched
    unfold BalancesMatch at matched before
    rw [matched, before, validators]
  have pending : pendingDepositSum input = pendingDepositSum state := by
    unfold pendingDepositSum
    rw [pendingI]
  refine ⟨?_, matched, ?_, ?_, ?_, ?_, ?_⟩
  · unfold BeaconState.RegistryWithinLimit
    rw [validators]
    exact holds.within
  · rw [validators]
    exact holds.capped
  -- The stake sum does not rise, and the pending deposits stay.
  · have := stakeSum_le validators sizes down
    have := holds.funded
    omega
  · unfold slashedBalanceSum
    rw [slashingsI]
    exact holds.slashed
  · rw [scoresI]
    exact holds.scored
  · rw [depositI, exitI]
    exact holds.carried

/-- Before Gloas, the steps of an honest block before its operations pass.

The proposer must hold the public key of the secret key, and must not be slashed.

The state must hold no block at its slot yet.

Before Heze the votes on the deposit contract must leave room for one more in the period.

That holds on every state reached from genesis, since the votes restart with each period.

The execution part of the block must pass on the state after its header, an assumption.

It checks the withdrawals and the payload against the state, and asks the execution layer.

The state that the steps reach names the proposer of the block.

From Altair it agrees with the state before the block on what the attestations read.

The mixes must span more than the seed lookahead plus two epochs.

The encoding of a block body must be lawful, so that the body has a root.

It is lawful for every preset whose sizes of lists and vectors are not zero. -/
theorem stateBeforeOperations_honestBlock [LawfulSszType (BeaconBlockBody preset fork)]
    (beforeGloas : fork < .glamsterdam)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {state : BeaconState preset fork} {key : Signatures.SecretKey}
    {block : BeaconBlock preset fork} {engine : ExecutionEngine preset fork}
    (honest : HonestBlock config state key block)
    (owned : ∃ validator, getValidator state block.proposerIndex = .ok validator ∧
      validator.pubkey = Signatures.skToPk key ∧ validator.slashed = false)
    (fresh : state.latestBlockHeader.slot < state.slot)
    (votesRoom : ∀ before : fork < .hegota, (state.eth1DataVotes before).data.size <
      preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (periodFits :
      preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64)
    (executes : ∀ headed, processBlockHeader state block = .ok headed →
      ∀ bellatrix : .bellatrix ≤ fork, ∃ executed,
        processBlockExecution config .bls engine headed block.body bellatrix = .ok executed) :
    ∃ input, stateBeforeOperations config .bls engine state block = .ok input ∧
      getBeaconProposerIndex input = .ok block.proposerIndex ∧
      AttestationReadsKept state input := by
  obtain ⟨validator, found, pubkey, notSlashed⟩ := owned
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt beforeGloas
  have nonzero : preset.EPOCHS_PER_HISTORICAL_VECTOR ≠ 0 := by
    intro zero
    rw [zero] at apart
    simp at apart
  -- The header passes, and keeps the fields that the later steps read.
  obtain ⟨headed, headerOk⟩ := processBlockHeader_honest honest found notSlashed fresh
  have headedKept : keptOf headed = keptOf state := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headerOk
    rfl
  -- From Bellatrix the execution part passes by assumption, and keeps the same fields.
  have executedExists : ∃ executed, (if bellatrix : .bellatrix ≤ fork then
        processBlockExecution config .bls engine headed block.body bellatrix
      else pure headed) = .ok executed ∧ keptOf executed = keptOf state := by
    by_cases bellatrix : .bellatrix ≤ fork
    · obtain ⟨executed, ok⟩ := executes headed headerOk bellatrix
      exact ⟨executed, by simp only [bellatrix, ↓reduceDIte]; exact ok,
        (keptOf_processBlockExecution ok).trans headedKept⟩
    · exact ⟨headed, by simp only [bellatrix, ↓reduceDIte]; rfl, headedKept⟩
  obtain ⟨executed, executionOk, executedKept⟩ := executedExists
  simp only [keptOf, Prod.mk.injEq] at executedKept
  obtain ⟨slotE, validatorsE, -, -, -, previousE, currentE, versionsE, rootE, -, mixesE, lookE,
    eth1E, votesE, indexE, startE, pendingE, slashingsE, scoresE, depositE, exitE⟩ :=
    executedKept
  -- The RANDAO reveal passes, since the execution part keeps what it reads.
  have proposes : getBeaconProposerIndex executed = .ok block.proposerIndex := by
    rw [getBeaconProposerIndex_congr slotE mixesE (fun _ => by rw [lookE])
      (by unfold getActiveValidatorIndicesChecked; rw [validatorsE])
      (fun _ _ => by rw [validatorsE])]
    exact honest.proposer
  have registered : getValidator executed block.proposerIndex = .ok validator := by
    unfold getValidator
    rw [validatorsE]
    exact found
  have epochE : getCurrentEpoch executed = getCurrentEpoch state := by
    unfold getCurrentEpoch
    rw [slotE]
  have current : computeEpochAtSlot preset block.slot = getCurrentEpoch executed := by
    rw [epochE, honest.slot]
    rfl
  have signed : getEpochSignature config executed block key = .ok block.body.randaoReveal := by
    rw [← honest.reveal]
    unfold getEpochSignature signAtEpoch getDomain
    rw [versionsE, rootE, epochE]
  obtain ⟨revealed, randaoOk⟩ :=
    processRandao_honest nonzero proposes registered pubkey current signed
  have written := mixesKeptBut_processRandao randaoOk
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, revealedEq⟩ := processRandao_eq randaoOk
  -- Before Heze the vote passes, since the earlier steps keep the votes.
  have votedExists : ∃ input, (if early : fork < .hegota then
      processEth1Data early revealed block.body else pure revealed) = .ok input := by
    by_cases early : fork < .hegota
    · simp only [early, ↓reduceDIte]
      refine processEth1Data_room early ?_ periodFits
      rw [revealedEq]
      show (executed.eth1DataVotes early).data.size < _
      rw [votesE]
      exact votesRoom early
    · simp only [early, ↓reduceDIte]
      exact ⟨_, rfl⟩
  obtain ⟨input, eth1Ok⟩ := votedExists
  have started : OperationsInput config .bls engine state block input :=
    ⟨state, headed, executed, revealed, by simp only [notGloas, ↓reduceDIte]; rfl, headerOk,
      executionOk, randaoOk, eth1Ok⟩
  have computed : stateBeforeOperations config .bls engine state block = .ok input := by
    unfold stateBeforeOperations
    simp only [notGloas, ↓reduceDIte, pure_bind, bind_ok_iff]
    exact ⟨headed, headerOk, executed, executionOk, revealed, randaoOk, eth1Ok⟩
  obtain ⟨proposer, sync, down⟩ := operationsInput_proposer apart started
  have frame := frame_operationsInput started
  have validators := started.validators_eq beforeGloas
  -- The vote changes only the votes and the deposit contract data.
  have rest : { input with
      eth1DataVotes := revealed.eth1DataVotes, eth1Data := revealed.eth1Data } = revealed := by
    split at eth1Ok
    · exact (processEth1Data_eq eth1Ok).2.2
    · cases eth1Ok
      rfl
  -- The vote repeats the data of the state, so the data stays.
  have eth1Same : ∀ early : fork < .hegota, input.eth1Data early = state.eth1Data early := by
    intro early
    simp only [early, ↓reduceDIte] at eth1Ok
    rw [(processEth1Data_eq eth1Ok).2.1, honest.eth1 early]
    have kept : revealed.eth1Data early = state.eth1Data early := by
      rw [revealedEq]
      exact congrFun eth1E early
    rw [kept]
    split <;> rfl
  -- The RANDAO step writes only the mix of the current epoch.
  have mixes : MixesKeptBut (getCurrentEpoch state) state input := by
    intro other far
    have kept : input.randaoMixes = revealed.randaoMixes := by
      have field := congrArg BeaconState.randaoMixes rest
      exact field
    show readCircular input.randaoMixes.elements other = _
    rw [kept, written other (by rw [epochE]; exact far), mixesE]
  subst revealedEq
  refine ⟨input, computed, proposer, ?_⟩
  have indexI : input.eth1DepositIndex = state.eth1DepositIndex :=
    (congrArg BeaconState.eth1DepositIndex rest).trans indexE
  have startI : input.depositRequestsStartIndex = state.depositRequestsStartIndex :=
    (congrArg BeaconState.depositRequestsStartIndex rest).trans startE
  have pendingI : input.pendingDeposits = state.pendingDeposits :=
    (congrArg BeaconState.pendingDeposits rest).trans pendingE
  have slashingsI : input.slashings = state.slashings :=
    (congrArg BeaconState.slashings rest).trans slashingsE
  have scoresI : input.inactivityScores = state.inactivityScores :=
    (congrArg BeaconState.inactivityScores rest).trans scoresE
  have depositI : input.depositBalanceToConsume = state.depositBalanceToConsume :=
    (congrArg BeaconState.depositBalanceToConsume rest).trans depositE
  have exitI : input.exitBalanceToConsume = state.exitBalanceToConsume :=
    (congrArg BeaconState.exitBalanceToConsume rest).trans exitE
  refine ⟨frame.slot, validators, frame.previousJustified, frame.currentJustified,
    frame.blockRoots, (congrArg BeaconState.previousEpochParticipation rest).trans previousE,
    (congrArg BeaconState.currentEpochParticipation rest).trans currentE, frame.forkVersions,
    frame.genesisValidatorsRoot, ?_, ?_, sync, ?_⟩
  -- The committees read the registry and mixes that the RANDAO step does not write.
  · intro epoch low high
    have previous := getPreviousEpoch_toNat state
    have lowNat := UInt64.le_iff_toNat_le.mp low
    exact CommitteesKept.of_activeKept apart
      (ActiveKept.of_validators (by rw [validators]) _) mixes high (by omega)
  -- The deposits read the deposit index, the deposit contract data and the start of requests.
  · intro early
    unfold expectedDepositCount
    rw [eth1Same early, indexI, startI]
  -- The budget reads the registry, the balances that do not rise and fields kept.
  · exact fun _ _ holds => withinBudget_kept validators frame.balancesMatch down pendingI
      slashingsI scoresI depositI exitI holds

end EthLib.Consensus
