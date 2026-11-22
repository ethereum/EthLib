module

public import EthLib.Consensus.Exports.Ssz
public import EthLib.Consensus.PayloadTimeliness
public import EthLib.Consensus.Proposers
public import EthLib.Consensus.Transition.Block
public import EthLib.Consensus.Transition.BuilderPayments
public import EthLib.Consensus.Transition.BuilderRequests
public import EthLib.Consensus.Transition.EpochJustification
public import EthLib.Consensus.Transition.EpochPending
public import EthLib.Consensus.Transition.EpochRewards
public import EthLib.Consensus.Transition.EpochUpdates
public import EthLib.Consensus.Transition.Execution
public import EthLib.Consensus.Transition.ForkBoundary
public import EthLib.Consensus.Transition.Operations
public import EthLib.Consensus.Transition.ParentPayload
public import EthLib.Consensus.Transition.Payload
public import EthLib.Consensus.Transition.Requests
public import EthLib.Consensus.Transition.SyncAggregate
public import EthLib.Consensus.Transition.StateTransition
public import EthLib.Consensus.Transition.Upgrade
public import EthLib.Consensus.Transition.Withdrawals

/-!
# `Exports.Transition`

C-ABI exports of the steps of the beacon state transition, for the consensus test vectors.

One export runs a block operation on a state, and another one step of the epoch transition.

Two more advance a state by some slots, and run the whole transition of a signed block.

They take and return states as SSZ bytes, and accept forks up to Heze.

From Gloas, only the steps whose Gloas rule EthLib holds run.

Another export upgrades a state to the next consensus fork, from Altair to Heze.

Another runs a signed block from a state of an earlier fork, across the fork epochs between.

Two more run a sequence of signed blocks in one call, in each of these two ways.

The state is then decoded and encoded once, not once for each block.

The configuration of a name holds, with the replacements that a `dict` gives.

The exports take the tuple of their arguments as typed Python values.

It checks the BLS signatures, or accepts every signature for the vectors with placeholder ones.

The vectors fix the answer of the execution layer to a payload, and so does the operation export.

An input that does not decode, or an unknown name, has code 0.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz
open EthLib.Exports (ExportError Result PyValue UnreadArgument pyExport rejectArgument
  toResult)

/-- The value of a type that SSZ bytes encode. -/
def decodeInput (α : Type) [SszType α] (data : ByteArray) : Result α :=
  toResult none ((SszType.deserialize α data).mapError fun e =>
    UnreadArgument.mk s!"input rejected: {reprStr e}")

/-- A failed step of the transition reaches Python with its code and its printed error. -/
instance : ExportError TransitionError where
  code := TransitionError.code
  message := toString

/-- The state after a block operation of a handler of the vectors, the operation given as bytes.

The execution layer gives one fixed answer to a payload. -/
def runOperation {preset : Preset} {fork : Fork} (config : Config) (checks : SignatureChecks)
    (executionValid : Bool) (handler : String) (state : BeaconState preset fork)
    (operation : ByteArray) : Result (BeaconState preset fork) :=
  match handler with
  | "block_header" => do
    toResult none (processBlockHeader state (← decodeInput (BeaconBlock preset fork) operation))
  | "proposer_slashing" => do
    toResult none (processProposerSlashing config checks state
      (← decodeInput ProposerSlashing operation))
  | "attester_slashing" => do
    toResult none (processAttesterSlashing config checks state
      (← decodeInput (AttesterSlashing preset fork) operation))
  | "attestation" => do
    -- Before a block runs, its parent is the latest block header, as the vectors take it.
    toResult none (processAttestation config checks state state.latestBlockHeader.slot
      (← decodeInput (Attestation preset fork) operation))
  | "deposit" =>
    if before : fork < .hegota then do
      toResult none (processDeposit config checks before state (← decodeInput Deposit operation))
    else rejectArgument none s!"no operation deposit at {fork.name}"
  | "sync_aggregate" =>
    if altair : .altair ≤ fork then do
      toResult none (processSyncAggregate config checks state altair
        (← decodeInput (SyncAggregate preset) operation))
    else rejectArgument none s!"no operation sync_aggregate at {fork.name}"
  | "voluntary_exit" | "voluntary_exit_churn" => do
    toResult none (processVoluntaryExit config checks state
      (← decodeInput SignedVoluntaryExit operation))
  | "execution_payload" =>
    if bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam then do
      toResult none (processExecutionPayload config (.constant executionValid) state
        (← decodeInput (BeaconBlockBody preset fork) operation) bellatrix)
    else rejectArgument none s!"no operation execution_payload at {fork.name}"
  | "withdrawals" =>
    if capella : .shapella ≤ fork then
      -- From Gloas the step takes no payload, and the operation bytes are not read.
      if gloas : .glamsterdam ≤ fork then
        toResult none (processWithdrawals state capella fun before => absurd gloas
          (Nat.not_le_of_lt before))
      else do
        let payload ← decodeInput (ExecutionPayload preset fork) operation
        toResult none (processWithdrawals state capella fun _ => payload)
    else rejectArgument none s!"no operation withdrawals at {fork.name}"
  | "bls_to_execution_change" =>
    if .shapella ≤ fork then do
      toResult none (processBlsToExecutionChange config checks state
        (← decodeInput SignedBLSToExecutionChange operation))
    else rejectArgument none s!"no operation bls_to_execution_change at {fork.name}"
  | "deposit_request" =>
    if electra : .pectra ≤ fork then do
      toResult none (processDepositRequest state electra (← decodeInput DepositRequest operation))
    else rejectArgument none s!"no operation deposit_request at {fork.name}"
  | "withdrawal_request" =>
    if electra : .pectra ≤ fork then do
      toResult none (processWithdrawalRequest config state electra
        (← decodeInput WithdrawalRequest operation))
    else rejectArgument none s!"no operation withdrawal_request at {fork.name}"
  | "consolidation_request" =>
    if electra : .pectra ≤ fork then do
      toResult none (processConsolidationRequest config state electra
        (← decodeInput ConsolidationRequest operation))
    else rejectArgument none s!"no operation consolidation_request at {fork.name}"
  | "payload_attestation" =>
    if gloas : .glamsterdam ≤ fork then do
      toResult none (processPayloadAttestation config checks state gloas
        (← decodeInput (PayloadAttestation preset) operation))
    else rejectArgument none s!"no operation payload_attestation at {fork.name}"
  | "execution_payload_bid" =>
    if gloas : .glamsterdam ≤ fork then do
      toResult none (processExecutionPayloadBid config checks state gloas
        (← decodeInput (SignedExecutionPayloadBid preset fork) operation))
    else rejectArgument none s!"no operation execution_payload_bid at {fork.name}"
  | "builder_deposit_request" =>
    if gloas : .glamsterdam ≤ fork then do
      toResult none (processBuilderDepositRequest config checks state gloas
        (← decodeInput BuilderDepositRequest operation))
    else rejectArgument none s!"no operation builder_deposit_request at {fork.name}"
  | "builder_exit_request" =>
    if gloas : .glamsterdam ≤ fork then do
      toResult none (processBuilderExitRequest config state gloas
        (← decodeInput BuilderExitRequest operation))
    else rejectArgument none s!"no operation builder_exit_request at {fork.name}"
  | "parent_execution_payload" =>
    if gloas : .glamsterdam ≤ fork then do
      let block ← decodeInput (BeaconBlock preset fork) operation
      toResult none (processParentExecutionPayload config checks state gloas block.body)
    else rejectArgument none s!"no operation parent_execution_payload at {fork.name}"
  | handler => rejectArgument none s!"no operation {handler}"

/-- The handlers of the operation vectors that run from Gloas.

From Gloas a block must hold no deposit, and the execution payload leaves the block. -/
def gloasOperations : List String :=
  ["block_header", "payload_attestation", "execution_payload_bid", "builder_deposit_request",
    "builder_exit_request", "withdrawals", "proposer_slashing", "attester_slashing",
    "withdrawal_request", "consolidation_request", "voluntary_exit", "voluntary_exit_churn",
    "deposit_request", "parent_execution_payload", "attestation", "sync_aggregate",
    "bls_to_execution_change"]

/-- The preset and the fork that UTF-8 names name, at a fork up to Heze. -/
def transitionPresetAndFork (name fork : ByteArray) : Result (Preset × Fork) := do
  return (← presetOf (← nameOf name), ← forkOf fork)

/-- The state after one step of the epoch transition of a handler of the vectors. -/
def runEpochStep {preset : Preset} {fork : Fork} (config : Config) (handler : String)
    (state : BeaconState preset fork) : Result (BeaconState preset fork) :=
  match handler with
  | "justification_and_finalization" =>
    toResult none (processJustificationAndFinalization state)
  | "inactivity_updates" =>
    if altair : .altair ≤ fork then toResult none (processInactivityUpdates config state altair)
    else rejectArgument none s!"no epoch step inactivity_updates at {fork.name}"
  | "rewards_and_penalties" => toResult none (processRewardsAndPenalties config state)
  | "registry_updates" => toResult none (processRegistryUpdates config state)
  | "slashings" => toResult none (processSlashings state)
  | "eth1_data_reset" =>
    if before : fork < .hegota then toResult none (processEth1DataReset before state)
    else rejectArgument none s!"no epoch step eth1_data_reset at {fork.name}"
  | "effective_balance_updates" => toResult none (processEffectiveBalanceUpdates state)
  | "slashings_reset" => toResult none (processSlashingsReset state)
  | "randao_mixes_reset" => toResult none (processRandaoMixesReset state)
  | "historical_roots_update" =>
    if before : fork < .shapella then toResult none (processHistoricalRootsUpdate state before)
    else rejectArgument none s!"no epoch step historical_roots_update at {fork.name}"
  | "participation_record_updates" =>
    if before : fork < .altair then toResult none (processParticipationRecordUpdates state before)
    else rejectArgument none s!"no epoch step participation_record_updates at {fork.name}"
  | "historical_summaries_update" =>
    if capella : .shapella ≤ fork then
      toResult none (processHistoricalSummariesUpdate state capella)
    else rejectArgument none s!"no epoch step historical_summaries_update at {fork.name}"
  | "participation_flag_updates" =>
    if altair : .altair ≤ fork then pure (processParticipationFlagUpdates state altair)
    else rejectArgument none s!"no epoch step participation_flag_updates at {fork.name}"
  | "sync_committee_updates" =>
    if altair : .altair ≤ fork then toResult none (processSyncCommitteeUpdates state altair)
    else rejectArgument none s!"no epoch step sync_committee_updates at {fork.name}"
  | "ptc_window" =>
    if gloas : .glamsterdam ≤ fork then toResult none (liftAccessor (processPtcWindow state gloas))
    else rejectArgument none s!"no epoch step ptc_window at {fork.name}"
  | "builder_pending_payments" =>
    if gloas : .glamsterdam ≤ fork then
      toResult none (liftAccessor (processBuilderPendingPayments state gloas))
    else rejectArgument none s!"no epoch step builder_pending_payments at {fork.name}"
  | "pending_deposits" | "pending_deposits_churn" =>
    -- The deposits to new keys are checked with BLS, as the vectors expect.
    if electra : .pectra ≤ fork then
      toResult none (processPendingDeposits config .bls state electra)
    else rejectArgument none s!"no epoch step pending_deposits at {fork.name}"
  | "pending_consolidations" =>
    if electra : .pectra ≤ fork then toResult none (processPendingConsolidations state electra)
    else rejectArgument none s!"no epoch step pending_consolidations at {fork.name}"
  | "proposer_lookahead" =>
    if fulu : .fusaka ≤ fork then
      toResult none (liftAccessor (processProposerLookahead state fulu))
    else rejectArgument none s!"no epoch step proposer_lookahead at {fork.name}"
  | handler => rejectArgument none s!"no epoch step {handler}"

/-- The state after a block operation of a handler of the vectors, as SSZ bytes. -/
def processOperationOf
    (args : String × String × String × ByteArray × ByteArray × Option PyValue × Bool × Bool) :
    Result ByteArray := do
  let (name, fork, handler, pre, operation, replacements, verify, executionValid) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  if .glamsterdam ≤ fork ∧ handler ∉ gloasOperations then
    rejectArgument none s!"no operation {handler} at {fork.name}"
  let state ← decodeInput (BeaconState preset fork) pre
  let after ← runOperation config checks executionValid handler state operation
  toResult none ((SszType.serialize after).mapError fun e =>
    UnreadArgument.mk s!"state rejected: {reprStr e}")

/-- The state after a block operation of a handler of the vectors, as SSZ bytes.

The preset, the configuration and the fork are named by `str`, and the handler too.

The signature checks run unless the verify flag is false.

The last argument is the answer of the execution layer to a payload. -/
@[export eth_consensus_process_operation]
def processOperationExport (args : PyValue) : Result PyValue := pyExport processOperationOf args

/-- The state after one step of the epoch transition of a handler of the vectors, as SSZ bytes. -/
def processEpochOf
    (args : String × String × String × ByteArray × Option PyValue) :
    Result ByteArray := do
  let (name, fork, handler, pre, replacements) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let state ← decodeInput (BeaconState preset fork) pre
  let after ← runEpochStep config handler state
  toResult none ((SszType.serialize after).mapError fun e =>
    UnreadArgument.mk s!"state rejected: {reprStr e}")

/-- The state after one step of the epoch transition of a handler of the vectors, as SSZ bytes.

The preset, the configuration and the fork are named by `str`, and the handler too.

The signature of a pending deposit to a new key is always checked. -/
@[export eth_consensus_process_epoch]
def processEpochExport (args : PyValue) : Result PyValue := pyExport processEpochOf args

/-- The state some slots later, as SSZ bytes. -/
def processSlotsOf
    (args : String × String × ByteArray × Option PyValue × UInt64) :
    Result ByteArray := do
  let (name, fork, pre, replacements, slots) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let state ← decodeInput (BeaconState preset fork) pre
  let target ← toResult none (liftAccessor (liftArith (Uint64.addChecked state.slot slots)))
  let after ← toResult none (processSlots config .bls state target)
  toResult none ((SszType.serialize after).mapError fun e =>
    UnreadArgument.mk s!"state rejected: {reprStr e}")

/-- The state some slots later, as SSZ bytes.

The preset, the configuration and the fork are named by `str`.

From Electra the pending deposits check the signatures of new keys with BLS, as the vectors expect.

A target slot that reaches `2^64` is an error. -/
@[export eth_consensus_process_slots]
def processSlotsExport (args : PyValue) : Result PyValue := pyExport processSlotsOf args

/-- The state after a signed block, as SSZ bytes, with the signature and the state root checked. -/
def stateTransitionOf
    (args : String × String × ByteArray × ByteArray × Option PyValue × Bool) :
    Result ByteArray := do
  let (name, fork, pre, block, replacements, verify) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let state ← decodeInput (BeaconState preset fork) pre
  let signed ← decodeInput (SignedBeaconBlock preset fork) block
  let after ← toResult none (stateTransition config checks (.constant true) state signed)
  toResult none ((SszType.serialize after).mapError fun e =>
    UnreadArgument.mk s!"state rejected: {reprStr e}")

/-- The state after a signed block, as SSZ bytes, with the signature and the state root checked.

The preset, the configuration and the fork are named by `str`.

The signature checks run unless the last argument is false.

The execution layer accepts every payload, as in the vectors, which fix no answer for blocks. -/
@[export eth_consensus_state_transition]
def stateTransitionExport (args : PyValue) : Result PyValue := pyExport stateTransitionOf args

/-- The consensus fork before a fork, from Altair to Heze. -/
def forkBefore : Fork → Result Fork
  | .altair => pure .phase0
  | .bellatrix => pure .altair
  | .shapella => pure .bellatrix
  | .dencun => pure .shapella
  | .pectra => pure .dencun
  | .fusaka => pure .pectra
  | .glamsterdam => pure .fusaka
  | .hegota => pure .glamsterdam
  | fork => rejectArgument none s!"no upgrade to {fork.name}"

/-- The state that the upgrade to a fork makes of a state of the fork before, as SSZ bytes. -/
def upgradeStateOf
    (args : String × String × ByteArray × Option PyValue × Bool) :
    Result ByteArray := do
  let (name, fork, pre, replacements, verify) := args
  let preset ← presetOf name
  let previous ← forkBefore (← forkOf fork.toUTF8)
  let config ← configWithValue name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let state ← decodeInput (BeaconState preset previous) pre
  let post ← toResult none (upgradeNext config checks ⟨previous, state⟩)
  toResult none ((SszType.serialize post.val.state).mapError fun e =>
    UnreadArgument.mk s!"state rejected: {reprStr e}")

/-- The state that the upgrade to a fork makes of a state of the fork before, as SSZ bytes.

The preset, the configuration and the target fork are named by `str`.

The upgrades are those from Altair to Heze, each from the consensus fork before it.

The signature checks of the deposits at the upgrade to Gloas run unless the last argument is false.
-/
@[export eth_consensus_upgrade_state]
def upgradeStateExport (args : PyValue) : Result PyValue := pyExport upgradeStateOf args

/-- The state after a signed block of a fork, from a state of that fork or an earlier one. -/
def stateTransitionAcrossOf
    (args : String × String × ByteArray × String × ByteArray × Option PyValue × Bool) :
    Result ByteArray := do
  let (name, fork, pre, blockFork, block, replacements, verify) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let (_, blockFork) ← transitionPresetAndFork name.toUTF8 blockFork.toUTF8
  let config ← configWithValue name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let state ← decodeInput (BeaconState preset fork) pre
  let signed ← decodeInput (SignedBeaconBlock preset blockFork) block
  let after ← toResult none
    (stateTransitionAcross config checks (.constant true) ⟨fork, state⟩ signed)
  toResult none ((SszType.serialize after).mapError fun e =>
    UnreadArgument.mk s!"state rejected: {reprStr e}")

/-- The state after a signed block of a fork, from a state of that fork or an earlier one.

The state advances to the slot of the block and upgrades at each fork epoch on the way.

The fork epochs are those of the configuration, with its replacements.

The block must be of the fork that the state then has.

The preset, the configuration and both forks are named by `str`, each fork up to Heze.

The signature checks run unless the last argument is false.

The execution layer accepts every payload, as in the vectors, which fix no answer for blocks. -/
@[export eth_consensus_state_transition_across]
def stateTransitionAcrossExport (args : PyValue) : Result PyValue :=
  pyExport stateTransitionAcrossOf args

/-- The state after signed blocks in order, as SSZ bytes, with each state root checked. -/
def stateTransitionsOf
    (args : String × String × ByteArray × Array ByteArray × Option PyValue × Bool) :
    Result ByteArray := do
  let (name, fork, pre, blocks, replacements, verify) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let mut state ← decodeInput (BeaconState preset fork) pre
  for block in blocks do
    let signed ← decodeInput (SignedBeaconBlock preset fork) block
    state ← toResult none (stateTransition config checks (.constant true) state signed)
  toResult none ((SszType.serialize state).mapError fun e =>
    UnreadArgument.mk s!"state rejected: {reprStr e}")

/-- The state after signed blocks in order, as SSZ bytes, with each state root checked.

The preset, the configuration and the fork are named by `str`, and every block is of that fork.

The first block that fails stops the call with its error.

The signature checks run unless the last argument is false.

The execution layer accepts every payload, as in the vectors, which fix no answer for blocks. -/
@[export eth_consensus_state_transitions]
def stateTransitionsExport (args : PyValue) : Result PyValue := pyExport stateTransitionsOf args

/-- The state after signed blocks in order, as SSZ bytes, across the fork epochs on the way. -/
def stateTransitionsAcrossOf
    (args : String × String × ByteArray × Array String × Array ByteArray × Option PyValue × Bool) :
    Result ByteArray := do
  let (name, fork, pre, blockForks, blocks, replacements, verify) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  if blockForks.size != blocks.size then
    rejectArgument none s!"{blockForks.size} block forks for {blocks.size} blocks"
  let mut forked : ForkedBeaconState preset := ⟨fork, ← decodeInput (BeaconState preset fork) pre⟩
  for (blockFork, block) in blockForks.zip blocks do
    let (_, blockFork) ← transitionPresetAndFork name.toUTF8 blockFork.toUTF8
    let signed ← decodeInput (SignedBeaconBlock preset blockFork) block
    forked := ⟨blockFork,
      ← toResult none (stateTransitionAcross config checks (.constant true) forked signed)⟩
  toResult none ((SszType.serialize forked.state).mapError fun e =>
    UnreadArgument.mk s!"state rejected: {reprStr e}")

/-- The state after signed blocks in order, as SSZ bytes, across the fork epochs on the way.

The state may be of the fork of the first block or of an earlier one.

Before each block, the state advances to the slot of the block and upgrades at each fork epoch.

Each block names its fork, which must be the fork that the state then has.

The preset, the configuration and every fork are named by `str`, each fork up to Heze.

The first block that fails stops the call with its error, as does a count of forks that differs.

The signature checks run unless the last argument is false.

The execution layer accepts every payload, as in the vectors, which fix no answer for blocks. -/
@[export eth_consensus_state_transitions_across]
def stateTransitionsAcrossExport (args : PyValue) : Result PyValue :=
  pyExport stateTransitionsAcrossOf args

end EthLib.Consensus.Exports
