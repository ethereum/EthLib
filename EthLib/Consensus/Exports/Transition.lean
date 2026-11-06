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

They take and return states as SSZ bytes, and accept forks up to Gloas.

At Gloas, only the steps whose Gloas rule EthLib holds run.

Another export upgrades a state to the next consensus fork, from Altair to Heze.

The last runs a signed block from a state of an earlier fork, across the fork epochs between.

The configuration of a name holds, with the replacements that a JSON object gives.

It checks the BLS signatures, or accepts every signature for the vectors with placeholder ones.

The vectors fix the answer of the execution layer to a payload, and so does the operation export.

An input that does not decode, or an unknown name, has code 0.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz
open EthLib.Exports (Result)

/-- The value of a type that SSZ bytes encode. -/
def decodeInput (α : Type) [SszType α] (data : ByteArray) : Result α :=
  (SszType.deserialize α data).mapError fun e => (0, s!"input rejected: {reprStr e}")

/-- The result of a step of the transition, with the code and the text of its error. -/
def runTransition {α : Type} (result : Except TransitionError α) : Result α :=
  result.mapError fun e => (e.code, reprStr e)

/-- The state after a block operation of a handler of the vectors, the operation given as bytes.

The execution layer gives one fixed answer to a payload. -/
def runOperation {preset : Preset} {fork : Fork} (config : Config) (checks : SignatureChecks)
    (executionValid : Bool) (handler : String) (state : BeaconState preset fork)
    (operation : ByteArray) : Result (BeaconState preset fork) :=
  match handler with
  | "block_header" => do
    runTransition (processBlockHeader state (← decodeInput (BeaconBlock preset fork) operation))
  | "proposer_slashing" => do
    runTransition (processProposerSlashing config checks state
      (← decodeInput ProposerSlashing operation))
  | "attester_slashing" => do
    runTransition (processAttesterSlashing config checks state
      (← decodeInput (AttesterSlashing preset fork) operation))
  | "attestation" => do
    runTransition (processAttestation config checks state
      (← decodeInput (Attestation preset fork) operation))
  | "deposit" =>
    if before : fork < .hegota then do
      runTransition (processDeposit config checks before state (← decodeInput Deposit operation))
    else throw (0, s!"no operation deposit at {fork.name}")
  | "sync_aggregate" =>
    if altair : .altair ≤ fork then do
      runTransition (processSyncAggregate config checks state altair
        (← decodeInput (SyncAggregate preset) operation))
    else throw (0, s!"no operation sync_aggregate at {fork.name}")
  | "voluntary_exit" => do
    runTransition (processVoluntaryExit config checks state
      (← decodeInput SignedVoluntaryExit operation))
  | "execution_payload" =>
    if bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam then do
      runTransition (processExecutionPayload config (.constant executionValid) state
        (← decodeInput (BeaconBlockBody preset fork) operation) bellatrix)
    else throw (0, s!"no operation execution_payload at {fork.name}")
  | "withdrawals" =>
    if capella : .shapella ≤ fork then
      -- From Gloas the step takes no payload, and the operation bytes are not read.
      if gloas : .glamsterdam ≤ fork then
        runTransition (processWithdrawals state capella fun before => absurd gloas
          (Nat.not_le_of_lt before))
      else do
        let payload ← decodeInput (ExecutionPayload preset fork) operation
        runTransition (processWithdrawals state capella fun _ => payload)
    else throw (0, s!"no operation withdrawals at {fork.name}")
  | "bls_to_execution_change" =>
    if .shapella ≤ fork then do
      runTransition (processBlsToExecutionChange config checks state
        (← decodeInput SignedBLSToExecutionChange operation))
    else throw (0, s!"no operation bls_to_execution_change at {fork.name}")
  | "deposit_request" =>
    if electra : .pectra ≤ fork then do
      runTransition (processDepositRequest state electra (← decodeInput DepositRequest operation))
    else throw (0, s!"no operation deposit_request at {fork.name}")
  | "withdrawal_request" =>
    if electra : .pectra ≤ fork then do
      runTransition (processWithdrawalRequest config state electra
        (← decodeInput WithdrawalRequest operation))
    else throw (0, s!"no operation withdrawal_request at {fork.name}")
  | "consolidation_request" =>
    if electra : .pectra ≤ fork then do
      runTransition (processConsolidationRequest config state electra
        (← decodeInput ConsolidationRequest operation))
    else throw (0, s!"no operation consolidation_request at {fork.name}")
  | "payload_attestation" =>
    if gloas : .glamsterdam ≤ fork then do
      runTransition (processPayloadAttestation config checks state gloas
        (← decodeInput (PayloadAttestation preset) operation))
    else throw (0, s!"no operation payload_attestation at {fork.name}")
  | "execution_payload_bid" =>
    if gloas : .glamsterdam ≤ fork then do
      runTransition (processExecutionPayloadBid config checks state gloas
        (← decodeInput (SignedExecutionPayloadBid preset fork) operation))
    else throw (0, s!"no operation execution_payload_bid at {fork.name}")
  | "builder_deposit_request" =>
    if gloas : .glamsterdam ≤ fork then do
      runTransition (processBuilderDepositRequest config checks state gloas
        (← decodeInput BuilderDepositRequest operation))
    else throw (0, s!"no operation builder_deposit_request at {fork.name}")
  | "builder_exit_request" =>
    if gloas : .glamsterdam ≤ fork then do
      runTransition (processBuilderExitRequest config state gloas
        (← decodeInput BuilderExitRequest operation))
    else throw (0, s!"no operation builder_exit_request at {fork.name}")
  | handler => throw (0, s!"no operation {handler}")

/-- The operations whose Gloas rule EthLib holds. -/
def gloasOperations : List String :=
  ["payload_attestation", "execution_payload_bid", "builder_deposit_request",
    "builder_exit_request", "withdrawals", "proposer_slashing", "attester_slashing",
    "withdrawal_request", "consolidation_request"]

/-- The preset and the fork that UTF-8 names name, at a fork up to Gloas. -/
def transitionPresetAndFork (name fork : ByteArray) : Result (Preset × Fork) := do
  let preset ← presetOf (← nameOf name)
  let fork ← forkOf fork
  if .hegota ≤ fork then throw (0, s!"fork {fork.name} not yet specified")
  return (preset, fork)

/-- The state after one step of the epoch transition of a handler of the vectors. -/
def runEpochStep {preset : Preset} {fork : Fork} (config : Config) (handler : String)
    (state : BeaconState preset fork) : Result (BeaconState preset fork) :=
  match handler with
  | "justification_and_finalization" =>
    runTransition (processJustificationAndFinalization state)
  | "inactivity_updates" =>
    if altair : .altair ≤ fork then runTransition (processInactivityUpdates config state altair)
    else throw (0, s!"no epoch step inactivity_updates at {fork.name}")
  | "rewards_and_penalties" => runTransition (processRewardsAndPenalties config state)
  | "registry_updates" => runTransition (processRegistryUpdates config state)
  | "slashings" => runTransition (processSlashings state)
  | "eth1_data_reset" =>
    if before : fork < .hegota then runTransition (processEth1DataReset before state)
    else throw (0, s!"no epoch step eth1_data_reset at {fork.name}")
  | "effective_balance_updates" => runTransition (processEffectiveBalanceUpdates state)
  | "slashings_reset" => runTransition (processSlashingsReset state)
  | "randao_mixes_reset" => runTransition (processRandaoMixesReset state)
  | "historical_roots_update" => runTransition (processHistoricalRootsUpdate state)
  | "participation_record_updates" => runTransition (processParticipationRecordUpdates state)
  | "historical_summaries_update" =>
    if capella : .shapella ≤ fork then
      runTransition (processHistoricalSummariesUpdate state capella)
    else throw (0, s!"no epoch step historical_summaries_update at {fork.name}")
  | "participation_flag_updates" =>
    if altair : .altair ≤ fork then pure (processParticipationFlagUpdates state altair)
    else throw (0, s!"no epoch step participation_flag_updates at {fork.name}")
  | "sync_committee_updates" =>
    if altair : .altair ≤ fork then runTransition (processSyncCommitteeUpdates state altair)
    else throw (0, s!"no epoch step sync_committee_updates at {fork.name}")
  | "ptc_window" =>
    if gloas : .glamsterdam ≤ fork then runTransition (liftAccessor (processPtcWindow state gloas))
    else throw (0, s!"no epoch step ptc_window at {fork.name}")
  | "builder_pending_payments" =>
    if gloas : .glamsterdam ≤ fork then
      runTransition (liftAccessor (processBuilderPendingPayments state gloas))
    else throw (0, s!"no epoch step builder_pending_payments at {fork.name}")
  | "pending_deposits" =>
    -- The deposits to new keys are checked with BLS, as the vectors expect.
    if electra : .pectra ≤ fork then
      runTransition (processPendingDeposits config .bls state electra)
    else throw (0, s!"no epoch step pending_deposits at {fork.name}")
  | "pending_consolidations" =>
    if electra : .pectra ≤ fork then runTransition (processPendingConsolidations state electra)
    else throw (0, s!"no epoch step pending_consolidations at {fork.name}")
  | "proposer_lookahead" =>
    if fulu : .fusaka ≤ fork then
      runTransition (liftAccessor (processProposerLookahead state fulu))
    else throw (0, s!"no epoch step proposer_lookahead at {fork.name}")
  | handler => throw (0, s!"no epoch step {handler}")

/-- The state after a block operation of a handler of the vectors, as SSZ bytes.

The preset, the configuration and the fork are named in UTF-8, and the handler too.

The signature checks run unless the verify flag is false.

The last argument is the answer of the execution layer to a payload. -/
@[export eth_consensus_process_operation]
def processOperationExport (name fork handler pre operation replacements : ByteArray)
    (verify executionValid : Bool) : Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let config ← configWith name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let handler ← nameOf handler
  -- At Gloas only the operations whose Gloas rule EthLib holds run.
  if .glamsterdam ≤ fork ∧ handler ∉ gloasOperations then
    throw (0, s!"operation {handler} not yet specified at {fork.name}")
  let state ← decodeInput (BeaconState preset fork) pre
  let after ← runOperation config checks executionValid handler state operation
  (SszType.serialize after).mapError fun e => (0, s!"state rejected: {reprStr e}")

/-- The state after one step of the epoch transition of a handler of the vectors, as SSZ bytes.

The preset, the configuration and the fork are named in UTF-8, and the handler too.

The signature of a pending deposit to a new key is always checked. -/
@[export eth_consensus_process_epoch]
def processEpochExport (name fork handler pre replacements : ByteArray) : Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let config ← configWith name replacements
  let state ← decodeInput (BeaconState preset fork) pre
  let after ← runEpochStep config (← nameOf handler) state
  (SszType.serialize after).mapError fun e => (0, s!"state rejected: {reprStr e}")

/-- The state some slots later, as SSZ bytes.

The preset, the configuration and the fork are named in UTF-8.

A target slot that reaches `2^64` is an error. -/
@[export eth_consensus_process_slots]
def processSlotsExport (name fork pre replacements : ByteArray) (slots : UInt64) :
    Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let config ← configWith name replacements
  let state ← decodeInput (BeaconState preset fork) pre
  let target ← runTransition (liftAccessor (liftArith (Uint64.addChecked state.slot slots)))
  let after ← runTransition (processSlots config state target)
  (SszType.serialize after).mapError fun e => (0, s!"state rejected: {reprStr e}")

/-- The state after a signed block, as SSZ bytes, with the signature and the state root checked.

The preset, the configuration and the fork are named in UTF-8.

The signature checks run unless the last argument is false.

The execution layer accepts every payload, as in the vectors, which fix no answer for blocks. -/
@[export eth_consensus_state_transition]
def stateTransitionExport (name fork pre block replacements : ByteArray) (verify : Bool) :
    Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let config ← configWith name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let state ← decodeInput (BeaconState preset fork) pre
  let signed ← decodeInput (SignedBeaconBlock preset fork) block
  let after ← runTransition (stateTransition config checks (.constant true) state signed)
  (SszType.serialize after).mapError fun e => (0, s!"state rejected: {reprStr e}")

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
  | fork => throw (0, s!"no upgrade to {fork.name}")

/-- The state that the upgrade to a fork makes of a state of the fork before, as SSZ bytes.

The preset, the configuration and the target fork are named in UTF-8.

The upgrades are those from Altair to Heze, each from the consensus fork before it.

The signature checks of the deposits at the upgrade to Gloas run unless the last argument is false.
-/
@[export eth_consensus_upgrade_state]
def upgradeStateExport (name fork pre replacements : ByteArray) (verify : Bool) :
    Result ByteArray := do
  let preset ← presetOf (← nameOf name)
  let previous ← forkBefore (← forkOf fork)
  let config ← configWith name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let state ← decodeInput (BeaconState preset previous) pre
  let post ← runTransition (upgradeNext config checks ⟨previous, state⟩)
  (SszType.serialize post.val.state).mapError fun e => (0, s!"state rejected: {reprStr e}")

/-- The state after a signed block of a fork, from a state of that fork or an earlier one.

The state advances to the slot of the block and upgrades at each fork epoch on the way.

The fork epochs are those of the configuration, with its replacements.

The block must be of the fork that the state then has.

The preset, the configuration and both forks are named in UTF-8, each fork up to Gloas.

The signature checks run unless the last argument is false.

The execution layer accepts every payload, as in the vectors, which fix no answer for blocks. -/
@[export eth_consensus_state_transition_across]
def stateTransitionAcrossExport (name fork pre blockFork block replacements : ByteArray)
    (verify : Bool) : Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let (_, blockFork) ← transitionPresetAndFork name blockFork
  let config ← configWith name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let state ← decodeInput (BeaconState preset fork) pre
  let signed ← decodeInput (SignedBeaconBlock preset blockFork) block
  let after ← runTransition
    (stateTransitionAcross config checks (.constant true) ⟨fork, state⟩ signed)
  (SszType.serialize after).mapError fun e => (0, s!"state rejected: {reprStr e}")

end EthLib.Consensus.Exports
