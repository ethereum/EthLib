module

public import EthLib.Consensus.Exports.Ssz
public import EthLib.Consensus.PayloadTimeliness
public import EthLib.Consensus.Proposers
public import EthLib.Consensus.Transition.Block
public import EthLib.Consensus.Transition.BuilderPayments
public import EthLib.Consensus.Transition.BuilderRequests
public import EthLib.Consensus.Transition.EpochJustification
public import EthLib.Consensus.Transition.EpochRewards
public import EthLib.Consensus.Transition.EpochUpdates
public import EthLib.Consensus.Transition.Operations
public import EthLib.Consensus.Transition.Payload
public import EthLib.Consensus.Transition.Upgrade
public import EthLib.Consensus.Transition.Withdrawals

/-!
# `Exports.Transition`

C-ABI exports of the steps of the beacon state transition, for the consensus test vectors.

One export runs a block operation on a state, and another one step of the epoch transition.

Both take and return states as SSZ bytes, and accept forks up to Gloas.

At Gloas, only the steps whose Gloas rule EthLib holds run.

A third export upgrades a state to Gloas or to Heze.

The configuration of a name holds, with the replacements that a JSON object gives.

It checks the BLS signatures, or accepts every signature for the vectors with placeholder ones.

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

/-- The state after a block operation of a handler of the vectors, the operation given as bytes. -/
def runOperation {preset : Preset} {fork : Fork} (config : Config) (checks : SignatureChecks)
    (handler : String) (state : BeaconState preset fork) (operation : ByteArray) :
    Result (BeaconState preset fork) :=
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
  | "voluntary_exit" => do
    runTransition (processVoluntaryExit config checks state
      (← decodeInput SignedVoluntaryExit operation))
  | "withdrawals" =>
    if capella : .shapella ≤ fork then do
      runTransition (processWithdrawals state capella
        (← decodeInput (ExecutionPayload preset fork) operation))
    else throw (0, s!"no operation withdrawals at {fork.name}")
  | "bls_to_execution_change" =>
    if .shapella ≤ fork then do
      runTransition (processBlsToExecutionChange config checks state
        (← decodeInput SignedBLSToExecutionChange operation))
    else throw (0, s!"no operation bls_to_execution_change at {fork.name}")
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
    "builder_exit_request"]

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
  | "ptc_window" =>
    if gloas : .glamsterdam ≤ fork then runTransition (liftAccessor (processPtcWindow state gloas))
    else throw (0, s!"no epoch step ptc_window at {fork.name}")
  | "builder_pending_payments" =>
    if gloas : .glamsterdam ≤ fork then
      runTransition (liftAccessor (processBuilderPendingPayments state gloas))
    else throw (0, s!"no epoch step builder_pending_payments at {fork.name}")
  | "proposer_lookahead" =>
    if fulu : .fusaka ≤ fork then
      runTransition (liftAccessor (processProposerLookahead state fulu))
    else throw (0, s!"no epoch step proposer_lookahead at {fork.name}")
  | handler => throw (0, s!"no epoch step {handler}")

/-- The state after a block operation of a handler of the vectors, as SSZ bytes.

The preset, the configuration and the fork are named in UTF-8, and the handler too.

The signature checks run unless the last argument is false. -/
@[export eth_consensus_process_operation]
def processOperationExport (name fork handler pre operation replacements : ByteArray)
    (verify : Bool) : Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let config ← configWith name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let handler ← nameOf handler
  -- At Gloas only the operations whose Gloas rule EthLib holds run.
  if .glamsterdam ≤ fork ∧ handler ∉ gloasOperations then
    throw (0, s!"operation {handler} not yet specified at {fork.name}")
  let state ← decodeInput (BeaconState preset fork) pre
  let after ← runOperation config checks handler state operation
  (SszType.serialize after).mapError fun e => (0, s!"state rejected: {reprStr e}")

/-- The state after one step of the epoch transition of a handler of the vectors, as SSZ bytes.

The preset, the configuration and the fork are named in UTF-8, and the handler too. -/
@[export eth_consensus_process_epoch]
def processEpochExport (name fork handler pre replacements : ByteArray) : Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let config ← configWith name replacements
  let state ← decodeInput (BeaconState preset fork) pre
  let after ← runEpochStep config (← nameOf handler) state
  (SszType.serialize after).mapError fun e => (0, s!"state rejected: {reprStr e}")

/-- The state that the upgrade to a fork makes of a state of the fork before, as SSZ bytes.

The preset, the configuration and the target fork are named in UTF-8.

The upgrades are the ones to Gloas and to Heze.

The signature checks of the deposits at the upgrade to Gloas run unless the last argument is false.
-/
@[export eth_consensus_upgrade_state]
def upgradeStateExport (name fork pre replacements : ByteArray) (verify : Bool) :
    Result ByteArray := do
  let preset ← presetOf (← nameOf name)
  let fork ← forkOf fork
  let config ← configWith name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  match fork with
  | .glamsterdam =>
    let state ← decodeInput (BeaconState preset .fusaka) pre
    let post ← runTransition (upgradeToGloas config checks state)
    (SszType.serialize post).mapError fun e => (0, s!"state rejected: {reprStr e}")
  | .hegota =>
    let state ← decodeInput (BeaconState preset .glamsterdam) pre
    let post ← runTransition (upgradeToHeze config state)
    (SszType.serialize post).mapError fun e => (0, s!"state rejected: {reprStr e}")
  | fork => throw (0, s!"no upgrade to {fork.name}")

end EthLib.Consensus.Exports
