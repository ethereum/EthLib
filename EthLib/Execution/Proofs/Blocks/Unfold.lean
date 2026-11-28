module

public import EthLib.Execution.Blocks.Transition
public import EthLib.Execution.Proofs.Transactions.Unfold

/-!
# Proofs: the steps of a block body with no observer

The system calls, the transactions, the requests and the body of a block take an observer.

With no observer, in the monad of errors, each one unfolds to a body with no lifts.

Proofs that read that body rewrite with these equations.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState TransactionState stateRoot)
open EthLib.Execution.Transactions
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- A system call with no observer unfolds to the message of a transaction from the system. -/
theorem systemCall_unfold {fork : Fork} (env : BlockEnvironment fork) (block : BlockState)
    (target : Address) (data : ByteArray) :
    systemCall env block target data = (do
      let message := systemMessage env target data
      let state := TransactionState.ofBlock block
      let substate := systemSubstate env target
      let out ← if fork ≥ .glamsterdam then
          processMessageCall (Meter := StateGasMeter) env.chainId.toNat message state substate
        else processMessageCall (Meter := Nat) env.chainId.toNat message state substate
      return ⟨out.state, out.output, out.error⟩) :=
  rfl

/-- The observer that observes nothing has the runs of a step observer that does nothing. -/
theorem BodyObserver.none_eq_ofSteps {fork : Fork} :
    (BodyObserver.none : BodyObserver (Except EvmError) (Except BlockError) fork) =
      .ofSteps (fun _ _ => pure ()) (fun run => run.mapError .aborted) (fun _ _ _ _ => pure ()) :=
  rfl

/-- A checked system call with no observer unfolds to its checks around the system call. -/
theorem checkedSystemCall_unfold {fork : Fork} (env : BlockEnvironment fork)
    (block : BlockState) (target : Address) (data : ByteArray) :
    checkedSystemCall env block target data = (do
      let code ← (codeAt block target).mapError .aborted
      if code.size = 0 then throw (.systemContractEmpty target)
      let out ← (systemCall env block target data).mapError .aborted
      match out.error with
      | some error => throw (.systemCallFailed target error)
      | none => return out) := by
  rw [checkedSystemCall, checkedSystemCallWith]
  simp only [liftExcept_except]
  rfl

/-- The system calls at the start of a block, with no observer, unfold to the two calls. -/
theorem startSystemCalls_unfold {fork : Fork} (env : BlockEnvironment fork) (parentHash : Hash32)
    (body : BodyState) :
    startSystemCalls env parentHash body = (do
      let body ← if h : BEACON_ROOTS_CONTRACT.since ≤ fork then do
          let out ← systemCall env body.block BEACON_ROOTS_CONTRACT.address
            ⟨(env.parentBeaconBlockRoot h).toArray⟩
          (body.join out.state).mapError .state
        else pure body
      if HISTORY_STORAGE_CONTRACT.since ≤ fork then do
        let out ← systemCall env body.block HISTORY_STORAGE_CONTRACT.address ⟨parentHash.toArray⟩
        (body.join out.state).mapError .state
      else pure body) := by
  rw [startSystemCalls, startSystemCallsWith]
  simp only [liftExcept_except]
  rfl

/-- A call to a request contract with no observer unfolds to the checked call and its requests. -/
theorem readRequest_unfold {fork : Fork} (env : BlockEnvironment fork)
    (state : BodyState × List ByteArray) (contract : UInt8 × Address) :
    readRequest env state contract = (do
      let out ← checkedSystemCall env state.1.block contract.2 .empty
      let body ← (state.1.join out.state).mapError .state
      return (body, state.2 ++ requestList contract.1 out.output)) := by
  rw [readRequest, readRequestWith]
  simp only [liftExcept_except]
  rfl

/-- The calls to the request contracts with no observer unfold to one call per contract. -/
theorem readRequests_unfold {fork : Fork} (env : BlockEnvironment fork) (body : BodyState) :
    readRequests env body = (requestContracts fork).foldlM (readRequest env) (body, []) :=
  rfl

/-- The requests of a block with no observer unfold to the deposits, then the calls. -/
theorem blockRequests_unfold {fork : Fork} (depositContract : Address)
    (env : BlockEnvironment fork) (body : BodyState) (logs : List Log) :
    blockRequests depositContract env body logs = (do
      if .pectra ≤ fork then
        let deposits ← (depositRequests depositContract logs).mapError .deposit
        let (body, requests) ← readRequests env body
        return (body, requestList DEPOSIT_REQUEST_TYPE deposits ++ requests)
      else return (body, [])) := by
  rw [blockRequests, blockRequestsWith]
  simp only [liftExcept_except]
  rfl

/-- A transaction of a body with no observer unfolds to its checks, its run and its receipt. -/
theorem applyTransaction_unfold {fork : Fork} (env : BlockEnvironment fork) (index : Nat)
    (before : BodyOutput fork) (tx : Transaction) (overrides : BodyOverrides) :
    applyTransaction env index before tx overrides = (do
      let included ← (checkInclusion env.chainId env before.gas
        (.ofBlock before.block) tx (overrides.senders index) overrides.lifted).mapError
        (.invalidTransaction index)
      let out ← (processTransaction env before.block included tx overrides.precompiles
        overrides.lifted).mapError .aborted
      let body ← ((before.body.beginIndex (index + 1)).join out.state).mapError .state
      let gas := before.gas.add out.blockGas
      let cumulativeGasUsed := before.cumulativeGasUsed + out.gasUsed
      let outcome : Outcome fork ← if h : .byzantium ≤ fork then pure (.status h out.error.isNone)
        else .postState (Nat.lt_of_not_le h) <$>
          (stateRoot keccak256 body.block.applyChanges).mapError .trie
      return { body, gas, cumulativeGasUsed
               receipts := before.receipts ++
                 [(tx.type, makeReceipt outcome cumulativeGasUsed out.logs.toList)]
               logs := before.logs ++ out.logs.toList
               results := before.results ++
                 [⟨out.messageOutput, out.gasBeforeRefund, out.error,
                   out.simulatedLogs.toList⟩] }) := by
  rw [applyTransaction, applyTransactionWith]
  simp only [liftExcept_except]
  rfl

/-- The transactions of a body with no observer unfold to one transaction after another. -/
theorem applyTransactions_unfold {fork : Fork} (env : BlockEnvironment fork) (body : BodyState)
    (transactions : List Transaction) (overrides : BodyOverrides) :
    applyTransactions env body transactions overrides =
      transactions.zipIdx.foldlM
        (fun before (tx, index) => applyTransaction env index before tx overrides)
        ⟨body, .zero, 0, [], [], []⟩ :=
  rfl

/-- The body of a block with no observer unfolds to its steps in the monad of errors. -/
theorem applyBody_unfold {fork : Fork} (config : ChainConfig) (env : BlockEnvironment fork)
    (block : Block fork Transaction) (start : BlockState) (overrides : BodyOverrides) :
    applyBody config env block start overrides = (do
      let state ← daoTransfer config fork block.header.number start
      let body ← (startSystemCalls env block.header.parentHash (.init state)).mapError .aborted
      let output ← applyTransactions env body block.transactions overrides
      let body := output.body.beginIndex (block.transactions.length + 1)
      let body ← if h : .shapella ≤ fork then do
          let tx ← (withdrawalState fork body.block (block.withdrawals h)).mapError .state
          (body.join tx).mapError .state
        else pure body
      let (body, requests) ← blockRequests config.depositContractAddress env body output.logs
      let ommers := block.ommers.map fun ommer => (ommer.2.coinbase, ommer.2.number)
      let state ← onBlock body.block fun tx =>
        payRewards fork tx block.header.coinbase block.header.number ommers
      let accessListHash ← accessListHashOf fork body block.header.gasLimit overrides.itemCap
      return { output with body := { body with block := state }, requests, accessListHash }) := by
  rw [applyBody, applyBodyWith]
  simp only [liftExcept_except]
  rfl

end EthLib.Execution.Blocks
