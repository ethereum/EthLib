module

public import EthLib.Execution.Evm.Call.ContractAddress
public import EthLib.Execution.Evm.Call.MessageCall
public import EthLib.Execution.Transactions.Authorization
public import EthLib.Execution.Transactions.Inclusion

/-!
# `Transactions.Process`

The run of a transaction that may enter its block: its message, then the settlement of its gas.

The sender first buys the gas, and its nonce grows by one.

The message gets the gas limit minus the intrinsic gas.

From Glamsterdam, that gas splits into execution gas and a reservoir of state gas, by EIP-8037.

A call runs the code of its recipient, and a creation runs the data as init code.

A creation goes to the address that the sender and its nonce before the transaction give.

It fails at once, with no gas left, when that address has code, a nonce or storage.

From Berlin, the transaction starts with some addresses and storage keys accessed:

- the sender, the recipient or the created address, and the precompiles of the fork;
- each address and storage key of the access list;
- from Shapella, the beneficiary of the block.

From Pectra, the authorizations of a set code transaction apply before its message.

From Pectra, a recipient whose code is a delegation indicator runs the code of its delegate.

The delegate is then accessed, and the message runs no precompile.

From Glamsterdam, the first frame pays some gas before its code runs, in this order:

- each accepted authorization pays what it writes, and that state gas is committed;
- a transfer of ether to an account that is not alive pays the state gas of a new account;
- the access to a delegate pays the price of an account access, cold or warm;
- a creation pays the state gas of a new account when its address had none.

A lack of gas there halts the message before its frame runs.

The authorizations are then undone, all the execution gas is used, and the reservoir comes back.

The nonce and the fee of the sender stay.

A message that fails keeps no log, no refund and no account to delete.

Once the message ends, the sender gets back its gas left and its refund.

From Glamsterdam, the gas left includes the reservoir left.

Then the beneficiary gets its fee.

Then each account that SELFDESTRUCT marked is deleted.

From Glamsterdam, such an account loses its nonce, code and storage, and keeps its balance.

It is deleted only when that leaves it empty, by EIP-8246.

From Spurious Dragon to Paris, each touched account that is empty is deleted too.

Section 6.2 of the Yellow Paper, Shanghai version, defines the run of a transaction.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

The EIPs that change it:

- [EIP-161][eip161], the deletion of touched empty accounts
- [EIP-2929][eip2929], the accessed addresses at the start
- [EIP-2930][eip2930], the access list
- [EIP-3651][eip3651], the beneficiary accessed at the start
- [EIP-7702][eip7702], the authorizations and the delegated recipient
- [EIP-2780][eip2780], the gas that the first frame pays before its code, in Last Call
- [EIP-8037][eip8037], the reservoir of state gas, in Last Call
- [EIP-8246][eip8246], the accounts that SELFDESTRUCT marked keep their balance, in Last Call

The run records what it reads, for the block access list of EIP-7928.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip161]: https://eips.ethereum.org/EIPS/eip-161#specification
[eip2929]: https://eips.ethereum.org/EIPS/eip-2929#specification
[eip2930]: https://eips.ethereum.org/EIPS/eip-2930#specification
[eip3651]: https://eips.ethereum.org/EIPS/eip-3651#specification
[eip7702]: https://eips.ethereum.org/EIPS/eip-7702#behavior
[eip2780]: https://eips.ethereum.org/EIPS/eip-2780#runtime-gas-costs
[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#transaction-level-gas-accounting-reservoir-model
[eip8246]: https://eips.ethereum.org/EIPS/eip-8246#specification
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Blocks (Log)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.GasCosts (NEW_ACCOUNT_STATE_GAS)
open EthLib.Execution.State (BlockState EMPTY_ACCOUNT TransactionState)

/-! ## The start of the message -/

/-- The versioned hashes of the blobs of a transaction, empty unless it carries blobs. -/
def Transaction.blobHashes : Transaction → List Hash32
  | .blob tx => tx.blobVersionedHashes
  | _ => []

/-- The addresses of the precompiles of `fork`. -/
def precompileAddresses (fork : Fork) : List Address :=
  (Precompiles.ADDRESSES.filter (Precompiles.isPrecompile fork)).map
    fun address => toAddressMasked (BitVec.ofNat 256 address)

/-- The addresses that a transaction has accessed when its message starts, at `fork`.

They are the sender, and `target`: the recipient or the created address.

Then come the precompiles and the addresses of the access list.

From Shapella, the beneficiary `coinbase` is one of them.

Before Berlin, no access counts, so the set is empty. -/
def startAccessedAddresses (fork : Fork) (coinbase sender target : Address) (tx : Transaction) :
    Std.ExtTreeSet Address :=
  if fork ≥ .berlin then
    let accessed := ((∅ : Std.ExtTreeSet Address).insert sender).insert target
    let accessed := accessed.insertMany (precompileAddresses fork)
    let accessed := accessed.insertMany (tx.accesses.map (·.account))
    if fork ≥ .shapella then accessed.insert coinbase else accessed
  else ∅

/-- The storage keys that a transaction has accessed when its message starts, at `fork`.

They are the keys of its access list, from Berlin. -/
def startAccessedStorageKeys (fork : Fork) (tx : Transaction) :
    Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32) :=
  if fork ≥ .berlin then
    tx.accesses.foldl
      (fun keys access => keys.insert access.account ((keys.getD access.account ∅).insertMany
        access.slots))
      ∅
  else ∅

/-- The substate of a transaction when its message starts: only the accesses of its start. -/
def startSubstate (fork : Fork) (coinbase sender target : Address) (tx : Transaction) :
    Substate :=
  { Substate.empty with
    accessedAddresses := startAccessedAddresses fork coinbase sender target tx
    accessedStorageKeys := startAccessedStorageKeys fork tx }

/-- The address that a transaction calls, or the address that its creation makes.

The sender is `sender`, with nonce `nonce` before the transaction. -/
def messageTarget (sender : Address) (nonce : Nat) (tx : Transaction) :
    Except EvmError Address :=
  match tx.to with
  | some to => .ok to
  | none => (createAddress sender nonce).mapError .encoding

/-- The message of a transaction from `sender` to `target`, with `gas` gas, at `fork`.

A call runs the code of its recipient on the data, and a creation runs the data as init code. -/
def transactionMessage {fork : Fork} (env : BlockEnvironment fork)
    (txEnv : TransactionEnvironment fork) (state : TransactionState) (sender target : Address)
    (gas : Nat) (tx : Transaction) : Except EvmError (Message fork) :=
  let start (data : ByteArray) (codeAddress : Option Address) (code : ByteArray) : Message fork :=
    { blockEnv := env, txEnv, caller := sender, target := tx.to, currentTarget := target, gas,
      value := tx.value, data, codeAddress, code, depth := 0, shouldTransferValue := true,
      isStatic := false, disablePrecompiles := false }
  match tx.to with
  | some to =>
    start tx.data (some to) <$> (state.getCode (state.getAccount to).codeHash).mapError .state
  | none => .ok (start .empty none tx.data)

/-! ## The message -/

/-- What the message of a transaction leaves. -/
structure CallOutput where
  /-- The state after the message. -/
  state : TransactionState
  /-- The execution gas left. -/
  gasLeft : Nat
  /-- The state gas left in the reservoir, 0 before Glamsterdam. -/
  reservoir : Nat
  /-- The gas to give back, before its cap. -/
  refund : Nat
  /-- The logs, oldest first. -/
  logs : Array Log
  /-- The accounts to delete. -/
  accountsToDelete : Std.ExtTreeSet Address
  /-- The touched accounts, whose empty ones EIP-161 deletes. -/
  touchedAccounts : Std.ExtTreeSet Address
  /-- The error that stopped the message, if any. -/
  error : Option EvmError
  /-- The data that the message returned, or the data of its revert. -/
  output : ByteArray
  /-- The net state gas that the message used, which can be negative, and is 0 before Glamsterdam.
  -/
  stateGasUsed : Int

variable {Meter : Type} [GasMeter Meter]

/-- The output of a message that ends with the frame `evm`, with `refund` gas from before it.

A message that fails keeps its gas left and the earlier refund, and nothing else. -/
def CallOutput.ofFrame {fork : Fork} (evm : Evm fork Meter) (refund : Nat)
    (touched : Std.ExtTreeSet Address) : CallOutput :=
  let gasLeft := GasMeter.gasLeft evm.gas
  let reservoir := GasMeter.reservoir evm.gas
  let used := GasMeter.stateGasUsed evm.gas
  if evm.error.isSome then
    ⟨evm.state, gasLeft, reservoir, refund, #[], ∅, ∅, evm.error, evm.output, used⟩
  else
    ⟨evm.state, gasLeft, reservoir, refund + evm.substate.refundCounter.toNat, evm.substate.logs,
      evm.substate.accountsToDelete, touched, none, evm.output, used⟩

/-- The output of a message whose first frame never runs, because of `error`.

The state stays `state`, from before the message.

No execution gas is left, the reservoir `reservoir` comes back whole, and no state gas is used. -/
def CallOutput.ofHalt (state : TransactionState) (reservoir : Nat) (error : EvmError) :
    CallOutput :=
  ⟨state, 0, reservoir, 0, #[], ∅, ∅, some error, .empty, 0⟩

/-- The first frame of a transaction, ready to run, with a gas meter of type `Meter`. -/
structure FirstFrame (fork : Fork) (Meter : Type) [GasMeter Meter] where
  /-- The message of the frame. -/
  message : Message fork
  /-- The state that the frame starts from. -/
  state : TransactionState
  /-- The substate that the frame starts from. -/
  substate : Substate
  /-- The gas that the authorizations give back. -/
  refund : Nat
  /-- The meter that the frame starts with. -/
  meter : Meter
  /-- The meter holds the gas of the message. -/
  held : GasMeter.gasHeld meter ≤ message.gas

/-- The first frame of `message`, whose meter has paid what comes before it.

The message holds the gas that the meter holds. -/
def FirstFrame.ofMeter {fork : Fork} (message : Message fork) (state : TransactionState)
    (substate : Substate) (refund : Nat) (meter : Meter) : FirstFrame fork Meter :=
  ⟨{ message with gas := GasMeter.gasHeld meter }, state, substate, refund, meter, Nat.le_refl _⟩

/-- The first frame of a transaction at `fork`, on the chain `chainId`, or the error that stops it.

The meter starts with the gas and the reservoir of the message.

A creation fails at an address with code, a nonce or storage.

From Glamsterdam, it pays the state gas of a new account when the address had none before.

A call first applies the authorizations `auths`, then commits the state gas they paid.

From Glamsterdam, a call that moves ether to an account not alive pays for a new account.

From Pectra, a recipient whose code is a delegation indicator runs the code of its delegate.

The delegate is then accessed, and the message runs no precompile.

From Glamsterdam, that access pays the price of an account access, cold or warm.

The accounts `paidWrites` have their first write paid already.

It reads the created address, or the authorities, the recipient and the delegate, in this order.

A call reads the recipient before its state gas only when it moves ether.

An error comes with the state so far, whose reads stay, by EIP-7928. -/
def prepareFirstFrame {fork : Fork} (chainId : Nat) (message : Message fork)
    (state : TransactionState) (substate : Substate) (auths : List Authorization)
    (paidWrites : Std.ExtTreeSet Address) :
    Except (EvmError × TransactionState) (FirstFrame fork Meter) := do
  let meter : Meter := GasMeter.start message.gas message.reservoir
  match message.target with
  | none =>
    let address := message.currentTarget
    let state := state.recordAccountRead address
    unless state.accountDeployable address do throw (.addressCollision, state)
    let meter ← if fork ≥ .glamsterdam ∧ state.getPreStateAccount address = EMPTY_ACCOUNT then
        (GasMeter.chargeState meter NEW_ACCOUNT_STATE_GAS).mapError (·, state)
      else pure meter
    return .ofMeter message state substate 0 meter
  | some target =>
    let done ← applyAuthorizations fork chainId state substate.accessedAddresses meter paidWrites
      auths
    let meter := GasMeter.commit done.meter
    let state := if message.value ≠ 0 then done.state.recordAccountRead target else done.state
    let meter ←
      if fork ≥ .glamsterdam ∧ message.value ≠ 0 ∧ !state.isAccountAlive target then
        (GasMeter.chargeState meter NEW_ACCOUNT_STATE_GAS).mapError (·, state)
      else pure meter
    let substate := { substate with accessedAddresses := done.accessed }
    let state := state.recordAccountRead target
    let code ← (state.getCode (state.getAccount target).codeHash).mapError (.state ·, state)
    match if fork ≥ .pectra then delegatedAddress code else none with
    | some delegate =>
      let meter ← if fork ≥ .glamsterdam then
          (GasMeter.charge meter (accountAccessCost fork (delegate ∉ done.accessed))).mapError
            (·, state)
        else pure meter
      let state := state.recordAccountRead delegate
      let code ← (state.getCode (state.getAccount delegate).codeHash).mapError (.state ·, state)
      let message := { message with code, codeAddress := some delegate, disablePrecompiles := true }
      let substate := { substate with accessedAddresses := done.accessed.insert delegate }
      return .ofMeter message state substate done.refund meter
    | none => return .ofMeter { message with code } state substate done.refund meter

/-- The message of a transaction at `fork`, on the chain `chainId`.

It first prepares the first frame, which applies the authorizations `auths` of a call.

A failure there halts the message before its frame runs, and undoes the authorizations.

That halt keeps what the preparation read.

From Spurious Dragon to Paris, a recipient left empty is touched. -/
def processMessageCall {fork : Fork} [LawfulGasMeter Meter] (chainId : Nat)
    (message : Message fork) (state : TransactionState) (substate : Substate)
    (auths : List Authorization := []) (paidWrites : Std.ExtTreeSet Address := ∅) :
    Except EvmError CallOutput :=
  match prepareFirstFrame (Meter := Meter) chainId message state substate auths paidWrites with
  | .error (e, read) =>
    if e.aborts then .error e else .ok (.ofHalt (state.withReadsOf read) message.reservoir e)
  | .ok first =>
    match message.target with
    | none => do
      let ⟨evm, _⟩ ← processCreateMessage fork first.message first.state first.substate
        first.meter first.held
      return .ofFrame evm 0 evm.substate.touchedAccounts
    | some target => do
      let ⟨evm, _⟩ ← processMessage fork first.message first.state first.substate first.meter
        first.held
      let touched := evm.substate.touchedAccounts
      let touched := if fork ≥ .spuriousDragon ∧ fork < .paris ∧
        evm.state.accountExistsAndIsEmpty target then touched.insert target else touched
      return .ofFrame evm first.refund touched

/-! ## The transaction -/

/-- What a transaction leaves once it has run. -/
structure TransactionOutput where
  /-- The state of the transaction once it has run, before its writes join the block.

  It holds the reads of the transaction, for the block access list of EIP-7928. -/
  state : TransactionState
  /-- The gas that the transaction used, after the refund. -/
  gasUsed : Nat
  /-- The gas that the transaction adds to the counts of its block. -/
  blockGas : BlockGas
  /-- The logs of the transaction, oldest first. -/
  logs : Array Log
  /-- The error that stopped its message, or none when the message succeeded. -/
  error : Option EvmError

/-- The block state, with the writes of the transaction. -/
def TransactionOutput.block (output : TransactionOutput) : BlockState :=
  output.state.incorporateTxIntoBlock.parent

/-- The state after the end of a transaction at `fork`: the deletions of its accounts.

Each account to delete goes, then each touched account that is empty.

From Glamsterdam, an account to delete keeps its balance, and goes only when that is 0. -/
def deleteAccounts (fork : Fork) (state : TransactionState) (output : CallOutput) :
    Except State.StateError TransactionState := do
  let state ← output.accountsToDelete.foldlM (init := state) fun state address =>
    if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
    else pure (state.destroyAccount address)
  return state.destroyTouchedEmptyAccounts fork output.touchedAccounts.toList

/-- The accounts whose first write a transaction from `sender` to `target` has paid.

The intrinsic gas pays the write of the sender.

It also pays that of the target, for a creation or a transfer of ether.

[EIP-2780][eip2780] defines them.

[eip2780]: https://eips.ethereum.org/EIPS/eip-2780#eip-7702-authorization-processing -/
def paidWrites (sender target : Address) (tx : Transaction) : Std.ExtTreeSet Address :=
  let paid := (∅ : Std.ExtTreeSet Address).insert sender
  if tx.to.isNone ∨ tx.value ≠ 0 then paid.insert target else paid

/-- Run a transaction with a gas meter of type `Meter`, on the block state `block` at `fork`.

The checks of the transaction gave `included`.

The gas past the intrinsic gas splits into the execution gas and the reservoir of the message.

The sender gets back the gas left and the reservoir left, with its refund. -/
def runTransaction {fork : Fork} (Meter : Type) [GasMeter Meter] [LawfulGasMeter Meter]
    (env : BlockEnvironment fork) (block : BlockState) (included : Included) (tx : Transaction) :
    Except EvmError TransactionOutput := do
  let state := TransactionState.ofBlock block
  let sender := included.sender
  let target ← messageTarget sender (state.getAccount sender).nonce tx
  let state ← (buyGas env state sender tx).mapError .state
  let txEnv : TransactionEnvironment fork :=
    { origin := sender, gasPrice := included.gasPrice,
      blobVersionedHashes := fun _ => tx.blobHashes }
  let gas := allocateGas fork tx included.intrinsicGas
  let message ← transactionMessage env txEnv state sender target gas.execution tx
  let output ← processMessageCall (Meter := Meter) env.chainId
    { message with reservoir := gas.reservoir } state
    (startSubstate fork env.coinbase sender target tx) tx.authorizations
    (paidWrites sender target tx)
  let gasLeft := output.gasLeft + output.reservoir
  let blockGas := transactionBlockGas fork sender tx gasLeft output.refund output.stateGasUsed
  let (state, gasUsed) ← (settleGas env output.state sender tx gasLeft output.refund).mapError
    .state
  let state ← (deleteAccounts fork state output).mapError .state
  return ⟨state, gasUsed, blockGas, output.logs, output.error⟩

/-- Run a transaction that may enter its block, on the block state `block` at `fork`.

The checks of the transaction gave `included`.

It returns the state of the transaction, whose writes then join the block.

It also returns the gas used, the gas it adds to its block, the logs, and the error of the message.

It fails only with an error that aborts the whole execution, such as missing code.

Up to BPO5, the gas meter is one counter of the gas left.

From Glamsterdam, the meter of EIP-8037 also meters state gas.

From Hegotá it fails, since the rules of that fork are not yet specified here. -/
def processTransaction {fork : Fork} (env : BlockEnvironment fork) (block : BlockState)
    (included : Included) (tx : Transaction) : Except EvmError TransactionOutput :=
  if .hegota ≤ fork then .error (.forkNotYetSpecified fork)
  else if fork ≥ .glamsterdam then runTransaction StateGasMeter env block included tx
  else runTransaction Nat env block included tx

end EthLib.Execution.Transactions
