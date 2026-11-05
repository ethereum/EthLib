module

public import EthLib.Execution.Evm.ContractAddress
public import EthLib.Execution.Evm.MessageCall
public import EthLib.Execution.Transactions.Authorization
public import EthLib.Execution.Transactions.Inclusion

/-!
# `Transactions.Process`

The run of a transaction that may enter its block: its message, then the settlement of its gas.

The sender first buys the gas, and its nonce grows by one.

The message gets the gas limit minus the intrinsic gas.

A call runs the code of its recipient, and a creation runs the data as init code.

A creation goes to the address that the sender and its nonce before the transaction give.

It fails at once, with no gas left, when that address has code or a nonce.

From Berlin, the transaction starts with some addresses and storage keys accessed:

- the sender, the recipient or the created address, and the precompiles of the fork;
- each address and storage key of the access list;
- from Shapella, the beneficiary of the block.

From Pectra, the authorizations of a set code transaction apply before its message.

From Pectra, a recipient whose code is a delegation indicator runs the code of its delegate.

The delegate is then accessed, and the message runs no precompile.

A message that fails keeps no log, no refund and no account to delete.

Once the message ends, the sender gets back its gas left and its refund.

Then the beneficiary gets its fee.

Then each account that SELFDESTRUCT marked is deleted.

From Spurious Dragon to Paris, each touched account that is empty is deleted too.

Section 6.2 of the Yellow Paper, Shanghai version, defines the run of a transaction.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

The EIPs that change it:

- [EIP-161][eip161], the deletion of touched empty accounts
- [EIP-2929][eip2929], the accessed addresses at the start
- [EIP-2930][eip2930], the access list
- [EIP-3651][eip3651], the beneficiary accessed at the start
- [EIP-7702][eip7702], the authorizations and the delegated recipient

These rules hold up to BPO5, which keeps the rules of BPO2.

Glamsterdam changes the gas used of a transaction, by EIP-7778 and EIP-8037.

It also records the reads of the run, by EIP-7928.

Those rules are not here yet, so a run from Glamsterdam fails as not yet specified.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip161]: https://eips.ethereum.org/EIPS/eip-161#specification
[eip2929]: https://eips.ethereum.org/EIPS/eip-2929#specification
[eip2930]: https://eips.ethereum.org/EIPS/eip-2930#specification
[eip3651]: https://eips.ethereum.org/EIPS/eip-3651#specification
[eip7702]: https://eips.ethereum.org/EIPS/eip-7702#behavior
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Blocks (Log)
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState TransactionState)

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
  /-- The gas left. -/
  gasLeft : Nat
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

/-- The output of a message that ends with the frame `evm`, with `refund` gas from before it.

A message that fails keeps its gas left and the earlier refund, and nothing else. -/
def CallOutput.ofFrame {fork : Fork} (evm : Evm fork Nat) (refund : Nat)
    (touched : Std.ExtTreeSet Address) : CallOutput :=
  if evm.error.isSome then
    ⟨evm.state, GasMeter.gasLeft evm.gas, refund, #[], ∅, ∅, evm.error⟩
  else
    ⟨evm.state, GasMeter.gasLeft evm.gas, refund + evm.substate.refundCounter.toNat,
      evm.substate.logs, evm.substate.accountsToDelete, touched, none⟩

/-- The message of a creation, at `fork`.

At an address with code or a nonce, it fails with no gas left. -/
def processCreation {fork : Fork} (message : Message fork) (state : TransactionState)
    (substate : Substate) : Except EvmError CallOutput :=
  if state.accountDeployable message.currentTarget then do
    let ⟨evm, _⟩ ← processCreateMessage (Meter := Nat) fork message state substate
    return .ofFrame evm 0 evm.substate.touchedAccounts
  else .ok ⟨state, 0, 0, #[], ∅, ∅, some .addressCollision⟩

/-- The message of a call to `target` at `fork`, once the authorizations have applied.

From Pectra, a recipient whose code is a delegation indicator runs the code of its delegate.

From Spurious Dragon to Paris, a recipient left empty is touched. -/
def processCall {fork : Fork} (message : Message fork) (target : Address)
    (state : TransactionState) (substate : Substate) (refund : Nat) :
    Except EvmError CallOutput := do
  let code ← (state.getCode (state.getAccount target).codeHash).mapError .state
  let delegate := if fork ≥ .pectra then delegatedAddress code else none
  let (message, substate) ← match delegate with
    | some delegate => do
      let code ← (state.getCode (state.getAccount delegate).codeHash).mapError .state
      pure ({ message with code, codeAddress := some delegate, disablePrecompiles := true },
        { substate with accessedAddresses := substate.accessedAddresses.insert delegate })
    | none => pure ({ message with code }, substate)
  let ⟨evm, _⟩ ← processMessage (Meter := Nat) fork message state substate
  let touched := evm.substate.touchedAccounts
  let touched := if fork ≥ .spuriousDragon ∧ fork < .paris ∧
    evm.state.accountExistsAndIsEmpty target then touched.insert target else touched
  return .ofFrame evm refund touched

/-- The message of a transaction at `fork`, on the chain `chainId`.

A call first applies the authorizations `auths`.

They add to the accessed addresses and to the refund.

From Glamsterdam it fails, since the rules of that fork are not yet specified here. -/
def processMessageCall {fork : Fork} (chainId : Nat) (message : Message fork)
    (state : TransactionState) (substate : Substate) (auths : List Authorization) :
    Except EvmError CallOutput :=
  if .glamsterdam ≤ fork then .error (.forkNotYetSpecified fork) else
  match message.target with
  | none => processCreation message state substate
  | some target => do
    let done ← (applyAuthorizations fork chainId state substate.accessedAddresses auths).mapError
      .state
    processCall message target done.state { substate with accessedAddresses := done.accessed }
      done.refund

/-! ## The transaction -/

/-- What a transaction leaves once it has run. -/
structure TransactionOutput where
  /-- The block state, with the writes of the transaction. -/
  block : BlockState
  /-- The gas that the transaction used, after the refund. -/
  gasUsed : Nat
  /-- The logs of the transaction, oldest first. -/
  logs : Array Log
  /-- The error that stopped its message, or none when the message succeeded. -/
  error : Option EvmError

/-- The state after the end of a transaction at `fork`: the deletions of its accounts.

Each account to delete goes, then each touched account that is empty. -/
def deleteAccounts (fork : Fork) (state : TransactionState) (output : CallOutput) :
    TransactionState :=
  let state := output.accountsToDelete.foldl (fun state address => state.destroyAccount address)
    state
  state.destroyTouchedEmptyAccounts fork output.touchedAccounts.toList

/-- Run a transaction that may enter its block, on the block state `block` at `fork`.

The checks of the transaction gave `included`.

It returns the block state with the writes of the transaction.

It also returns the gas used, the logs, and the error of the message.

It fails only with an error that aborts the whole execution, such as missing code.

From Glamsterdam it fails, since the rules of that fork are not yet specified here. -/
def processTransaction {fork : Fork} (env : BlockEnvironment fork) (block : BlockState)
    (included : Included) (tx : Transaction) : Except EvmError TransactionOutput := do
  if .glamsterdam ≤ fork then throw (.forkNotYetSpecified fork)
  let state := TransactionState.ofBlock block
  let sender := included.sender
  let target ← messageTarget sender (state.getAccount sender).nonce tx
  let state ← (buyGas env state sender tx).mapError .state
  let txEnv : TransactionEnvironment fork :=
    { origin := sender, gasPrice := included.gasPrice,
      blobVersionedHashes := fun _ => tx.blobHashes }
  let message ← transactionMessage env txEnv state sender target
    (tx.gas.toNat - included.intrinsicGas) tx
  let output ← processMessageCall env.chainId message state
    (startSubstate fork env.coinbase sender target tx) tx.authorizations
  let settled := settleGas env output.state sender tx output.gasLeft output.refund
  let (state, gasUsed) ← settled.mapError .state
  let state := deleteAccounts fork state output
  return ⟨state.incorporateTxIntoBlock.parent, gasUsed, output.logs, output.error⟩

end EthLib.Execution.Transactions
