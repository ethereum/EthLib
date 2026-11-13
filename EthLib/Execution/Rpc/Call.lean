module

public import EthLib.Execution.Rpc.GenericTransaction
public import EthLib.Execution.Rpc.Raw
public import EthLib.Execution.Transactions.Process

/-!
# `Execution.Rpc.Call`

The method `eth_call` of [`execute.yaml`][execute]: a message call on the state after a block.

The call runs the message of its transaction as the state transition runs it, but commits nothing.

It reads the state after the block that its block parameter names, `latest` by default.

The sender is the field `from` of the request, else a sender of the node's choice.

The source fixes few rules of the call, and the node makes the other choices.

These choices are one structure, which every call takes:

- the fork and the block environment of the call;
- the gas limit of a request that names none;
- the price per gas that the code sees when the request names no fee;
- the sender of a request without `from`.

By default the call runs in the environment of the header of the block that it names.

The fixtures `call-callenv.io` and `call-block-hash-object.io` expect the number of that block.

The source fixes no other field of that environment.

The default gas limit is the gas limit of that header, and the default sender is address zero.

That gas limit may be above the cap on the gas of a transaction of EIP-7825, which a call ignores.

A request that names no fee falls under a rule of the source.

It "MUST NOT fail solely because the sender cannot afford the gas fees" of the node's defaults.

It adds that this "does not waive balance requirements for a non-zero transaction `value`".

So a request that names no fee pays no fee, and the code sees the price of the node's choice.

Its environment then has a base fee of 0, so that this price need not cover a base fee.

The fixture `call-callenv.io` expects that base fee of 0.

The fixture `call-callenv-options-eip1559.io` names a fee, and expects the base fee of the header.

A blob fee cap alone names no fee, so such a request pays neither fee.

A request that names a fee buys its gas as a transaction does.

It pays its gas limit times its effective price per gas, and the fee of its blobs.

A transaction must hold the fee at its caps, but a call needs only the fee that it pays.

The blob fee cap is not checked against the base fee per blob gas.

A missing fee cap is the base fee plus the priority fee, and a missing priority fee is 0.

The sender must hold the value, and still hold it once it has paid the fee.

Otherwise the call fails with code 809.

As in a transaction, the nonce of the sender grows by one and the fee leaves its balance.

The nonce of the request is not checked, as the source fixes no rule for it.

Nor is the nonce of the sender bounded, as EIP-2681 bounds it for a transaction.

The gas past the intrinsic gas splits between execution gas and a reservoir as in a transaction.

A gas limit below the intrinsic gas fails with code 800.

So does one below the floor of EIP-7623, from Pectra.

A fee cap or a gas price below the base fee fails with code 806.

A priority fee above the fee cap fails with code 804.

A type that is not yet active at the fork of the call is an invalid parameter.

So is a field that the kind of the request cannot carry, or a chain other than the node's.

So is a creation of type 3 or 4.

The other checks of a transaction before its block do not run.

They are the checks of the blobs and of the authorization list, and of a sender with code.

The call answers the data that the message returns.

A revert answers the error of code 3 and message `"execution reverted"`, as the source fixes.

Its data is the output of the revert.

The source fixes no answer for a halt other than a revert.

Here it is code 801 for a lack of gas and 4 for an invalid opcode.

These codes come from `src/error-groups/` of the source.

Any other halt is code -32000, such as a creation at an address that has code.

A call at a fork that EthLib does not yet specify fails with code -32603.

[execute]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/eth/execute.yaml
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Evm
open EthLib.Execution.Blocks (blockEnvironment)
open EthLib.Execution.State (BlockState TransactionState)
open EthLib.Execution.Transactions

/-- A fork with a block environment at that fork, in which a call runs. -/
structure CallEnvironment where
  /-- The fork of the call. -/
  fork : Fork
  /-- The block environment of the call. -/
  env : BlockEnvironment fork

/-- The environment of the header of a block of the view.

The hashes before it are those of the last 256 canonical blocks below its number, or fewer.

They leave out the blocks of the history.

For a block off the canonical chain, they are not the hashes of its ancestors. -/
def ChainView.headerEnvironment (v : ChainView) (r : BlockRecord) : CallEnvironment :=
  let before := (v.canonical.filter (·.block.header.number < r.block.header.number)).map (·.hash)
  ⟨r.fork, blockEnvironment v.config (before.drop (before.length - 256)) r.block.header⟩

/-- The choices that the source leaves to the node, for a call. -/
structure CallChoices where
  /-- The fork and the environment of a call on the state after a block of the view. -/
  environment : ChainView → BlockRecord → CallEnvironment := ChainView.headerEnvironment
  /-- The gas limit of a request that names none, or none for the gas limit of the environment. -/
  gasLimit : Option Nat := none
  /-- The price per gas that the code sees when the request names no fee. -/
  gasPrice : Nat := 0
  /-- The sender of a request without `from`. -/
  sender : Address := Vector.replicate 20 0

/-- The error of a parameter of a call that does not fit its field or its kind. -/
def callParamError (reason : String) : RpcError :=
  RpcError.invalidParams s!"transaction: {reason}"

/-- A number of the request as a 256-bit word, or the error of a number that does not fit. -/
def callWord (what : String) (n : Nat) : Except RpcError U256 :=
  if n < 2 ^ 256 then .ok (BitVec.ofNat 256 n) else .error (callParamError s!"{what}: too large")

/-- The unsigned transaction of a request, with every signature field 0.

`nonce` is the nonce of the sender's account, and `gas` is the gas limit.

`chainId` is the chain of the node.

Each fee field that the request leaves out is 0 here, and the fee cap is `maxFee`.

A field that its kind does not allow, or another chain, fails with the code of invalid parameters.
-/
def GenericTransaction.toTransaction (tx : GenericTransaction) (chainId : UInt64)
    (nonce gas maxFee : Nat) : Except RpcError Transaction := do
  let kind := tx.kind
  ensure (kind ≤ 4) (callParamError "type: not a transaction type")
  ensure (¬(kind ≤ 1 && (tx.maxFeePerGas.isSome || tx.maxPriorityFeePerGas.isSome)))
    (callParamError "a fee cap needs type 2, 3 or 4")
  ensure (¬(2 ≤ kind && tx.gasPrice.isSome)) (callParamError "a gas price needs type 0 or 1")
  ensure (¬(kind = 0 && tx.accessList.isSome))
    (callParamError "an access list needs type 1 or more")
  ensure (¬(kind ≠ 3 && (tx.blobVersionedHashes.isSome || tx.maxFeePerBlobGas.isSome)))
    (callParamError "blobs need type 3")
  ensure (¬(kind ≠ 4 && tx.authorizationList.isSome)) (callParamError "authorizations need type 4")
  if let some c := tx.chainId then
    ensure (c = chainId.toNat) (callParamError "chainId: not the chain of the node")
  let nonce ← callWord "nonce" nonce
  let gas ← callWord "gas" gas
  let value ← callWord "value" (tx.value.getD 0)
  let data := tx.input.getD .empty
  let accessList := tx.accessList.getD []
  let maxPriorityFeePerGas ← callWord "maxPriorityFeePerGas" (tx.maxPriorityFeePerGas.getD 0)
  let maxFeePerGas ← callWord "maxFeePerGas" maxFee
  let gasPrice ← callWord "gasPrice" (tx.gasPrice.getD 0)
  if kind = 0 then
    return .legacy { nonce, gasPrice, gas, to := tx.to, value, data, v := 0, r := 0, s := 0 }
  if kind = 1 then
    return .accessList { chainId, nonce, gasPrice, gas, to := tx.to, value, data, accessList,
                         yParity := 0, r := 0, s := 0 }
  if kind = 2 then
    return .feeMarket { chainId, nonce, maxPriorityFeePerGas, maxFeePerGas, gas, to := tx.to,
                        value, data, accessList, yParity := 0, r := 0, s := 0 }
  let some to := tx.to | throw (callParamError "type 3 and type 4 need a recipient")
  if kind = 3 then
    return .blob { chainId, nonce, maxPriorityFeePerGas, maxFeePerGas, gas, to, value, data,
                   accessList, yParity := 0, r := 0, s := 0
                   maxFeePerBlobGas := ← callWord "maxFeePerBlobGas" (tx.maxFeePerBlobGas.getD 0)
                   blobVersionedHashes := tx.blobVersionedHashes.getD [] }
  return .setCode { chainId, nonce, maxPriorityFeePerGas, maxFeePerGas, gas, to, value, data,
                    accessList, authorizations := tx.authorizationList.getD [], yParity := 0,
                    r := 0, s := 0 }

/-- A call ready to run: its environment, its sender, its transaction, its state and its message. -/
structure CallSetup where
  /-- The fork of the call. -/
  fork : Fork
  /-- The block environment of the call. -/
  env : BlockEnvironment fork
  /-- The sender. -/
  sender : Address
  /-- The unsigned transaction of the request. -/
  transaction : Transaction
  /-- The state after the block, with the nonce and the fee of the sender taken. -/
  state : TransactionState
  /-- The message of the transaction. -/
  message : Message fork
  /-- The substate that the message starts from. -/
  substate : Substate

/-- The first message of a transaction once it has bought its gas, and the substate it starts from.

The sender is `sender`, the target `target`, and the code sees the price per gas `gasPrice`.

The gas past the intrinsic gas `intrinsic` splits between execution gas and a reservoir.

These are the steps that `runTransaction` takes between buying the gas and running the message. -/
def transactionStart {fork : Fork} (env : BlockEnvironment fork) (state : TransactionState)
    (sender target : Address) (gasPrice intrinsic : Nat) (tx : Transaction) :
    Except EvmError (Message fork × Substate) := do
  let txEnv : TransactionEnvironment fork :=
    { origin := sender, gasPrice, blobVersionedHashes := fun _ => tx.blobHashes }
  let gas := allocateGas fork tx intrinsic
  let message ← transactionMessage env txEnv state sender target gas.execution tx
  return ({ message with reservoir := gas.reservoir },
    startSubstate fork env.coinbase sender target tx)

/-- The error of a failure of the node itself, such as missing code in its state. -/
def callInternalError (reason : String) : RpcError :=
  internalError.toRpcError (some (.str s!"call: {reason}"))

/-- The call of a request on the state after a block, ready to run, or the error that stops it.

The block is the one that `p` names, and `choices` are the choices of the node. -/
def ChainView.prepareCall (v : ChainView) (tx : GenericTransaction) (p : BlockParam)
    (choices : CallChoices) : Except RpcError CallSetup :=
  v.ofBlock p fun r => do
    let ce := choices.environment v r
    let fork := ce.fork
    let env := if tx.namesFee then ce.env else { ce.env with baseFeePerGas := fun _ => 0 }
    ensure (fork < .hegota) (callInternalError "fork not yet specified")
    let sender := tx.sender.getD choices.sender
    let state := TransactionState.ofBlock ⟨r.state, ∅, ∅, ∅, ∅⟩
    let account := state.getAccount sender
    let gas := tx.gas.getD (choices.gasLimit.getD env.gasLimit)
    let baseFee := baseFeeOf env
    let priority := tx.maxPriorityFeePerGas.getD 0
    let maxFee := tx.maxFeePerGas.getD (baseFee + priority)
    let t ← tx.toTransaction env.chainId account.nonce gas (if tx.namesFee then maxFee else 0)
    if 2 ≤ tx.kind && tx.namesFee then
      ensure (priority ≤ maxFee) (priorityFeeAboveCap.toRpcError)
    ensure (t.fork ≤ fork) (callParamError "type: not active at the fork of the block")
    ensure (¬(tx.namesFee && t.maxFeePerGas < baseFee)) feeCapBelowBaseFee.toRpcError
    let price := if tx.namesFee then effectiveGasPrice baseFee t else choices.gasPrice
    ensure (t.value.toNat ≤ account.balance.toNat) insufficientFunds.toRpcError
    let target ← (messageTarget sender account.nonce t).mapError fun _ =>
      callInternalError "no address for the creation"
    let bought :=
      if tx.namesFee then buyGas env state sender t else state.incrementNonce fork sender
    let state ← bought.mapError fun
      | .insufficientBalance _ => insufficientFunds.toRpcError
      | _ => callInternalError "the account of the sender"
    ensure (t.value.toNat ≤ (state.getAccount sender).balance.toNat) insufficientFunds.toRpcError
    ensure (minimumGas fork sender t ≤ gas) intrinsicGasTooLow.toRpcError
    let (message, substate) ←
      (transactionStart env state sender target price (intrinsicGas fork sender t) t).mapError
        fun _ => callInternalError "code: missing from the state"
    return { fork, env, sender, transaction := t, state, message, substate }

/-- Run the message of a call as the state transition runs the message of a transaction.

From Glamsterdam, the gas meter also meters state gas. -/
def CallSetup.run (s : CallSetup) : Except EvmError CallOutput :=
  let paid := paidWrites s.sender s.message.currentTarget s.transaction
  if s.fork ≥ .glamsterdam then
    processMessageCall (Meter := StateGasMeter) s.env.chainId.toNat s.message s.state s.substate
      s.transaction.authorizations paid
  else
    processMessageCall (Meter := Nat) s.env.chainId.toNat s.message s.state s.substate
      s.transaction.authorizations paid

/-- The error of a call that reverts, code 3, with the output of the revert as its data. -/
def revertError (output : ByteArray) : RpcError :=
  { code := executionReverted.code, message := "execution reverted"
    data := some (dataJson output.toList) }

/-- The error of a call that halts for a reason other than a revert. -/
def haltError : EvmError → RpcError
  | .outOfGas => ranOutOfGas.toRpcError
  | .invalidOpcode _ => invalidOpcode.toRpcError
  | _ => { code := -32000, message := "execution failed" }

/-- The answer of a call whose message gave `o`: its return data, or the error that stopped it. -/
def callAnswer (o : CallOutput) : Except RpcError ByteArray :=
  match o.error with
  | none => .ok o.output
  | some .revert => .error (revertError o.output)
  | some e => .error (haltError e)

/-- The call of a request on the state after a block, and the output of its message.

It fails with the error that stops the call before its message, or that aborts the message. -/
def ChainView.runCall (v : ChainView) (tx : GenericTransaction) (p : BlockParam)
    (choices : CallChoices) : Except RpcError (CallSetup × CallOutput) := do
  let s ← v.prepareCall tx p choices
  let o ← s.run.mapError fun _ => callInternalError "the execution aborted"
  return (s, o)

/-- The answer of `eth_call` for a request on the state after the block that `p` names. -/
def ChainView.ethCall (v : ChainView) (tx : GenericTransaction) (p : BlockParam)
    (choices : CallChoices) : Except RpcError ByteArray := do
  let (_, o) ← v.runCall tx p choices
  callAnswer o

end EthLib.Execution.Rpc
