module

public import EthLib.Execution.Rpc.GenericTransaction
public import EthLib.Execution.Rpc.Raw
public import EthLib.Execution.Transactions.Process

/-!
# `Execution.Rpc.Call`

The method `eth_call`: a message call on the state after a block.

The call runs the message of its transaction as the state transition runs it, but commits nothing.

Source: [`execute.yaml`][execute], at commit `1ca0818` of execution-apis: the method.

[execute]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/eth/execute.yaml
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

By default the call runs in the environment of the header of the block that it names.

The fixtures `call-callenv.io` and `call-block-hash-object.io` expect the number of that block.

The source fixes no other field of that environment.

The hashes before it are those of the last 256 canonical blocks below its number, or fewer.

They leave out the blocks of the history.

For a block off the canonical chain, they are not the hashes of its ancestors. -/
def ChainView.headerEnvironment (v : ChainView) (r : BlockRecord) : CallEnvironment :=
  let before := (v.canonical.filter (·.block.header.number < r.block.header.number)).map (·.hash)
  ⟨r.fork, blockEnvironment v.config (before.drop (before.length - 256)) r.block.header⟩

/-- The choices that the source leaves to the node, for a call.

The source fixes few rules of the call, and the node makes the other choices.

Every call takes them as one structure:

- the fork and the environment of the call
- the gas limit of a request that names none
- the price per gas that the code sees when the request names no fee
- the sender of a request without `from`

The default gas limit is the gas limit of the header, and the default sender is address zero.

That gas limit may be above the cap on the gas of a transaction of EIP-7825, which a call ignores.
-/
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

/-- The error of a request that a rule of the method rejects, code -32000 for invalid input.

The text names no code for its rejections, and the fixtures expect -32000.

That is the code of invalid input in [EIP-1474][eip-1474], which EthLib gives them.

[eip-1474]: https://eips.ethereum.org/EIPS/eip-1474#error-codes -/
def callRuleError (reason : String) : RpcError :=
  invalidInput.toRpcError (some (.str s!"transaction: {reason}"))

/-- A number of the request as a 256-bit word, or the error of a number that does not fit. -/
def callWord (what : String) (n : Nat) : Except RpcError U256 :=
  if n < 2 ^ 256 then .ok (BitVec.ofNat 256 n) else .error (callParamError s!"{what}: too large")

/-- A number of the request as a 64-bit integer, or the error of a number that does not fit. -/
def callUint64 (what : String) (n : Nat) : Except RpcError UInt64 :=
  if h : n < 2 ^ 64 then .ok (UInt64.ofNatLT n h)
  else .error (callParamError s!"{what}: too large")

/-- The unsigned transaction of a request, with every signature field 0.

`nonce` is the nonce of the sender's account, and `gas` is the gas limit.

`chainId` is the chain of the node.

Each fee field that the request leaves out is 0 here, and the fee cap is `maxFee`.

A fee, an access list, blob hashes, a blob fee cap or authorizations that its kind lacks fail.

So does a chain other than `chainId`, a kind above 4, or type 3 or 4 without a recipient.

So does a value, fee or fee cap of the request, or `nonce`, `gas` or `maxFee`, of `2 ^ 256` or more.

Type 4 holds its nonce in 64 bits, so it also fails on a `nonce` of `2 ^ 64` or more.

Each of these fails with the code of invalid parameters.

The schema of the request ties none of its fields to its kind, so the checks of kind are EthLib's.

The blobs, their commitments and their proofs are never checked, and leave the result unchanged.
-/
def GenericTransaction.toTransaction (tx : GenericTransaction) (chainId : UInt64)
    (nonce gas maxFee : Nat) : Except RpcError Transaction := do
  -- The type of the request, else the kind its fields imply, EthLib's reading; above 4 is invalid.
  let kind := tx.kind
  ensure (kind ≤ 4) (callParamError "type: not a transaction type")
  -- Each field that the kind lacks is an invalid parameter.
  ensure (¬(kind ≤ 1 && (tx.maxFeePerGas.isSome || tx.maxPriorityFeePerGas.isSome)))
    (callParamError "a fee cap needs type 2, 3 or 4")
  ensure (¬(2 ≤ kind && tx.gasPrice.isSome)) (callParamError "a gas price needs type 0 or 1")
  ensure (¬(kind = 0 && tx.accessList.isSome))
    (callParamError "an access list needs type 1 or more")
  ensure (¬(kind ≠ 3 && (tx.blobVersionedHashes.isSome || tx.maxFeePerBlobGas.isSome)))
    (callParamError "blobs need type 3")
  ensure (¬(kind ≠ 4 && tx.authorizationList.isSome)) (callParamError "authorizations need type 4")
  -- A chain other than the node's is an invalid parameter.
  if let some c := tx.chainId then
    ensure (c = chainId.toNat) (callParamError "chainId: not the chain of the node")
  -- Each number must fit in 256 bits, else an invalid parameter.
  let nonce ← callWord "nonce" nonce
  let gas ← callWord "gas" gas
  let value ← callWord "value" (tx.value.getD 0)
  let data := tx.input.getD .empty
  let accessList := tx.accessList.getD []
  let maxPriorityFeePerGas ← callWord "maxPriorityFeePerGas" (tx.maxPriorityFeePerGas.getD 0)
  let maxFeePerGas ← callWord "maxFeePerGas" maxFee
  let gasPrice ← callWord "gasPrice" (tx.gasPrice.getD 0)
  -- The transaction of the kind, with a signature of 0.
  if kind = 0 then
    return .legacy { nonce, gasPrice, gas, to := tx.to, value, data, v := 0, r := 0, s := 0 }
  if kind = 1 then
    return .accessList { chainId, nonce, gasPrice, gas, to := tx.to, value, data, accessList,
                         yParity := 0, r := 0, s := 0 }
  if kind = 2 then
    return .feeMarket { chainId, nonce, maxPriorityFeePerGas, maxFeePerGas, gas, to := tx.to,
                        value, data, accessList, yParity := 0, r := 0, s := 0 }
  -- EIP-4844 and EIP-7702: types 3 and 4 have a recipient.
  let some to := tx.to | throw (callParamError "type 3 and type 4 need a recipient")
  if kind = 3 then
    return .blob { chainId, nonce, maxPriorityFeePerGas, maxFeePerGas, gas, to, value, data,
                   accessList, yParity := 0, r := 0, s := 0
                   maxFeePerBlobGas := ← callWord "maxFeePerBlobGas" (tx.maxFeePerBlobGas.getD 0)
                   blobVersionedHashes := tx.blobVersionedHashes.getD [] }
  -- A set-code transaction holds its nonce in 64 bits.
  let nonce ← callUint64 "nonce" nonce.toNat
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

These are the steps that a transaction takes between buying its gas and running its message. -/
def transactionStart {fork : Fork} (env : BlockEnvironment fork) (state : TransactionState)
    (sender target : Address) (gasPrice intrinsic : Nat) (tx : Transaction) :
    Except EvmError (Message fork × Substate) := do
  -- The environment of the transaction: the Yellow Paper's `I_o` is the sender, `I_p` the price.
  let txEnv : TransactionEnvironment fork :=
    { origin := sender, gasPrice, blobVersionedHashes := fun _ => tx.blobHashes }
  -- The gas past the intrinsic gas: execution gas, and from Glamsterdam a reservoir, by EIP-8037.
  let gas := allocateGas fork tx intrinsic
  let message ← transactionMessage env txEnv state sender target gas.execution tx
  return ({ message with reservoir := gas.reservoir },
    startSubstate fork env.coinbase sender target tx)

/-- The error of a failure of the node itself, such as missing code in its state. -/
def callInternalError (reason : String) : RpcError :=
  internalError.toRpcError (some (.str s!"call: {reason}"))

/-- The call of a request on the state after a block, ready to run, or the error that stops it.

The block is the one that `p` names, and `choices` are the choices of the node.

The call ignores the field `type`, as the [text of the method][rules] requires.

Past their reading as bytes, a call never reads the blobs, their commitments or their proofs.

So its kind does not limit them.

[rules]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/eth/execute.yaml#L11-L24
-/
def ChainView.prepareCall (v : ChainView) (tx : GenericTransaction) (p : BlockParam)
    (choices : CallChoices) : Except RpcError CallSetup :=
  -- The text of the method ignores the type of the request, so the other fields decide the kind.
  --
  -- So any type gives the answer of no type.
  let tx : GenericTransaction := { tx with type := none }
  v.ofBlock p fun r => do
    let ce := choices.environment v r
    let fork := ce.fork
    -- A request that names no fee falls under a rule of the source.
    --
    -- Such a request must not fail solely because the sender cannot afford the node's default fees.
    --
    -- The rule adds that this does not waive the balance requirement for a value that is not zero.
    --
    -- So a request that names no fee pays no fee, and the code sees the price of the node's choice.
    --
    -- Its environment then has a base fee of 0, so that this price need not cover a base fee.
    --
    -- The fixture `call-callenv.io` expects that base fee of 0.
    --
    -- The fixture `call-callenv-options-eip1559.io` names a fee, and expects the header's base fee.
    --
    -- A blob fee cap alone names no fee, so such a request pays neither fee.
    let env := if tx.namesFee then ce.env else { ce.env with baseFeePerGas := fun _ => 0 }
    -- A fork that EthLib does not yet specify: EthLib's rejection, code -32603.
    ensure (fork < .hegota) (callInternalError "fork not yet specified")
    -- The text of the method rejects empty blob hashes, or a blob fee cap without them: -32000.
    ensure (tx.blobVersionedHashes ≠ some []) (callRuleError "blobVersionedHashes: empty")
    ensure (¬(tx.maxFeePerBlobGas.isSome ∧ tx.blobVersionedHashes.isNone))
      (callRuleError "maxFeePerBlobGas: no blobVersionedHashes")
    -- The sender of the request, else the node's choice.
    let sender := tx.sender.getD choices.sender
    -- The state after the block, with no write yet.
    let state := TransactionState.ofBlock ⟨r.state, ∅, ∅, ∅, ∅⟩
    let account := state.getAccount sender
    -- The gas limit of the request, else the node's choice, else that of the environment.
    let gas := tx.gas.getD (choices.gasLimit.getD env.gasLimit)
    -- A missing fee cap is the base fee plus the priority fee, and a missing priority fee is 0.
    let baseFee := baseFeeOf env
    let priority := tx.maxPriorityFeePerGas.getD 0
    let maxFee := tx.maxFeePerGas.getD (baseFee + priority)
    -- The unsigned transaction at the sender's nonce, with a fee cap of 0 when no fee is named.
    --
    -- The nonce of the request is not checked, as the source fixes no rule for it.
    --
    -- Nor is the nonce of the sender bounded, as EIP-2681 bounds it for a transaction.
    let t ← tx.toTransaction env.chainId account.nonce gas (if tx.namesFee then maxFee else 0)
    -- A priority fee above the fee cap: code 804.
    if 2 ≤ tx.kind && tx.namesFee then
      ensure (priority ≤ maxFee) (priorityFeeAboveCap.toRpcError)
    -- A field whose EIP is not active at the block: code -32000, even when zero or an empty list.
    --
    -- The fields are an access list before Berlin, a fee cap or a priority fee before London.
    --
    -- They also include blob hashes before Cancun, and authorizations before Prague.
    --
    -- The kind has the fork of the latest of these fields, so its fork check covers them.
    ensure (t.fork ≤ fork) (callRuleError "a field is not active at the fork of the block")
    -- A fee cap or a gas price below the base fee: code 806.
    ensure (¬(tx.namesFee && t.maxFeePerGas < baseFee)) feeCapBelowBaseFee.toRpcError
    -- The price per gas that the code sees: the effective gas price, or the node's choice.
    let price := if tx.namesFee then effectiveGasPrice baseFee t else choices.gasPrice
    -- The sender holds the value, else code 809.
    ensure (t.value.toNat ≤ account.balance.toNat) insufficientFunds.toRpcError
    let target ← (messageTarget sender account.nonce t).mapError fun _ =>
      callInternalError "no address for the creation"
    -- A request that names a fee buys its gas as a transaction does.
    --
    -- That request pays its gas limit times its effective price per gas, and the fee of its blobs.
    --
    -- A transaction must hold the fee at its caps, but a call needs only the fee that it pays.
    --
    -- The blob fee cap is not checked against the base fee per blob gas.
    --
    -- As in a transaction, the nonce of the sender grows by one and the fee leaves its balance.
    --
    -- A request that names no fee still grows the nonce of the sender by one.
    let bought :=
      if tx.namesFee then buyGas env state sender t else state.incrementNonce fork sender
    let state ← bought.mapError fun
      | .insufficientBalance _ => insufficientFunds.toRpcError
      | _ => callInternalError "the account of the sender"
    -- The sender still holds the value once it has paid the fee, else code 809.
    ensure (t.value.toNat ≤ (state.getAccount sender).balance.toNat) insufficientFunds.toRpcError
    -- A gas limit below the intrinsic gas, or from Pectra the floor of EIP-7623: code 800.
    ensure (minimumGas fork sender t ≤ gas) intrinsicGasTooLow.toRpcError
    -- The other checks of a transaction before its block do not run.
    --
    -- They are the checks of the blobs and of the authorization list, and of a sender with code.
    let (message, substate) ←
      (transactionStart env state sender target price (intrinsicGas fork sender t) t).mapError
        fun _ => callInternalError "code: missing from the state"
    return { fork, env, sender, transaction := t, state, message, substate }

/-- Run the message of a call as the state transition runs the message of a transaction.

From Glamsterdam, the gas meter also meters state gas. -/
def CallSetup.run (s : CallSetup) : Except EvmError CallOutput :=
  let paid := paidWrites s.sender s.message.currentTarget s.transaction
  -- From Glamsterdam, the meter of EIP-8037; before, one counter of gas.
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
  -- A lack of gas: code 801.
  | .outOfGas => ranOutOfGas.toRpcError
  -- An invalid opcode: code 4.
  | .invalidOpcode _ => invalidOpcode.toRpcError
  -- Any other halt, such as a creation at an address that has code: code -32000, EthLib's choice.
  | _ => { code := -32000, message := "execution failed" }

/-- The answer of a call whose message gave `o`: its return data, or the error that stopped it.

The source fixes the answer of a revert, and no answer for a halt other than a revert.

EthLib takes the codes of the other answers from `src/error-groups/` of the source. -/
def callAnswer (o : CallOutput) : Except RpcError ByteArray :=
  match o.error with
  -- The data that the message returns.
  | none => .ok o.output
  -- A revert: code 3, with the output of the revert as its data, as the source fixes.
  | some .revert => .error (revertError o.output)
  -- Another halt: the source fixes no answer.
  | some e => .error (haltError e)

/-- The call of a request on the state after a block, and the output of its message.

It fails with the error that stops the call before its message, or that aborts the message. -/
def ChainView.runCall (v : ChainView) (tx : GenericTransaction) (p : BlockParam)
    (choices : CallChoices) : Except RpcError (CallSetup × CallOutput) := do
  let s ← v.prepareCall tx p choices
  let o ← s.run.mapError fun _ => callInternalError "the execution aborted"
  return (s, o)

/-- The answer of `eth_call` for a request on the state after the block that `p` names.

The sender is the field `from` of the request, else a sender of the node's choice. -/
def ChainView.ethCall (v : ChainView) (tx : GenericTransaction) (p : BlockParam)
    (choices : CallChoices) : Except RpcError ByteArray := do
  let (_, o) ← v.runCall tx p choices
  callAnswer o

end EthLib.Execution.Rpc
