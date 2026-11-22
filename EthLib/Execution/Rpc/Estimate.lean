module

public import EthLib.Execution.Rpc.Call

/-!
# `Execution.Rpc.Estimate`

The methods `eth_estimateGas` and `eth_createAccessList` of [`execute.yaml`][execute].

Both take the request and the block parameter of `eth_call`, and run its call the same way.

The block parameter is optional, and `latest` by default.

Of the three methods, only `eth_call` states that default, and the other two follow it.

[execute]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/eth/execute.yaml
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Evm
open EthLib.Execution.Transactions

namespace ChainView

/-- The call completes with gas limit `g`.

It prepares, and its message neither reverts nor halts. -/
def Completes (v : ChainView) (tx : GenericTransaction) (p : BlockParam) (c : CallChoices)
    (g : Nat) : Prop :=
  ∃ s o, v.runCall { tx with gas := some g } p c = .ok (s, o) ∧ o.error = none

instance (v : ChainView) (tx : GenericTransaction) (p : BlockParam) (c : CallChoices) (g : Nat) :
    Decidable (v.Completes tx p c g) :=
  match h : v.runCall { tx with gas := some g } p c with
  | .ok (s, o) =>
    if he : o.error = none then isTrue ⟨s, o, h, he⟩
    else isFalse fun ⟨_, _, h', he'⟩ => by
      rw [h, Except.ok.injEq, Prod.mk.injEq] at h'
      obtain ⟨-, rfl⟩ := h'
      exact he he'
  | .error _ => isFalse fun ⟨_, _, h', _⟩ => by rw [h] at h'; cases h'

/-- A gas limit up to `hi`, found by binary search above `lo`.

The answer is `hi` or a limit with which the call completes.

It is the least such limit when the limits that complete form an interval. -/
def searchGas (v : ChainView) (tx : GenericTransaction) (p : BlockParam) (c : CallChoices)
    (lo hi : Nat) : Nat :=
  -- `hi` stays a limit that completes, as the caller checks it first; the search stops at `lo + 1`.
  if lo + 1 < hi then
    let mid := (lo + hi) / 2
    -- Down to `mid` when the call completes there, else up from it.
    if v.Completes tx p c mid then v.searchGas tx p c lo mid else v.searchGas tx p c mid hi
  else hi
termination_by hi - lo

/-- The answer of `eth_estimateGas`: a gas limit with which the call completes.

The source asks for an estimate of the gas that lets the transaction complete, and no more.

If the limits that complete form an interval, the answer is the least positive one.

Code that reads the gas left can break that property, and the answer may then not be the least.

The estimate has no cap from EIP-7825, as the call has none.

When the request names a fee, the first call buys its whole gas limit.

The sender must then hold that fee. -/
def estimateGas (v : ChainView) (tx : GenericTransaction) (p : BlockParam) (c : CallChoices) :
    Except RpcError Nat := do
  -- The call prepared as for a call: a rejection fails the method, and the gas limit is set.
  let s ← v.prepareCall tx p c
  let hi := s.transaction.gas.toNat
  -- The call at that limit; a failure is the error of a call, the revert of code 3 included.
  let (_, o) ← v.runCall { tx with gas := some hi } p c
  let _ ← callAnswer o
  -- Then a binary search between 0 and that limit, EthLib's choice, as the source asks an estimate.
  return v.searchGas tx p c 0 hi

end ChainView

/-- The answer of `eth_createAccessList`: an access list, the gas used, and an error.

The schema makes all three optional, and the source fixes none of their contents. -/
structure AccessListResult where
  /-- The addresses and storage keys that the call accessed. -/
  accessList : List Access
  /-- The gas that the call with that access list uses, after its refund. -/
  gasUsed : Nat
  /-- The message of the error of `eth_call` for that call, absent when it completes. -/
  error : Option String

/-- The result of `eth_createAccessList` as JSON, without an error member when there is none. -/
def accessListResultJson (r : AccessListResult) : Json :=
  Json.mkObj <| [("accessList", accessListJson r.accessList), ("gasUsed", quantityJson r.gasUsed)]
    ++ (r.error.map fun e => ("error", Json.str e)).toList

/-- The addresses and storage keys that the call `s` read or wrote, with the output `o`.

The reads are those of the state tracker, which a revert keeps.

The fixture [`create-al-abi-revert.io`][abi-revert] asks for them when the call fails.

Its text asks the server to return the accessed slots regardless of failure.

An address without a storage key is left out when the transaction accesses it from the start.

Those are the sender, the recipient or the created contract, and the precompiles of the fork.

From Shapella, the beneficiary is one of them, as [EIP-3651][eip-3651] makes it warm.

The [text of the method][rules] names only the first three, and asks to keep every other address.

Whether it means to keep the beneficiary is an open question of the source.

The authorities and the delegate of EIP-7702 stay in.

So do the contracts that the code of the call creates.

[abi-revert]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/tests/eth_createAccessList/create-al-abi-revert.io
[eip-3651]: https://eips.ethereum.org/EIPS/eip-3651
[rules]: https://github.com/ethereum/execution-apis/blob/68d76a5b1c09dff023782d97eec6ce87a6f6505e/src/eth/execute.yaml#L122-L142
-/
def accessedList (s : CallSetup) (o : CallOutput) : List Access :=
  let state := o.state
  -- The keys read or written at each address; a revert keeps the reads.
  let keys := state.storageWrites.foldl
    (fun keys address slots => keys.insert address ((keys.getD address ∅).insertMany slots.keys))
    state.storageReads
  let addresses := (state.accountReads.insertMany state.accountWrites.keys).insertMany keys.keys
  -- Warm from the start by EIP-2929: the sender, the recipient or created contract, precompiles.
  --
  -- From Shapella the beneficiary too, by EIP-3651, which the text of the method does not name.
  let anyway := fun address =>
    address == s.sender || address == s.message.currentTarget ||
      (precompileAddresses s.fork).contains address ||
      (s.fork ≥ .shapella && address == s.env.coinbase)
  -- Such an address is left out unless it has a storage key.
  addresses.toList.filterMap fun address =>
    let slots := (keys.getD address ∅).toList
    if slots.isEmpty && anyway address then none else some ⟨address, slots⟩

/-- The gas that the call `s` uses, after its refund, when its message gave `o`. -/
def callGasUsed (s : CallSetup) (o : CallOutput) : Nat :=
  -- The gas used by the rule of a transaction, from its gas left with the reservoir and its refund.
  gasUsed s.fork s.sender s.transaction (o.gasLeft + o.reservoir) o.refund

/-- The message of the error that `eth_call` answers for the output `o`, or none for data. -/
def callErrorMessage (o : CallOutput) : Option String :=
  match callAnswer o with
  | .ok _ => none
  | .error e => some e.message

namespace ChainView

/-- The answer of `eth_createAccessList` for a request on the state after the block `p` names.

It runs the call, then runs it again with the addresses and keys it accessed.

The request then has an access list, so it runs again with type 1 or above.

Before Berlin no transaction has an access list, so the [text of the method][rules] rejects it.

The rejection has code -32000, the code of invalid input.

The gas used and the error are those of the last call.

When the call rejects the request before its message runs, the method fails with that rejection.

It also fails when the second call is rejected, such as when the gas no longer covers the list.

[rules]: https://github.com/ethereum/execution-apis/blob/68d76a5b1c09dff023782d97eec6ce87a6f6505e/src/eth/execute.yaml#L122-L142
-/
def createAccessList (v : ChainView) (tx : GenericTransaction) (p : BlockParam)
    (c : CallChoices) : Except RpcError AccessListResult := do
  -- The call as requested.
  let (s, o) ← v.runCall tx p c
  -- No access list before Berlin, by the text of the method: code -32000.
  ensure (.berlin ≤ s.fork) (callRuleError "no access list before Berlin")
  -- The addresses and keys it accessed.
  let accessList := accessedList s o
  -- The call again with that list; its gas used and its error are the answer.
  let (s, o) ← v.runCall { tx with accessList := some accessList } p c
  return { accessList, gasUsed := callGasUsed s o, error := callErrorMessage o }

end ChainView

end EthLib.Execution.Rpc
