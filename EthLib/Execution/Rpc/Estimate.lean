module

public import EthLib.Execution.Rpc.Call

/-!
# `Execution.Rpc.Estimate`

The methods `eth_estimateGas` and `eth_createAccessList` of [`execute.yaml`][execute].

Both take the request and the block parameter of `eth_call`, and run its call the same way.

The block parameter is optional, and `latest` by default.

Of the three methods, only `eth_call` states that default, and the other two follow it.

A call completes when it prepares and its message ends without an error.

The source asks `eth_estimateGas` for an estimate, and nothing more.

Its text reads "an estimate of how much gas is necessary to allow the transaction to complete".

Here the answer is a gas limit with which the call completes.

The method first runs the call at the gas limit of the request, or the default one.

If that call fails, the method fails with the same error as `eth_call`.

That includes the revert of code 3.

Otherwise it searches by halves, between 0 and that limit, for a limit that completes.

The answer always completes.

It is the least positive limit that completes when those limits form an interval.

Code that reads the gas left can break that, and the answer may then not be the least.

The answer of `eth_createAccessList` is an object with an access list, the gas used, and an error.

The schema makes all three optional, and the source fixes none of their contents.

Here the access list holds each address and storage key that the call read or wrote.

An address without a storage key is left out when its transaction accesses it from the start.

Those are the sender, the recipient or the created contract, and the precompiles of the fork.

From Shapella, the beneficiary is one of them.

The authorities and the delegate of EIP-7702, and the contracts that the call creates, stay in.

The reads are those of the state tracker, which a revert keeps.

The fixture [`create-al-abi-revert.io`][abi-revert] asks for them when the call fails.

Its text reads "The server should return the accessed slots regardless of failure".

The method then runs the call again with that access list, and reports its gas used and its error.

A request of type 0 runs again as type 1, the first type with an access list.

Before Berlin no transaction has an access list, so the list is empty and the call runs once.

The gas used is the gas that the transaction would use, after its refund.

The error is absent when that call completes, and else the message of the error of `eth_call`.

A request that the call rejects before its message runs gets that error, as for `eth_call`.

So does a request whose second call is rejected, such as one whose gas no longer covers the list.

The estimate has no cap from EIP-7825, as the call has none.

With a fee named, the first call buys its whole gas limit, so the sender must hold that fee.

[execute]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/eth/execute.yaml
[abi-revert]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/tests/eth_createAccessList/create-al-abi-revert.io
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Evm
open EthLib.Execution.Transactions

namespace ChainView

/-- The call with gas limit `g` completes: it prepares, and its message neither reverts nor halts.
-/
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

/-- A gas limit up to `hi`, found by halves above `lo`.

The answer is `hi` or a limit with which the call completes.

It is the least such limit when the limits that complete form an interval. -/
def searchGas (v : ChainView) (tx : GenericTransaction) (p : BlockParam) (c : CallChoices)
    (lo hi : Nat) : Nat :=
  if lo + 1 < hi then
    let mid := (lo + hi) / 2
    if v.Completes tx p c mid then v.searchGas tx p c lo mid else v.searchGas tx p c mid hi
  else hi
termination_by hi - lo

/-- The answer of `eth_estimateGas`: a gas limit with which the call completes.

It fails with the error of the call at the gas limit of the request, or at the default one. -/
def estimateGas (v : ChainView) (tx : GenericTransaction) (p : BlockParam) (c : CallChoices) :
    Except RpcError Nat := do
  let s ← v.prepareCall tx p c
  let hi := s.transaction.gas.toNat
  let (_, o) ← v.runCall { tx with gas := some hi } p c
  let _ ← callAnswer o
  return v.searchGas tx p c 0 hi

end ChainView

/-- The answer of `eth_createAccessList`: an access list, the gas used, and an error. -/
structure AccessListResult where
  /-- The addresses and storage keys that the call accessed. -/
  accessList : List Access
  /-- The gas that the call with that access list uses, after its refund. -/
  gasUsed : Nat
  /-- The message of the error of that call, if it fails. -/
  error : Option String

/-- The result of `eth_createAccessList` as JSON, without `error` when there is none. -/
def accessListResultJson (r : AccessListResult) : Json :=
  Json.mkObj <| [("accessList", accessListJson r.accessList), ("gasUsed", quantityJson r.gasUsed)]
    ++ (r.error.map fun e => ("error", Json.str e)).toList

/-- The addresses and storage keys that the call `s` read or wrote, with the output `o`.

An address without a storage key is left out when the transaction accesses it anyway. -/
def accessedList (s : CallSetup) (o : CallOutput) : List Access :=
  let state := o.state
  let keys := state.storageWrites.foldl
    (fun keys address slots => keys.insert address ((keys.getD address ∅).insertMany slots.keys))
    state.storageReads
  let addresses := (state.accountReads.insertMany state.accountWrites.keys).insertMany keys.keys
  let anyway := fun address =>
    address == s.sender || address == s.message.currentTarget ||
      (precompileAddresses s.fork).contains address ||
      (s.fork ≥ .shapella && address == s.env.coinbase)
  addresses.toList.filterMap fun address =>
    let slots := (keys.getD address ∅).toList
    if slots.isEmpty && anyway address then none else some ⟨address, slots⟩

/-- The gas that the call `s` uses, after its refund, when its message gave `o`. -/
def callGasUsed (s : CallSetup) (o : CallOutput) : Nat :=
  gasUsed s.fork s.sender s.transaction (o.gasLeft + o.reservoir) o.refund

/-- The message of the error that `eth_call` answers for the output `o`, or none for data. -/
def callErrorMessage (o : CallOutput) : Option String :=
  match callAnswer o with
  | .ok _ => none
  | .error e => some e.message

namespace ChainView

/-- The answer of `eth_createAccessList` for a request on the state after the block `p` names. -/
def createAccessList (v : ChainView) (tx : GenericTransaction) (p : BlockParam)
    (c : CallChoices) : Except RpcError AccessListResult := do
  let (s, o) ← v.runCall tx p c
  if s.fork < .berlin then
    return { accessList := [], gasUsed := callGasUsed s o, error := callErrorMessage o }
  let accessList := accessedList s o
  let again := { tx with accessList := some accessList
                         type := if tx.kind = 0 then some 1 else tx.type }
  let (s, o) ← v.runCall again p c
  return { accessList, gasUsed := callGasUsed s o, error := callErrorMessage o }

end ChainView

end EthLib.Execution.Rpc
