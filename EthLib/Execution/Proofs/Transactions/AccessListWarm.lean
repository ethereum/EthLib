module

public import EthLib.Execution.Proofs.Evm.Call.AccessesRun
public import EthLib.Execution.Proofs.Transactions.Authorization
public import EthLib.Execution.Proofs.Transactions.Process

/-!
# Proofs: the access list of a transaction stays warm in every frame of its message

From Berlin, the access list starts accessed, and every frame that the message reaches keeps it.

Sources:

- [EIP-2929, Specification][eip2929]: the price of a cold and of a warm access, and the revert.
- [EIP-2930, Specification][eip2930]: the access list starts accessed.

[eip2929]: https://eips.ethereum.org/EIPS/eip-2929#specification
[eip2930]: https://eips.ethereum.org/EIPS/eip-2930#specification
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The first frame of a transaction keeps every access of the substate it is given.

The authorities and a delegate only join the accessed addresses. -/
theorem accessesLe_prepareFirstFrame {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    substate.AccessesLe first.substate := by
  unfold prepareFirstFrame at h
  split at h
  -- A creation keeps the substate.
  · dsimp only at h
    split at h
    · split at h
      · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
        cases h
        exact .refl _
      · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
        cases h
        exact .refl _
    · obtain ⟨m, h, -⟩ := bind_ok_iff.mp h
      cases h
  -- A call takes the accessed addresses after the authorizations, with its delegate if any.
  · dsimp only at h
    obtain ⟨done, hdone, h⟩ := bind_ok_iff.mp h
    have grow : ∀ address, address ∈ substate.accessedAddresses → address ∈ done.accessed :=
      fun _ mem => mem_accessed_foldlM_applyAuthorization hdone mem
    generalize (if message.value ≠ 0 then _ else done.state) = read0 at h
    split at h <;>
    · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
      obtain ⟨code, -, h⟩ := bind_ok_iff.mp h
      generalize (if fork ≥ .pectra then delegatedAddress code else none) = delegate at h
      rcases delegate with _ | delegate
      · cases h
        exact ⟨grow, fun _ _ mem => mem⟩
      · dsimp only at h
        split at h <;>
        · obtain ⟨m', -, h⟩ := bind_ok_iff.mp h
          obtain ⟨code', -, h⟩ := bind_ok_iff.mp h
          cases h
          exact ⟨fun a mem => Std.ExtTreeSet.mem_insert.mpr (.inr (grow a mem)),
            fun _ _ mem => mem⟩

/-- Every frame that the message of a transaction reaches holds every access of a substate.

That substate is the one that its first frame is prepared from.

The message runs from that frame, as a call or as a creation. -/
theorem accessesLe_of_runReaches {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    {start : BurnStart fork Meter} {reached : Evm fork Meter}
    (prepared : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first)
    (starts : start = .call first.message first.state first.substate first.meter ∨
      start = .create first.message first.state first.substate first.meter)
    (reach : RunReaches fork Meter start reached) :
    substate.AccessesLe reached.substate := by
  refine (accessesLe_prepareFirstFrame prepared).trans ?_
  rcases starts with rfl | rfl <;> exact reach.accessesLe

/-- A storage key that the access list names is warm in every frame of the transaction's message.

So SLOAD and SSTORE price an access to it there as warm, at any depth and after any revert. -/
theorem accessStorageKey_fst_of_mem_accesses {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {coinbase sender target : Address} {tx : Transaction}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    {start : BurnStart fork Meter} {reached : Evm fork Meter} {access : Access} {key : Bytes32}
    (prepared : prepareFirstFrame (Meter := Meter) chainId message state
      (startSubstate fork coinbase sender target tx) auths paid = .ok first)
    (starts : start = .call first.message first.state first.substate first.meter ∨
      start = .create first.message first.state first.substate first.meter)
    (reach : RunReaches fork Meter start reached) (listed : access ∈ tx.accesses)
    (slot : key ∈ access.slots) :
    (accessStorageKey reached access.account key).1 = false := by
  by_cases hfork : .berlin ≤ fork
  · -- From Berlin the key starts accessed, and every reached frame keeps it.
    refine accessStorageKey_fst_of_mem
      ((accessesLe_of_runReaches prepared starts reach).storageKeys _ _ ?_)
    exact (mem_startAccessedStorageKeys hfork).mpr ⟨access, listed, rfl, slot⟩
  · -- Before Berlin no access is cold.
    rw [accessStorageKey_of_lt_berlin (Nat.lt_of_not_le hfork)]

/-- An address that the access list names is warm in every frame of the transaction's message.

So the instructions that read another account price an access to it there as warm. -/
theorem accessAddress_fst_of_mem_accesses {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {coinbase sender target : Address} {tx : Transaction}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    {start : BurnStart fork Meter} {reached : Evm fork Meter} {access : Access}
    (prepared : prepareFirstFrame (Meter := Meter) chainId message state
      (startSubstate fork coinbase sender target tx) auths paid = .ok first)
    (starts : start = .call first.message first.state first.substate first.meter ∨
      start = .create first.message first.state first.substate first.meter)
    (reach : RunReaches fork Meter start reached) (listed : access ∈ tx.accesses) :
    (accessAddress reached access.account).1 = false := by
  by_cases hfork : .berlin ≤ fork
  · -- From Berlin the address starts accessed, and every reached frame keeps it.
    exact accessAddress_fst_of_mem ((accessesLe_of_runReaches prepared starts reach).addresses _
      (access_mem_startAccessedAddresses hfork listed))
  · -- Before Berlin no access is cold.
    rw [accessAddress_of_lt_berlin (Nat.lt_of_not_le hfork)]

end EthLib.Execution.Transactions
