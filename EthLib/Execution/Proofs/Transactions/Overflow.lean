module

public import EthLib.Execution.Proofs.Transactions.Unfold
public import EthLib.Execution.Proofs.Evm.Call.Overflow
public import EthLib.Execution.Proofs.Transactions.Supply
import EthLib.Execution.Proofs.Transactions.Inclusion

/-!
# Proofs: no transaction overflows a balance when the supply leaves room

A transaction that passes its checks, on a supply with room, never fails for a balance overflow.

A supply leaves room when it is below `2^256`, or twice it is before Cancun.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base (Address Fork)
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState TransactionState)

section

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- A read of code never fails for a balance that would overflow. -/
theorem getCode_ne_balanceOverflow (state : TransactionState) (codeHash : Base.Hash32)
    (address : Address) : state.getCode codeHash ≠ .error (.balanceOverflow address) :=
  fun h => by cases State.TransactionState.error_getCode h

/-- A credit of ether never overflows a balance when the supply plus the credit is below `2^256`. -/
private theorem creditEther_ne_balanceOverflow {state : TransactionState}
    {address : Address} {amount : Nat} (fits : state.supply + amount < 2 ^ 256)
    (other : Address) :
    creditEther fork state address amount ≠ .error (.balanceOverflow other) := by
  unfold creditEther
  split
  · rename_i hlt
    refine State.TransactionState.createEther_ne_balanceOverflow ?_ other
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    exact fits
  · omega

/-- The settlement never overflows a balance when the supply plus both credits is below `2^256`. -/
private theorem settleGas_ne_balanceOverflow {env : BlockEnvironment fork}
    {state : TransactionState} {sender : Address} {tx : Transaction} {gasLeft refund : Nat}
    (fits : state.supply +
      (settlement fork (baseFeeOf env) sender tx gasLeft refund).senderRefund +
      (settlement fork (baseFeeOf env) sender tx gasLeft refund).priorityFee < 2 ^ 256)
    (other : Address) :
    settleGas env state sender tx gasLeft refund ≠ .error (.balanceOverflow other) := by
  intro he
  unfold settleGas at he
  rw [paidBaseFee_empty] at he
  rcases Base.bind_eq_error he with he | ⟨mid, hmid, he⟩
  · exact creditEther_ne_balanceOverflow (by omega) _ he
  have hsupply := (supply_creditEther hmid).1
  rcases Base.bind_eq_error he with he | ⟨paid, -, he⟩
  · unfold payBeneficiary at he
    split at he
    · cases he
    · exact creditEther_ne_balanceOverflow (by omega) _ he
  · cases he

/-- The message of a transaction never overflows a balance when its start supply leaves room. -/
theorem processMessageCall_ne_balanceOverflow [LawfulGasMeter Meter]
    {chainId : Nat} {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address}
    (room : SupplyRoom fork state.supply) (address : Address) :
    processMessageCall (Meter := Meter) chainId message state substate auths paid ≠
      .error (.state (.balanceOverflow address)) := by
  intro h
  rw [processMessageCall_unfold] at h
  rcases hprep : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid
    with ⟨e, read⟩ | first
  · rw [hprep] at h
    dsimp only at h
    split at h
    · cases h
      exact prepareFirstFrame_ne_state (fun _ h => by cases h) read hprep
    · cases h
  · rw [hprep] at h
    dsimp only at h
    -- The authorizations keep every balance.
    have froom : SupplyRoom fork first.state.supply := by
      rwa [supply_prepareFirstFrame hprep]
    -- No call or creation overflows a balance when the supply it starts with leaves room.
    split at h
    · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
      · exact processCreateMessage_ne_balanceOverflow froom address h
      · cases h
    · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
      · exact processMessage_ne_balanceOverflow froom address h
      · cases h

/-- A run of a transaction never overflows a balance when the supply before it leaves room.

Its gas limit must cover the least gas, and its price must cover the base fee. -/
private theorem runTransaction_ne_balanceOverflow [LawfulGasMeter Meter]
    {env : BlockEnvironment fork} {block : BlockState} {included : Included} {tx : Transaction}
    (hMin : minimumGas fork included.sender tx ≤ tx.gas.toNat)
    (hPrice : baseFeeOf env ≤ effectiveGasPrice (baseFeeOf env) tx)
    (room : SupplyRoom fork (TransactionState.ofBlock block).supply) (address : Address) :
    runTransaction Meter env block included tx ≠ .error (.state (.balanceOverflow address)) := by
  intro h
  rw [runTransaction_unfold] at h
  rcases Base.bind_eq_error h with h | ⟨target, -, h⟩
  · unfold messageTarget at h
    split at h
    · cases h
    · unfold Except.mapError at h
      split at h <;> cases h
  -- The sender first pays the fee for the whole gas limit and the blob gas.
  rcases Base.bind_eq_error h with h | ⟨bought, hbought, h⟩
  · unfold Except.mapError at h
    split at h
    · rename_i he'
      cases h
      cases error_buyGas he'
    · cases h
  have hbought := Base.mapError_ok_iff.mp hbought
  have hbuy := (supply_buyGas hbought).1
  rcases Base.bind_eq_error h with h | ⟨message, -, h⟩
  · unfold transactionMessage at h
    split at h
    · dsimp only at h
      generalize hx : Except.mapError EvmError.state _ = x at h
      cases x with
      | error e' =>
        cases h
        unfold Except.mapError at hx
        split at hx
        · rename_i he'
          cases hx
          exact getCode_ne_balanceOverflow _ _ _ he'
        · cases hx
      | ok _ => cases h
    · cases h
  rcases Base.bind_eq_error h with h | ⟨output, houtput, h⟩
  -- So the first message starts with at most the supply before the transaction.
  · exact processMessageCall_ne_balanceOverflow (room.mono (by omega)) address h
  have hended := (supplyLe_processMessageCall houtput).1
  rcases Base.bind_eq_error h with h | ⟨⟨settled, used⟩, -, h⟩
  · unfold Except.mapError at h
    split at h
    · rename_i he'
      cases h
      -- The settlement credits the refund of the sender and the priority fee of the beneficiary.
      refine settleGas_ne_balanceOverflow ?_ _ he'
      -- Those two add up to at most the fee that the sender paid.
      --
      -- So each credit raises one balance to at most the supply before the transaction.
      have conserve := settlement_conserves hMin hPrice
        (output.gasLeft + output.reservoir) output.refund
      have := room.lt
      dsimp only at conserve
      omega
    · cases h
  rcases Base.bind_eq_error h with h | ⟨deleted, -, h⟩
  · unfold Except.mapError at h
    split at h
    · rename_i he'
      cases h
      -- The deletions at the end credit nothing.
      exact deleteAccounts_ne_error _ _ _ he'
    · cases h
  · cases h

end

/-- No transaction fails with the state error for a balance that would overflow.

It must pass its checks on the block state it runs on.

The supply of that state must leave room for the credits of a message. -/
theorem processTransaction_ne_balanceOverflow {fork : Fork} {env : BlockEnvironment fork}
    {block : BlockState} {chainId : UInt64} {used : BlockGas} {tx : Transaction}
    {included : Included}
    (checked : checkInclusion chainId env used (.ofBlock block) tx = .ok included)
    (room : SupplyRoom fork (TransactionState.ofBlock block).supply) (address : Address) :
    processTransaction env block included tx ≠ .error (.state (.balanceOverflow address)) := by
  obtain ⟨-, valid, -, -, -, fee, -⟩ := checkInclusion_ok checked
  have hMin := (validateTransaction_ok valid).2.1
  have hPrice := le_effectiveGasPrice fee
  rw [processTransaction_unfold]
  split
  · nofun
  split
  · exact runTransaction_ne_balanceOverflow hMin hPrice room address
  · exact runTransaction_ne_balanceOverflow hMin hPrice room address

end EthLib.Execution.Transactions
