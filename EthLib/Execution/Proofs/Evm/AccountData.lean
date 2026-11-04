module

public import EthLib.Base.Proofs.Fork
public import EthLib.Execution.Evm.AccountData
public import EthLib.Execution.Proofs.Evm.Step

/-!
# Proofs: `Evm.AccountData`

From Berlin, an access is cold exactly when the transaction has not yet accessed the address.

The access warms the address, so a second access is warm.

Before Berlin, an access changes nothing.

BALANCE pays the price of its access, then pushes the balance of the account.

EXTCODEHASH gives 0 for an address with no account.

Each instruction exists exactly from the fork that adds its opcode.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256 toAddressMasked)
open EthLib.Execution.State (EMPTY_ACCOUNT)

variable {fork : Fork} {Meter : Type}

/-- Before Berlin, an access is warm and leaves the frame as it is. -/
theorem accessAddress_of_lt_berlin (h : fork < .berlin) (evm : Evm fork Meter) (a : Address) :
    accessAddress evm a = (false, evm) := by
  have : ¬fork ≥ .berlin := Nat.not_le_of_lt h
  simp [accessAddress, this]

/-- From Berlin, an access is cold exactly when the transaction has not accessed the address. -/
theorem accessAddress_fst (h : fork ≥ .berlin) (evm : Evm fork Meter) (a : Address) :
    (accessAddress evm a).1 = decide (a ∉ evm.substate.accessedAddresses) := by
  simp [accessAddress, h]

/-- From Berlin, an access adds the address to the accessed addresses. -/
theorem mem_accessAddress (h : fork ≥ .berlin) (evm : Evm fork Meter) (a : Address) :
    a ∈ (accessAddress evm a).2.substate.accessedAddresses := by
  simp [accessAddress, h]

/-- A second access to the same address is warm. -/
theorem accessAddress_accessAddress_fst (evm : Evm fork Meter) (a : Address) :
    (accessAddress (accessAddress evm a).2 a).1 = false := by
  by_cases h : fork ≥ .berlin
  · simp [accessAddress, h]
  · simp [accessAddress, h]

/-- An access keeps the message, the state and every part of the substate but its addresses. -/
theorem accessAddress_snd (evm : Evm fork Meter) (a : Address) :
    ∃ accessed, (accessAddress evm a).2 =
      { evm with substate := { evm.substate with accessedAddresses := accessed } } := by
  unfold accessAddress
  split
  · exact ⟨_, rfl⟩
  · exact ⟨evm.substate.accessedAddresses, rfl⟩

/-- BALANCE on an address word with room on the stack: access, pay, push the balance. -/
theorem balanceStep_cons [GasMeter Meter] {evm : Evm fork Meter} {word : U256} {rest : List U256}
    (h : evm.stack.val = word :: rest) :
    balanceStep evm =
      let accessed := accessAddress { evm with stack := ⟨rest, by
        have := evm.stack.property; rw [h] at this; simp at this; omega⟩ } (toAddressMasked word)
      (GasMeter.charge accessed.2.gas (balanceCost fork accessed.1)).map fun gas =>
        { accessed.2 with
          gas
          stack := ⟨(evm.state.getAccount (toAddressMasked word)).balance :: rest,
            by have := evm.stack.property; rw [h] at this; simpa using this⟩
          pc := evm.pc + 1 } := by
  have hstack : evm.stack = ⟨word :: rest, h ▸ evm.stack.property⟩ := Subtype.ext h
  have room : ¬(rest.length = STACK_LIMIT) := by
    have := evm.stack.property
    rw [h] at this
    simp only [List.length_cons] at this
    omega
  obtain ⟨accessed, hacc⟩ := accessAddress_snd
    { evm with stack := ⟨rest, by have := evm.stack.property; rw [h] at this; simp at this; omega⟩ }
    (toAddressMasked word)
  simp only [balanceStep, popWord, chargeGas, pushWord, advance, hstack, Stack.pop]
  simp only [bind, Except.bind, pure, Except.pure, hacc]
  rcases hc : GasMeter.charge _ _ with _ | _ <;> simp [Except.map, Stack.push, room]

/-- EXTCODEHASH reads 0 for an address with no account. -/
theorem codeHashWord_of_none {state : State.TransactionState} {a : Address}
    (h : state.getAccountOptional a = none) : codeHashWord (state.getAccount a) = 0 := by
  simp [codeHashWord, State.TransactionState.getAccount, h]

/-- EXTCODEHASH reads the code hash of an account that is not empty. -/
theorem codeHashWord_of_ne {account : State.Account} (h : account ≠ EMPTY_ACCOUNT) :
    codeHashWord account = U256.fromBeBytes account.codeHash := by
  simp [codeHashWord, h]

/-- An opcode that reads another account has an instruction exactly from the fork that adds it.

No other opcode has one. -/
theorem isSome_accountStep [GasMeter Meter] {op : Op} :
    (accountStep (Meter := Meter) fork op).isSome ↔
      op ∈ [.balance, .selfbalance, .extcodesize, .extcodecopy, .extcodehash] ∧
      op.since ≤ fork := by
  cases op <;> simp [accountStep, Op.since, Fork.frontier_le] <;> split <;> simp_all

end EthLib.Execution.Evm
