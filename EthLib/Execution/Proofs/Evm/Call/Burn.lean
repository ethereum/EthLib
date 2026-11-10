module

public import EthLib.Execution.Proofs.Evm.Call.Supply

/-!
# Proofs: the ether burned by the writes of a message

A burn log records SELFDESTRUCT and the rollback of failed frames.

Its total counts only burns that survive every enclosing rollback.

The burn formula reads the SELFDESTRUCT operands and its starting balance.

[EIP-6780, Specification][e6780] defines the self-beneficiary burn from Cancun.

[EIP-8246, Specification][e8246] removes that burn from Glamsterdam.

The [Yellow Paper][yp], Shanghai version, section 8, equations 127 and 129, defines the rollback.

Its Appendix H.2 defines the earlier SELFDESTRUCT.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[e6780]: https://eips.ethereum.org/EIPS/eip-6780#specification
[e8246]: https://eips.ethereum.org/EIPS/eip-8246#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256)
open EthLib.Execution.State (TransactionState)

/-- The wei lost by SELFDESTRUCT's balance transfer, before any enclosing rollback. -/
def selfdestructBurn (fork : Fork) (tx : TransactionState) (originator beneficiary : Address) :
    Nat :=
  if originator = beneficiary ∧
      (fork < .dencun ∨ (fork < .glamsterdam ∧ originator ∈ tx.createdAccounts)) then
    tx.balanceOf originator
  else 0

/-- The balance transfer of SELFDESTRUCT loses exactly its self-beneficiary burn. -/
theorem supply_selfdestructTransfer {fork : Fork} {tx tx' : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    tx'.supply + selfdestructBurn fork tx originator beneficiary = tx.supply := by
  unfold selfdestructTransfer at h
  split at h
  · rename_i hdencun
    obtain ⟨mid, hm, h⟩ := Base.bind_ok_iff.mp h
    have moved := TransactionState.supply_moveEther hm
    have created := TransactionState.createdAccounts_moveEther hm
    split at h
    · rename_i hburn
      have hs := TransactionState.supply_setAccountBalance h
      have hzero : (0 : U256).toNat = 0 := rfl
      rw [hzero] at hs
      by_cases same : originator = beneficiary
      · subst same
        have balance := (TransactionState.moveEther_self hm).1
        simp only [selfdestructBurn, true_and, created ▸ hburn, or_true, ↓reduceIte]
        unfold TransactionState.balanceOf at hs ⊢
        rw [balance] at hs
        omega
      · obtain ⟨-, -, balance, -⟩ := TransactionState.moveEther_eq_ok same hm
        have hb : mid.balanceOf originator = 0 := by
          unfold TransactionState.balanceOf
          rw [balance, BitVec.sub_self]
          rfl
        simp only [selfdestructBurn, same, false_and, ↓reduceIte]
        omega
    · rename_i hburn
      cases h
      have notBurn : ¬(originator = beneficiary ∧
          (fork < .dencun ∨ (fork < .glamsterdam ∧ originator ∈ tx.createdAccounts))) := by
        rintro ⟨-, hlt | hcreated⟩
        · exact Nat.not_lt_of_ge hdencun hlt
        · exact hburn (created ▸ hcreated)
      simp only [selfdestructBurn, notBurn, ↓reduceIte, Nat.add_zero]
      exact moved
  · rename_i hdencun
    obtain ⟨mid, hm, h⟩ := Base.bind_ok_iff.mp h
    have added := TransactionState.supply_createEther hm
    have hs := TransactionState.supply_setAccountBalance h
    have balance := (TransactionState.getAccount_createEther hm originator).1
    have hzero : (0 : U256).toNat = 0 := rfl
    rw [hzero] at hs
    unfold TransactionState.balanceOf at hs
    rw [balance] at hs
    by_cases same : originator = beneficiary
    · subst same
      simp only [selfdestructBurn, true_and,
        (show fork < .dencun from Nat.lt_of_not_ge hdencun), true_or, ↓reduceIte]
      simp only [↓reduceIte] at hs
      unfold TransactionState.balanceOf
      omega
    · simp only [selfdestructBurn, same, false_and, ↓reduceIte]
      simp only [Ne.symm same, ↓reduceIte] at hs
      omega

/-- A log of burns, their composition, and the discarded log of a rollback. -/
inductive BurnLog where
  | empty
  | selfdestruct (originator beneficiary : Address) (amount : Nat)
  | append (first second : BurnLog)
  | rollback (discarded : BurnLog)

/-- The wei of the log that survive its rollbacks. -/
def BurnLog.total : BurnLog → Nat
  | .empty => 0
  | .selfdestruct _ _ amount => amount
  | .append first second => first.total + second.total
  | .rollback _ => 0

end EthLib.Execution.Evm
