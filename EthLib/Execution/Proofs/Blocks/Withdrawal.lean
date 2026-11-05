module

public import EthLib.Execution.Blocks.Withdrawal
public import EthLib.Execution.Proofs.State.Tracker
public import EthLib.Serialization.Proofs.Rlp.Codec

/-!
# Proofs: withdrawals

The RLP codec of a withdrawal is lawful.

So a withdrawal decodes from exactly one byte string, its encoding.

After the withdrawals of a block, each account holds its balance plus the wei withdrawn to it.

Its nonce and its code stay the same.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Serialization.Rlp

instance : LawfulCodec Withdrawal where
  ofItem_toItem w := by
    show Withdrawal.ofItem (Withdrawal.toItem w) = _
    simp only [Withdrawal.ofItem, Withdrawal.toItem, Item.fields, Item.toItems, List.length_cons,
      List.length_nil, ↓reduceIte, Item.readField_cons, bind, Except.bind, pure, Except.pure]
  toItem_of_ofItem {item w} hDecode := by
    change Withdrawal.ofItem item = .ok w at hDecode
    unfold Withdrawal.ofItem at hDecode
    obtain ⟨items, hFields, hDecode⟩ := bind_ok_iff.mp hDecode
    have hItem := Item.fields_eq_ok.mp hFields
    -- Each read takes the item of one field from the front of the rest.
    iterate 4
      obtain ⟨⟨_, _⟩, hRead, hDecode⟩ := bind_ok_iff.mp hDecode
      have := Item.eq_of_readField hRead
    obtain rfl := Except.ok.inj hDecode
    obtain ⟨rfl, hLen⟩ := hItem
    subst_vars
    -- The four fields fill the count, so no item is left.
    simp at hLen
    subst hLen
    rfl

open EthLib.Execution.State

/-- The wei that a list of withdrawals gives an address: the sum of its amounts, times `10^9`. -/
def withdrawnTo (withdrawals : List Withdrawal) (address : Address) : Nat :=
  ((withdrawals.filter (·.address = address)).map (·.amount.toNat)).sum * GWEI_TO_WEI

/-- The amount of a withdrawal in wei is below `2^256`, since its amount in Gwei is below `2^64`. -/
private theorem toNat_wei (amount : UInt64) :
    (BitVec.ofNat 256 (amount.toNat * GWEI_TO_WEI)).toNat = amount.toNat * GWEI_TO_WEI := by
  have hlt : amount.toNat * GWEI_TO_WEI < 2 ^ 64 * GWEI_TO_WEI :=
    Nat.mul_lt_mul_of_pos_right amount.toNat_lt (by decide)
  have hle : 2 ^ 64 * GWEI_TO_WEI ≤ 2 ^ 256 := by decide
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt hle)]

/-- Creating ether at one address adds it to that balance, and leaves nonces and code. -/
private theorem getAccount_createEther {fork : Fork} {tx tx' : TransactionState}
    {target : Address} {amount : U256} (h : tx.createEther fork target amount = .ok tx')
    (address : Address) :
    (tx'.getAccount address).balance.toNat = (tx.getAccount address).balance.toNat +
        (if target = address then amount.toNat else 0) ∧
      (tx'.getAccount address).nonce = (tx.getAccount address).nonce ∧
      (tx'.getAccount address).codeHash = (tx.getAccount address).codeHash := by
  obtain ⟨account, hf, hread, hother⟩ := TransactionState.modifyState_eq_ok h
  by_cases hsame : target = address
  · subst hsame
    rw [hread]
    split at hf
    · rename_i hfit
      cases hf
      simp only [↓reduceIte, BitVec.toNat_add, Nat.mod_eq_of_lt hfit, and_self]
    · cases hf
  · rw [hother address (Ne.symm hsame)]
    simp [hsame]

/-- Each step of the withdrawals adds the wei of its address, and leaves nonce and code. -/
private theorem getAccount_foldlM_createEther (fork : Fork) {wei : Withdrawal → U256}
    (hwei : ∀ w, (wei w).toNat = w.amount.toNat * GWEI_TO_WEI) (withdrawals : List Withdrawal) :
    ∀ {tx tx' : TransactionState},
      withdrawals.foldlM (fun tx w => tx.createEther fork w.address (wei w)) tx = .ok tx' →
      ∀ address, (tx'.getAccount address).balance.toNat =
          (tx.getAccount address).balance.toNat + withdrawnTo withdrawals address ∧
        (tx'.getAccount address).nonce = (tx.getAccount address).nonce ∧
        (tx'.getAccount address).codeHash = (tx.getAccount address).codeHash := by
  induction withdrawals with
  | nil =>
    intro tx tx' h address
    cases h
    simp [withdrawnTo]
  | cons w rest ih =>
    intro tx tx' h address
    rw [List.foldlM_cons] at h
    cases hmid : tx.createEther fork w.address (wei w) with
    | error e =>
      rw [hmid] at h
      cases h
    | ok mid =>
      rw [hmid] at h
      obtain ⟨hb, hn, hc⟩ := getAccount_createEther hmid address
      obtain ⟨hb', hn', hc'⟩ := ih h address
      refine ⟨?_, hn'.trans hn, hc'.trans hc⟩
      rw [hb', hb, hwei]
      by_cases hsame : w.address = address
      · simp only [withdrawnTo, hsame, ↓reduceIte, List.filter_cons, decide_true,
          List.map_cons, List.sum_cons, Nat.add_mul]
        omega
      · simp only [withdrawnTo, hsame, ↓reduceIte, List.filter_cons, decide_false,
          Bool.false_eq_true, Nat.add_zero]

/-- After the withdrawals of a block, each account holds its balance plus its withdrawn wei.

Its nonce and its code hash stay the same, and an address with no withdrawal keeps its balance. -/
theorem getAccount_processWithdrawals {fork : Fork} {block block' : BlockState}
    {withdrawals : List Withdrawal} (h : processWithdrawals fork block withdrawals = .ok block')
    (address : Address) :
    ((TransactionState.ofBlock block').getAccount address).balance.toNat =
        ((TransactionState.ofBlock block).getAccount address).balance.toNat +
          withdrawnTo withdrawals address ∧
      ((TransactionState.ofBlock block').getAccount address).nonce =
        ((TransactionState.ofBlock block).getAccount address).nonce ∧
      ((TransactionState.ofBlock block').getAccount address).codeHash =
        ((TransactionState.ofBlock block).getAccount address).codeHash := by
  simp only [processWithdrawals, withdrawalState, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i tx htx
    cases h
    -- The block after the withdrawals reads its accounts as the last step does.
    have hread : (TransactionState.ofBlock tx.incorporateTxIntoBlock.parent).getAccount address =
        tx.getAccount address := by
      unfold TransactionState.getAccount
      rw [← TransactionState.getAccountOptional_incorporateTxIntoBlock tx address]
      rfl
    rw [hread]
    exact getAccount_foldlM_createEther fork (fun w => toNat_wei w.amount) withdrawals htx address

end EthLib.Execution.Blocks
