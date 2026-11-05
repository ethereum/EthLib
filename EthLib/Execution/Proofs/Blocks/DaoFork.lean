module

public import EthLib.Execution.Blocks.DaoFork
public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: the DAO Fork

The list holds 116 distinct accounts, and the recovery contract is not among them.

After the fork every listed account holds no ether, and the recovery contract holds their ether.

Every other account is unchanged, so the fork creates and destroys no ether.

On mainnet, blocks 1,920,000 to 1,920,009 must carry the fork's extra data.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.State
open EthLib.Execution.State.TransactionState

/-- The list holds 116 accounts. -/
theorem length_daoAccounts : DAO_ACCOUNTS.length = 116 := rfl

/-- No account appears twice in the list. -/
theorem daoAccounts_nodup : DAO_ACCOUNTS.Nodup := by decide +kernel

/-- The recovery contract is not in the list, so no account sends ether to itself. -/
theorem daoRecovery_not_mem : DAO_RECOVERY ∉ DAO_ACCOUNTS := by decide

/-- The ether that some accounts hold, in wei. -/
def balanceSum (tx : TransactionState) (addresses : List Address) : Nat :=
  (addresses.map fun a => (tx.getAccount a).balance.toNat).sum

/-- Moving a whole balance empties the sender and credits the recipient with it. -/
theorem moveEther_whole {fork : Fork} {tx tx' : TransactionState} {sender recipient : Address}
    (hne : sender ≠ recipient)
    (h : tx.moveEther fork sender recipient (tx.getAccount sender).balance = .ok tx') :
    (tx'.getAccount sender).balance = 0 ∧
      (tx'.getAccount recipient).balance.toNat =
        (tx.getAccount recipient).balance.toNat + (tx.getAccount sender).balance.toNat ∧
      ∀ other, other ≠ sender → other ≠ recipient →
        tx'.getAccount other = tx.getAccount other := by
  obtain ⟨-, hfit, hsender, hrecipient, hrest⟩ := moveEther_eq_ok hne h
  -- The sender's balance minus itself is zero, and the credit stays below 2^256.
  refine ⟨by rw [hsender]; exact BitVec.sub_self _, ?_, hrest⟩
  rw [hrecipient, BitVec.toNat_add, Nat.mod_eq_of_lt hfit]

/-- Moving each listed balance to an outside recipient empties the list and credits the recipient.

Every other account is left alone. -/
theorem foldlM_moveEther {fork : Fork} (recipient : Address) :
    ∀ (l : List Address) (tx tx' : TransactionState), l.Nodup → recipient ∉ l →
      l.foldlM (fun tx a => tx.moveEther fork a recipient (tx.getAccount a).balance) tx = .ok tx' →
      (∀ a ∈ l, (tx'.getAccount a).balance = 0) ∧
        (tx'.getAccount recipient).balance.toNat =
          (tx.getAccount recipient).balance.toNat + balanceSum tx l ∧
        ∀ other, other ∉ l → other ≠ recipient → tx'.getAccount other = tx.getAccount other := by
  intro l
  induction l with
  | nil =>
    intro tx tx' _ _ h
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [balanceSum]
  | cons a l ih =>
    intro tx tx' hnd hr h
    simp only [List.foldlM, bind, Except.bind] at h
    have hne : a ≠ recipient := fun he => hr (he ▸ List.mem_cons_self)
    cases hstep : tx.moveEther fork a recipient (tx.getAccount a).balance with
    | error e => simp [hstep] at h
    | ok mid =>
      rw [hstep] at h
      obtain ⟨hzero, hcredit, hrest⟩ := moveEther_whole hne hstep
      have hnd' := (List.nodup_cons.mp hnd)
      obtain ⟨hall, hrec, hother⟩ :=
        ih mid tx' hnd'.2 (fun hm => hr (List.mem_cons_of_mem _ hm)) h
      -- The rest of the list reads the same balances before and after the first move.
      have hsame : balanceSum mid l = balanceSum tx l := by
        unfold balanceSum
        congr 1
        apply List.map_congr_left
        intro b hb
        rw [hrest b (fun he => hnd'.1 (he ▸ hb)) (fun he => hr (he ▸ List.mem_cons_of_mem _ hb))]
      refine ⟨fun b hb => ?_, ?_, fun other hno hrc => ?_⟩
      · rcases List.mem_cons.mp hb with rfl | hb
        · rw [hother b hnd'.1 hne, hzero]
        · exact hall b hb
      · rw [hrec, hcredit, hsame]
        simp only [balanceSum, List.map_cons, List.sum_cons]
        omega
      · rw [hother other (fun hm => hno (List.mem_cons_of_mem _ hm)) hrc,
          hrest other (fun he => hno (he ▸ List.mem_cons_self)) hrc]

/-- After the DAO Fork the listed accounts hold no ether, and the recovery contract holds it.

Every other account is unchanged. -/
theorem applyDaoFork_spec {fork : Fork} {tx tx' : TransactionState}
    (h : applyDaoFork fork tx = .ok tx') :
    (∀ a ∈ DAO_ACCOUNTS, (tx'.getAccount a).balance = 0) ∧
      (tx'.getAccount DAO_RECOVERY).balance.toNat =
        (tx.getAccount DAO_RECOVERY).balance.toNat + balanceSum tx DAO_ACCOUNTS ∧
      ∀ other, other ∉ DAO_ACCOUNTS → other ≠ DAO_RECOVERY →
        tx'.getAccount other = tx.getAccount other :=
  foldlM_moveEther DAO_RECOVERY DAO_ACCOUNTS tx tx' daoAccounts_nodup daoRecovery_not_mem h

/-- Mainnet activates the DAO Fork at block 1,920,000. -/
theorem daoForkBlock_mainnet : daoForkBlock ChainConfig.mainnet = some 1920000 := rfl

/-- On mainnet, a header in blocks 1,920,000 to 1,920,009 passes exactly with the fork's extra data.

Every other header passes. -/
theorem daoExtraDataValid_mainnet {fork : Fork} (header : Header fork) :
    daoExtraDataValid ChainConfig.mainnet header = true ↔
      (1920000 ≤ header.number ∧ header.number < 1920010 → header.extraData = DAO_EXTRA_DATA) := by
  simp only [daoExtraDataValid, daoForkBlock_mainnet, DAO_EXTRA_DATA_BLOCKS, Nat.reduceAdd]
  by_cases h : 1920000 ≤ header.number ∧ header.number < 1920010 <;> simp [h]

end EthLib.Execution.Blocks
