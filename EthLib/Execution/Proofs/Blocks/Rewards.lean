module

public import EthLib.Execution.Blocks.Rewards
public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: the mining rewards

From Paris on, paying the rewards leaves the state unchanged.

Before Paris, creating ether adds exactly the amount to one account and leaves the others.

So when the beneficiaries are distinct, each gains exactly its reward, and nothing else changes.

When some beneficiaries coincide, each address gains the sum of its rewards.

Paying the rewards succeeds exactly when no balance would reach 2^256.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.State
open EthLib.Execution.State.TransactionState

/-- From Paris on, no reward is paid. -/
theorem payRewards_of_paris_le {fork : Fork} (h : .paris ≤ fork) (tx : TransactionState)
    (coinbase : Address) (number : Nat) (ommers : List (Address × Nat)) :
    payRewards fork tx coinbase number ommers = .ok tx := by
  simp [payRewards, h]

/-- Creating ether adds the amount to the account, and leaves every other account. -/
theorem createEther_eq_ok {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {amount : U256} (h : tx.createEther fork address amount = .ok tx') :
    (tx'.getAccount address).balance.toNat =
        (tx.getAccount address).balance.toNat + amount.toNat ∧
      ∀ other, other ≠ address → tx'.getAccount other = tx.getAccount other := by
  obtain ⟨account, hf, hread, hrest⟩ := modifyState_eq_ok h
  refine ⟨?_, hrest⟩
  rw [hread]
  unfold Account.credit at hf
  split at hf
  · rename_i hfit
    cases hf
    simp only [BitVec.toNat_add, Nat.mod_eq_of_lt hfit]
  · cases hf

/-- The miner's reward of a block with at most two ommers is below `2^256`. -/
theorem minerReward_lt {fork : Fork} {n : Nat} (hn : n ≤ 2) :
    minerReward fork n < 2 ^ 256 := by
  have hR : blockReward fork ≤ 5 * WEI_PER_ETHER := by
    unfold blockReward; split <;> (try split) <;> simp [WEI_PER_ETHER]
  simp only [minerReward, WEI_PER_ETHER] at *
  have : n * (blockReward fork / 32) ≤ 2 * blockReward fork := by
    calc n * (blockReward fork / 32) ≤ 2 * (blockReward fork / 32) := Nat.mul_le_mul_right _ hn
      _ ≤ 2 * blockReward fork := Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
  omega

/-- An ommer's reward is below `2^256`. -/
theorem ommerReward_lt (fork : Fork) (age : Nat) : ommerReward fork age < 2 ^ 256 := by
  have hR : blockReward fork ≤ 5 * WEI_PER_ETHER := by
    unfold blockReward; split <;> (try split) <;> simp [WEI_PER_ETHER]
  have : (8 - age) * blockReward fork / 8 ≤ blockReward fork := by
    apply Nat.div_le_of_le_mul
    exact Nat.mul_le_mul_right _ (show 8 - age ≤ 8 by omega)
  simp only [ommerReward, WEI_PER_ETHER] at *
  omega

/-- Paying the ommers' rewards to distinct beneficiaries credits each with its reward.

Every other account is left alone. -/
theorem foldlM_ommerRewards {fork : Fork} (number : Nat) :
    ∀ (ommers : List (Address × Nat)) (tx tx' : TransactionState),
      (ommers.map Prod.fst).Nodup →
      ommers.foldlM (fun tx (beneficiary, ommerNumber) => tx.createEther fork beneficiary
        (BitVec.ofNat 256 (ommerReward fork (number - ommerNumber)))) tx = .ok tx' →
      (∀ o ∈ ommers, (tx'.getAccount o.1).balance.toNat =
        (tx.getAccount o.1).balance.toNat + ommerReward fork (number - o.2)) ∧
      ∀ other, other ∉ ommers.map Prod.fst → tx'.getAccount other = tx.getAccount other := by
  intro ommers
  induction ommers with
  | nil =>
    intro tx tx' _ h
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp
  | cons o rest ih =>
    intro tx tx' hnd h
    simp only [List.foldlM, bind, Except.bind] at h
    obtain ⟨beneficiary, ommerNumber⟩ := o
    cases hstep : tx.createEther fork beneficiary
        (BitVec.ofNat 256 (ommerReward fork (number - ommerNumber))) with
    | error e => simp [hstep] at h
    | ok mid =>
      rw [hstep] at h
      obtain ⟨hcredit, hrest⟩ := createEther_eq_ok hstep
      have hnd' := List.nodup_cons.mp hnd
      obtain ⟨hall, hother⟩ := ih mid tx' hnd'.2 h
      have hlt := ommerReward_lt fork (number - ommerNumber)
      refine ⟨fun o ho => ?_, fun other hno => ?_⟩
      · rcases List.mem_cons.mp ho with rfl | ho
        · rw [hother _ hnd'.1, hcredit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
        · have hne : o.1 ≠ beneficiary := fun he => hnd'.1 (List.mem_map.mpr ⟨o, ho, he⟩)
          rw [hall o ho, hrest o.1 hne]
      · simp only [List.map_cons, List.mem_cons, not_or] at hno
        rw [hother other hno.2, hrest other hno.1]

/-- Before Paris, with at most two ommers and distinct beneficiaries, each gains its reward.

The miner gains its reward, and each ommer's beneficiary its own; every other account is unchanged.
-/
theorem payRewards_spec {fork : Fork} (h : fork < .paris) {tx tx' : TransactionState}
    {coinbase : Address} {number : Nat} {ommers : List (Address × Nat)}
    (hn : ommers.length ≤ 2) (hnd : (coinbase :: ommers.map Prod.fst).Nodup)
    (hp : payRewards fork tx coinbase number ommers = .ok tx') :
    (tx'.getAccount coinbase).balance.toNat =
        (tx.getAccount coinbase).balance.toNat + minerReward fork ommers.length ∧
      (∀ o ∈ ommers, (tx'.getAccount o.1).balance.toNat =
        (tx.getAccount o.1).balance.toNat + ommerReward fork (number - o.2)) ∧
      ∀ other, other ∉ coinbase :: ommers.map Prod.fst →
        tx'.getAccount other = tx.getAccount other := by
  have hnot : ¬ .paris ≤ fork := fun hle => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h hle)
  simp only [payRewards, hnot, ↓reduceIte, bind, Except.bind] at hp
  cases hmine : tx.createEther fork coinbase (BitVec.ofNat 256 (minerReward fork ommers.length))
    with
  | error e => simp [hmine] at hp
  | ok mid =>
    rw [hmine] at hp
    obtain ⟨hcredit, hrest⟩ := createEther_eq_ok hmine
    have hnd' := List.nodup_cons.mp hnd
    obtain ⟨hall, hother⟩ := foldlM_ommerRewards number ommers mid tx' hnd'.2 hp
    refine ⟨?_, fun o ho => ?_, fun other hno => ?_⟩
    · rw [hother coinbase hnd'.1, hcredit, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (minerReward_lt hn)]
    · have hne : o.1 ≠ coinbase := fun he => hnd'.1 (List.mem_map.mpr ⟨o, ho, he⟩)
      rw [hall o ho, hrest o.1 hne]
    · simp only [List.mem_cons, not_or] at hno
      rw [hother other hno.2, hrest other hno.1]

/-- The reward of an ommer, as a word, has the same value. -/
private theorem toNat_ommerReward (fork : Fork) (age : Nat) :
    (BitVec.ofNat 256 (ommerReward fork age)).toNat = ommerReward fork age := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (ommerReward_lt fork age)]

/-- Before Paris, with at most two ommers, each address gains the sum of its rewards.

The beneficiaries need not be distinct.

Every nonce and every code hash stays the same. -/
theorem getAccount_payRewards {fork : Fork} (h : fork < .paris) {tx tx' : TransactionState}
    {coinbase : Address} {number : Nat} {ommers : List (Address × Nat)}
    (hn : ommers.length ≤ 2) (hp : payRewards fork tx coinbase number ommers = .ok tx')
    (address : Address) :
    (tx'.getAccount address).balance.toNat = (tx.getAccount address).balance.toNat +
        (if coinbase = address then minerReward fork ommers.length else 0) +
        ((ommers.filter (·.1 = address)).map fun o => ommerReward fork (number - o.2)).sum ∧
      (tx'.getAccount address).nonce = (tx.getAccount address).nonce ∧
      (tx'.getAccount address).codeHash = (tx.getAccount address).codeHash := by
  have hnot : ¬ .paris ≤ fork := fun hle => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h hle)
  simp only [payRewards, hnot, ↓reduceIte, bind, Except.bind] at hp
  cases hmine : tx.createEther fork coinbase (BitVec.ofNat 256 (minerReward fork ommers.length))
    with
  | error e => simp [hmine] at hp
  | ok mid =>
    rw [hmine] at hp
    obtain ⟨hb, hnonce, hcode⟩ := getAccount_createEther hmine address
    obtain ⟨hb', hnonce', hcode'⟩ :=
      getAccount_foldlM_createEther _ _ ommers hp address
    refine ⟨?_, hnonce'.trans hnonce, hcode'.trans hcode⟩
    rw [hb', hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (minerReward_lt hn)]
    simp only [toNat_ommerReward]

/-- Before Paris, with at most two ommers, the rewards succeed exactly when no balance overflows.

A balance overflows when it would reach 2^256.

The balance of an address counts the sum of all its rewards. -/
theorem payRewards_isOk_iff {fork : Fork} (h : fork < .paris) {tx : TransactionState}
    {coinbase : Address} {number : Nat} {ommers : List (Address × Nat)}
    (hn : ommers.length ≤ 2) :
    (∃ tx', payRewards fork tx coinbase number ommers = .ok tx') ↔
      ∀ address, (tx.getAccount address).balance.toNat +
        (if coinbase = address then minerReward fork ommers.length else 0) +
        ((ommers.filter (·.1 = address)).map fun o => ommerReward fork (number - o.2)).sum <
          2 ^ 256 := by
  have hnot : ¬ .paris ≤ fork := fun hle => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h hle)
  have hminer := minerReward_lt (fork := fork) hn
  simp only [payRewards, hnot, ↓reduceIte, bind, Except.bind]
  cases hmine : tx.createEther fork coinbase (BitVec.ofNat 256 (minerReward fork ommers.length))
    with
  | error e =>
    simp only [reduceCtorEq, exists_false, false_iff, Classical.not_forall, Nat.not_lt]
    -- The reward of the block already overflows the balance of its beneficiary.
    have hover : ¬ (tx.getAccount coinbase).balance.toNat + minerReward fork ommers.length <
        2 ^ 256 := fun hfit => by
      obtain ⟨tx', hok⟩ := createEther_isOk_iff.mpr
        (by rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hminer])
      rw [hmine] at hok
      cases hok
    exact ⟨coinbase, by simp only [↓reduceIte]; omega⟩
  | ok mid =>
    simp only
    rw [foldlM_createEther_isOk_iff]
    refine forall_congr' fun address => ?_
    rw [(getAccount_createEther hmine address).1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hminer]
    simp only [toNat_ommerReward]

end EthLib.Execution.Blocks
