module

public import EthLib.Execution.Blocks.BlockAccessList
public import EthLib.Base.Proofs.BigEndian
public import EthLib.Serialization.Proofs.Rlp.Codec

/-!
# Proofs: block access lists

The RLP codec of a block access list is lawful.

So a list decodes from exactly one byte string, its encoding, and its hash commits to its value.

A list that passes the checks names each account once.

In each account, no storage key appears twice among the written and the read keys.

So the size rule counts the accounts and the distinct keys of each account.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Serialization.Rlp

/-! ## The codecs -/

instance : LawfulCodec StorageChange where
  ofItem_toItem c := by
    show StorageChange.ofItem (StorageChange.toItem c) = _
    simp only [StorageChange.ofItem, StorageChange.toItem, Item.fields, Item.toItems,
      List.length_cons, List.length_nil, ↓reduceIte, Item.readField_cons, bind, Except.bind,
      pure, Except.pure]
  toItem_of_ofItem {item c} hDecode := by
    change StorageChange.ofItem item = .ok c at hDecode
    unfold StorageChange.ofItem at hDecode
    obtain ⟨items, hFields, hDecode⟩ := bind_ok_iff.mp hDecode
    have hItem := Item.fields_eq_ok.mp hFields
    iterate 2
      obtain ⟨⟨_, _⟩, hRead, hDecode⟩ := bind_ok_iff.mp hDecode
      have := Item.eq_of_readField hRead
    obtain rfl := Except.ok.inj hDecode
    obtain ⟨rfl, hLen⟩ := hItem
    subst_vars
    simp at hLen
    subst hLen
    rfl

instance : LawfulCodec BalanceChange where
  ofItem_toItem c := by
    show BalanceChange.ofItem (BalanceChange.toItem c) = _
    simp only [BalanceChange.ofItem, BalanceChange.toItem, Item.fields, Item.toItems,
      List.length_cons, List.length_nil, ↓reduceIte, Item.readField_cons, bind, Except.bind,
      pure, Except.pure]
  toItem_of_ofItem {item c} hDecode := by
    change BalanceChange.ofItem item = .ok c at hDecode
    unfold BalanceChange.ofItem at hDecode
    obtain ⟨items, hFields, hDecode⟩ := bind_ok_iff.mp hDecode
    have hItem := Item.fields_eq_ok.mp hFields
    iterate 2
      obtain ⟨⟨_, _⟩, hRead, hDecode⟩ := bind_ok_iff.mp hDecode
      have := Item.eq_of_readField hRead
    obtain rfl := Except.ok.inj hDecode
    obtain ⟨rfl, hLen⟩ := hItem
    subst_vars
    simp at hLen
    subst hLen
    rfl

instance : LawfulCodec NonceChange where
  ofItem_toItem c := by
    show NonceChange.ofItem (NonceChange.toItem c) = _
    simp only [NonceChange.ofItem, NonceChange.toItem, Item.fields, Item.toItems,
      List.length_cons, List.length_nil, ↓reduceIte, Item.readField_cons, bind, Except.bind,
      pure, Except.pure]
  toItem_of_ofItem {item c} hDecode := by
    change NonceChange.ofItem item = .ok c at hDecode
    unfold NonceChange.ofItem at hDecode
    obtain ⟨items, hFields, hDecode⟩ := bind_ok_iff.mp hDecode
    have hItem := Item.fields_eq_ok.mp hFields
    iterate 2
      obtain ⟨⟨_, _⟩, hRead, hDecode⟩ := bind_ok_iff.mp hDecode
      have := Item.eq_of_readField hRead
    obtain rfl := Except.ok.inj hDecode
    obtain ⟨rfl, hLen⟩ := hItem
    subst_vars
    simp at hLen
    subst hLen
    rfl

instance : LawfulCodec CodeChange where
  ofItem_toItem c := by
    show CodeChange.ofItem (CodeChange.toItem c) = _
    simp only [CodeChange.ofItem, CodeChange.toItem, Item.fields, Item.toItems,
      List.length_cons, List.length_nil, ↓reduceIte, Item.readField_cons, bind, Except.bind,
      pure, Except.pure]
  toItem_of_ofItem {item c} hDecode := by
    change CodeChange.ofItem item = .ok c at hDecode
    unfold CodeChange.ofItem at hDecode
    obtain ⟨items, hFields, hDecode⟩ := bind_ok_iff.mp hDecode
    have hItem := Item.fields_eq_ok.mp hFields
    iterate 2
      obtain ⟨⟨_, _⟩, hRead, hDecode⟩ := bind_ok_iff.mp hDecode
      have := Item.eq_of_readField hRead
    obtain rfl := Except.ok.inj hDecode
    obtain ⟨rfl, hLen⟩ := hItem
    subst_vars
    simp at hLen
    subst hLen
    rfl

instance : LawfulCodec SlotChanges where
  ofItem_toItem c := by
    show SlotChanges.ofItem (SlotChanges.toItem c) = _
    simp only [SlotChanges.ofItem, SlotChanges.toItem, Item.fields, Item.toItems,
      List.length_cons, List.length_nil, ↓reduceIte, Item.readField_cons, bind, Except.bind,
      pure, Except.pure]
  toItem_of_ofItem {item c} hDecode := by
    change SlotChanges.ofItem item = .ok c at hDecode
    unfold SlotChanges.ofItem at hDecode
    obtain ⟨items, hFields, hDecode⟩ := bind_ok_iff.mp hDecode
    have hItem := Item.fields_eq_ok.mp hFields
    iterate 2
      obtain ⟨⟨_, _⟩, hRead, hDecode⟩ := bind_ok_iff.mp hDecode
      have := Item.eq_of_readField hRead
    obtain rfl := Except.ok.inj hDecode
    obtain ⟨rfl, hLen⟩ := hItem
    subst_vars
    simp at hLen
    subst hLen
    rfl

instance : LawfulCodec AccountChanges where
  ofItem_toItem c := by
    show AccountChanges.ofItem (AccountChanges.toItem c) = _
    simp only [AccountChanges.ofItem, AccountChanges.toItem, Item.fields, Item.toItems,
      List.length_cons, List.length_nil, ↓reduceIte, Item.readField_cons, bind, Except.bind,
      pure, Except.pure]
  toItem_of_ofItem {item c} hDecode := by
    change AccountChanges.ofItem item = .ok c at hDecode
    unfold AccountChanges.ofItem at hDecode
    obtain ⟨items, hFields, hDecode⟩ := bind_ok_iff.mp hDecode
    have hItem := Item.fields_eq_ok.mp hFields
    iterate 6
      obtain ⟨⟨_, _⟩, hRead, hDecode⟩ := bind_ok_iff.mp hDecode
      have := Item.eq_of_readField hRead
    obtain rfl := Except.ok.inj hDecode
    obtain ⟨rfl, hLen⟩ := hItem
    subst_vars
    simp at hLen
    subst hLen
    rfl

namespace BlockAccessList

/-- Two errors with one code come from one constructor. -/
theorem Error.code_injective (e₁ e₂ : Error) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [Error.code] at h; exact absurd h (by decide))

/-! ## The checks -/

/-- A list that passes the order test is in strictly ascending order. -/
theorem pairwise_of_ascending : ∀ {l : List Nat}, ascending l = true → l.Pairwise (· < ·)
  | [], _ => .nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [ascending, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_ascending h.2
    refine List.Pairwise.cons ?_ ih
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons ih hx)

/-- A list in strictly ascending order passes the order test. -/
theorem ascending_of_pairwise : ∀ {l : List Nat}, l.Pairwise (· < ·) → ascending l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
    simp only [ascending, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨List.rel_of_pairwise_cons h (List.mem_cons_self ..), ascending_of_pairwise h.of_cons⟩

/-- A list that passes the order test has no number twice. -/
theorem nodup_of_ascending {l : List Nat} (h : ascending l = true) : l.Nodup :=
  (pairwise_of_ascending h).imp Nat.ne_of_lt

/-- Two addresses with one number are equal. -/
theorem addressKey_injective : Function.Injective addressKey := by
  intro a b h
  apply Vector.toList_inj.mp
  have ha := natToBytes_bytesToNat a.toList
  have hb := natToBytes_bytesToNat b.toList
  simp only [Vector.length_toList] at ha hb
  rw [← ha, ← hb]
  exact congrArg _ h

/-- The address test passes exactly when the numbers of the addresses ascend. -/
theorem checkAddresses_eq_ok_iff (bal : BlockAccessList) :
    checkAddresses bal = .ok () ↔ ascending (bal.map (addressKey ·.address)) = true := by
  induction bal with
  | nil => simp [checkAddresses, ascending, pure, Except.pure]
  | cons a rest ih =>
    cases rest with
    | nil => simp [checkAddresses, ascending, pure, Except.pure]
    | cons b rest =>
      simp only [checkAddresses, List.map_cons, ascending, Bool.and_eq_true, decide_eq_true_eq]
      split
      · rename_i hlt
        simp only [List.map_cons] at ih
        simp [ih, hlt]
      · rename_i hlt
        simp [hlt]

/-- The checks of a list pass exactly when each of its three parts passes. -/
theorem check_eq_ok_iff (bal : BlockAccessList) (gasLimit : Nat) :
    check bal gasLimit = .ok () ↔ (∀ a ∈ bal, checkAccount a = .ok ()) ∧
      ascending (bal.map (addressKey ·.address)) = true ∧
      itemCount bal ≤ gasLimit / ITEM_COST := by
  simp only [check, bind_unit_ok_iff, forM_ok_iff, checkAddresses_eq_ok_iff, ensure_ok_iff]

/-- A list that passes the checks names each account once. -/
theorem nodup_addresses_of_check {bal : BlockAccessList} {gasLimit : Nat}
    (h : check bal gasLimit = .ok ()) : (bal.map (·.address)).Nodup := by
  have hKeys := nodup_of_ascending ((check_eq_ok_iff bal gasLimit).mp h).2.1
  rw [show bal.map (addressKey ·.address) = (bal.map (·.address)).map addressKey by
    simp [Function.comp_def]] at hKeys
  exact List.Pairwise.of_map addressKey (fun _ _ hne heq => hne (congrArg addressKey heq)) hKeys

/-- In an account that passes its checks, no key is written twice, read twice, or both. -/
theorem nodup_keys_of_checkAccount {a : AccountChanges} (h : checkAccount a = .ok ()) :
    (a.storageChanges.map (·.slot.toNat) ++ a.storageReads.map (·.toNat)).Nodup := by
  simp only [checkAccount, bind_unit_ok_iff, ensure_ok_iff, forM_ok_iff] at h
  obtain ⟨hSlots, -, hReads, hDisjoint, -⟩ := h
  refine List.nodup_append.mpr ⟨nodup_of_ascending hSlots, nodup_of_ascending hReads, ?_⟩
  intro x hx y hy hxy
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy
  have := hDisjoint r hr
  simp at this
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
  exact this s hs hxy

end BlockAccessList

end EthLib.Execution.Blocks
