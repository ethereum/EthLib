module

public import EthLib.Execution.Blocks.AccessListBuilder
public import EthLib.Execution.Proofs.Blocks.BlockAccessList
public import EthLib.Base.Proofs.U256

/-!
# Proofs: the builder of a block access list

Every list that the builder gives passes the order and uniqueness checks of EIP-7928.

So each account appears once, and no key of an account is both read and written.

A write that leaves a value as its position found it records no change at that position.

It keeps the changes of the other positions.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open BlockAccessList

/-! ## Sorted lists -/

/-- A list sorted by a key, whose keys are distinct, has strictly ascending keys. -/
theorem pairwise_lt_mergeSort {α : Type} (key : α → Nat) {l : List α}
    (distinct : (l.map key).Nodup) :
    ((l.mergeSort fun a b => key a ≤ key b).map key).Pairwise (· < ·) := by
  have sorted := List.pairwise_mergeSort (le := fun a b => decide (key a ≤ key b))
    (fun _ _ _ h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  have nodup : ((l.mergeSort fun a b => key a ≤ key b).map key).Nodup :=
    ((List.mergeSort_perm l _).map key).nodup_iff.mpr distinct
  rw [List.pairwise_map]
  rw [List.Nodup, List.pairwise_map] at nodup
  exact (sorted.and nodup).imp fun ⟨h1, h2⟩ => by
    simp only [decide_eq_true_eq] at h1
    omega

/-- The positions of a map of changes ascend strictly. -/
theorem pairwise_lt_positions {β γ : Type} (m : Std.ExtTreeMap UInt32 β) (f : UInt32 → β → γ)
    (position : γ → UInt32) (hposition : ∀ i v, position (f i v) = i) :
    ((m.toList.map fun p => f p.1 p.2).map fun c => (position c).toNat).Pairwise (· < ·) := by
  rw [List.map_map, List.pairwise_map]
  refine Std.ExtTreeMap.ordered_keys_toList.imp fun {a b} h => ?_
  rw [Std.compare_eq_lt] at h
  simpa [hposition] using UInt32.lt_iff_toNat_lt.mp h

/-- Two keys of 32 bytes with one value as words are equal. -/
theorem fromBeBytes_toNat_injective :
    Function.Injective fun key : Bytes32 => (U256.fromBeBytes key).toNat :=
  fun _ _ h => U256.fromBeBytes_injective (BitVec.eq_of_toNat_eq h)

/-- An injective function keeps the elements of a list distinct. -/
theorem nodup_map_of_injective {α β : Type} {f : α → β} (inj : Function.Injective f)
    {l : List α} (h : l.Nodup) : (l.map f).Nodup :=
  List.Pairwise.map f (fun _ _ hne heq => hne (inj heq)) h

/-- The keys of a part of the entries of a map are distinct. -/
theorem nodup_keys_filter {β : Type} (m : Std.ExtTreeMap Bytes32 β) (p : Bytes32 × β → Bool) :
    ((m.toList.filter p).map fun e => (U256.fromBeBytes e.1).toNat).Nodup := by
  have keys : (m.toList.map Prod.fst).Nodup := by
    rw [Std.ExtTreeMap.map_fst_toList_eq_keys]
    exact Std.ExtTreeMap.nodup_keys
  have sub := nodup_map_of_injective fromBeBytes_toNat_injective
    (keys.sublist ((List.filter_sublist (p := p)).map Prod.fst))
  simpa [List.map_map, Function.comp_def] using sub

/-- The keys of a part of a set are distinct. -/
theorem nodup_toList_filter (s : Std.ExtTreeSet Bytes32) (p : Bytes32 → Bool) :
    ((s.toList.filter p).map fun key => (U256.fromBeBytes key).toNat).Nodup := by
  have keys : s.toList.Nodup := Std.ExtTreeSet.distinct_toList.imp Std.ReflCmp.ne_of_cmp_ne_eq
  have sub := nodup_map_of_injective fromBeBytes_toNat_injective
    (keys.sublist (List.filter_sublist (p := p)))
  simpa [List.map_map, Function.comp_def] using sub

/-! ## The order of each account -/

/-- The entry of every account record passes the checks of one account. -/
theorem checkAccount_toChanges (address : Address) (r : AccountRecord) :
    checkAccount (r.toChanges address) = .ok () := by
  simp only [checkAccount, AccountRecord.toChanges, bind_eq_ok_unit, ensure_eq_ok, forM_eq_ok]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ascending_of_pairwise (pairwise_lt_mergeSort (fun s : SlotChanges => s.slot.toNat) ?_)
    simpa [List.map_map, Function.comp_def] using
      nodup_keys_filter r.storageChanges fun x => !x.2.isEmpty
  · intro s hs
    obtain ⟨⟨key, values⟩, hmem, rfl⟩ := List.mem_map.mp (List.mem_mergeSort.mp hs)
    refine ⟨by simpa using (List.mem_filter.mp hmem).2, ascending_of_pairwise ?_⟩
    simpa using pairwise_lt_positions values (fun i v => (⟨i, v⟩ : StorageChange)) (·.index)
      fun _ _ => rfl
  · refine ascending_of_pairwise (pairwise_lt_mergeSort (fun k : U256 => k.toNat) ?_)
    simpa [List.map_map, Function.comp_def] using nodup_toList_filter r.storageReads _
  · intro read hread
    obtain ⟨key, hkey, rfl⟩ := List.mem_map.mp (List.mem_mergeSort.mp hread)
    have hempty := (List.mem_filter.mp hkey).2
    simp only [Bool.not_eq_true']
    refine Bool.eq_false_iff.mpr fun hc => ?_
    obtain ⟨s, hs, heq⟩ := List.mem_map.mp (List.mem_of_elem_eq_true hc)
    obtain ⟨⟨key', values⟩, hmem, rfl⟩ := List.mem_map.mp (List.mem_mergeSort.mp hs)
    obtain ⟨hmem, hne⟩ := List.mem_filter.mp hmem
    have := fromBeBytes_toNat_injective heq
    subst this
    rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some] at hmem
    simp [Std.ExtTreeMap.getD_eq_getD_getElem?, hmem] at hempty
    simp [hempty] at hne
  · exact ascending_of_pairwise
      (pairwise_lt_positions _ (fun i v => (⟨i, v⟩ : BalanceChange)) (·.index) fun _ _ => rfl)
  · exact ascending_of_pairwise (pairwise_lt_positions _
      (fun i v => (⟨i, UInt64.ofNat v⟩ : NonceChange)) (·.index) fun _ _ => rfl)
  · exact ascending_of_pairwise
      (pairwise_lt_positions _ (fun i v => (⟨i, v⟩ : CodeChange)) (·.index) fun _ _ => rfl)

/-! ## The order of the accounts -/

/-- The accounts of every built list ascend by address. -/
theorem checkAddresses_build (b : AccessListBuilder) : checkAddresses b.build = .ok () := by
  rw [checkAddresses_eq_ok_iff]
  refine ascending_of_pairwise ?_
  have := pairwise_lt_mergeSort (fun x : AccountChanges => addressKey x.address)
    (l := b.accounts.toList.map fun (address, r) => r.toChanges address) ?_
  · simpa [AccessListBuilder.build] using this
  have keys : (b.accounts.toList.map Prod.fst).Nodup := by
    rw [Std.ExtTreeMap.map_fst_toList_eq_keys]
    exact Std.ExtTreeMap.nodup_keys
  have := nodup_map_of_injective addressKey_injective keys
  rw [List.map_map] at this
  simpa [List.map_map, Function.comp_def, AccountRecord.toChanges] using this

/-- Every built list passes the order and uniqueness checks.

So it passes all the checks of a list alone exactly when its size fits the gas limit. -/
theorem check_build (b : AccessListBuilder) (gasLimit : Nat) :
    check b.build gasLimit = .ok () ↔ itemCount b.build ≤ gasLimit / ITEM_COST := by
  rw [check_eq_ok_iff, ← checkAddresses_eq_ok_iff]
  refine ⟨fun h => h.2.2, fun h => ⟨fun a ha => ?_, checkAddresses_build b, h⟩⟩
  obtain ⟨⟨address, r⟩, -, rfl⟩ := List.mem_map.mp (List.mem_mergeSort.mp ha)
  exact checkAccount_toChanges address r

/-! ## Changes and writes that change nothing -/

namespace AccessListBuilder

/-- A field change at the current position sets or drops its value there, and keeps the others.

It sets the value when the field changed, and drops it when it did not. -/
theorem setField_at {α : Type} (b : AccessListBuilder) (address : Address) (changed : Bool)
    (value : α) (field : AccountRecord → Std.ExtTreeMap UInt32 α)
    (update : AccountRecord → Std.ExtTreeMap UInt32 α → AccountRecord)
    (hfield : ∀ r m, field (update r m) = m) (hempty : field {} = ∅) (index : UInt32) :
    ((b.setField address changed value field update).accounts[address]?.bind
        fun r => (field r)[index]?) =
      if index = b.index then (if changed then some value else none)
      else b.accounts[address]?.bind fun r => (field r)[index]? := by
  unfold setField record amend
  cases changed <;> cases h : b.accounts[address]? <;>
    simp [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase,
      Std.ExtTreeMap.getD_eq_getD_getElem?, h, hfield, hempty,
      eq_comm (a := index)] <;> split <;> simp_all

/-- A field change keeps every value of another field. -/
theorem setField_other {α β : Type} (b : AccessListBuilder) (address other : Address)
    (changed : Bool) (value : α) (field : AccountRecord → Std.ExtTreeMap UInt32 α)
    (update : AccountRecord → Std.ExtTreeMap UInt32 α → AccountRecord)
    (get : AccountRecord → Std.ExtTreeMap UInt32 β) (hget : ∀ r m, get (update r m) = get r)
    (hempty : get {} = ∅) (index : UInt32) :
    ((b.setField address changed value field update).accounts[other]?.bind
        fun r => (get r)[index]?) = b.accounts[other]?.bind fun r => (get r)[index]? := by
  unfold setField record amend
  cases changed <;> cases h : b.accounts[address]? <;> cases h' : b.accounts[other]? <;>
    simp [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_modify,
      Std.ExtTreeMap.getD_eq_getD_getElem?, h, h', hget, hempty] <;>
    first | (rintro rfl; simp_all) | (split <;> simp_all)

/-- Bringing an account into the list keeps every value of its fields. -/
theorem record_id_at {β : Type} (b : AccessListBuilder) (address other : Address)
    (get : AccountRecord → Std.ExtTreeMap UInt32 β) (hempty : get {} = ∅) (index : UInt32) :
    ((b.record address id).accounts[other]?.bind fun r => (get r)[index]?) =
      b.accounts[other]?.bind fun r => (get r)[index]? := by
  unfold record
  cases h : b.accounts[address]? <;> cases h' : b.accounts[other]? <;>
    simp [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getD_eq_getD_getElem?, h, h', hempty] <;>
    first | (rintro rfl; simp_all) | (split <;> simp_all)

/-- An account write brings the account into the list, even when no field changed. -/
theorem mem_recordAccountWrite {b b' : AccessListBuilder} {tx : State.TransactionState}
    {address : Address} {written : Option State.Account}
    (h : b.recordAccountWrite tx address written = .ok b') : address ∈ b'.accounts := by
  have keep : ∀ (c : AccessListBuilder) (changed : Bool) {α : Type} (value : α) field update,
      address ∈ c.accounts →
        address ∈ (c.setField address changed value field update).accounts := by
    intro c changed α value field update hc
    unfold setField record amend
    split <;> simp_all [Std.ExtTreeMap.mem_modify]
  unfold recordAccountWrite at h
  dsimp only at h
  split at h
  all_goals
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact keep _ _ _ _ _ (keep _ _ _ _ _ (keep _ _ _ _ _ (by
      simp [record])))

/-- An account write records its balance at the current position when the balance changed.

A balance that ends as the position found it records nothing there, as EIP-7928 asks.

Either way, the balances of the other positions stay. -/
theorem recordAccountWrite_balance_at {b b' : AccessListBuilder} {tx : State.TransactionState}
    {address : Address} {written : Option State.Account}
    (h : b.recordAccountWrite tx address written = .ok b') (index : UInt32) :
    (b'.accounts[address]?.bind fun r => r.balanceChanges[index]?) =
      let before := (b.startAccount address).balance
      let after := (written.getD State.EMPTY_ACCOUNT).balance
      if index = b.index then (if before ≠ after then some after else none)
      else b.accounts[address]?.bind fun r => r.balanceChanges[index]? := by
  unfold recordAccountWrite at h
  dsimp only at h
  split at h
  all_goals
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    rw [setField_other (get := fun r => r.balanceChanges) (hget := by intros; rfl) (hempty := rfl),
      setField_other (get := fun r => r.balanceChanges) (hget := by intros; rfl) (hempty := rfl),
      setField_at (hfield := by intros; rfl) (hempty := rfl),
      record_id_at (get := fun r => r.balanceChanges) (hempty := rfl)]
    simp only [decide_eq_true_eq]
    rfl

/-- Dropping the value of a slot at a position drops only that value. -/
theorem dropSlotChange_at (changes : Std.ExtTreeMap Bytes32 (Std.ExtTreeMap UInt32 U256))
    (key : Bytes32) (index other : UInt32) :
    ((dropSlotChange changes key index)[key]?.bind (·[other]?)) =
      if other = index then none else (changes[key]?.bind (·[other]?)) := by
  unfold dropSlotChange
  cases h : changes[key]? with
  | none => simp [h]
  | some values =>
    simp only
    split
    · rename_i hempty
      have := congrArg (·[other]?) (Std.ExtTreeMap.isEmpty_iff.mp hempty)
      simp only [Std.ExtTreeMap.getElem?_erase, Std.compare_eq_iff_eq] at this
      simp only [Std.ExtTreeMap.getElem?_erase, Std.compare_eq_iff_eq, Option.bind_some]
      split <;> simp_all [eq_comm (a := other)]
    · simp [Std.ExtTreeMap.getElem?_erase, eq_comm (a := other)]

/-- A storage write records its value at the current position when it changes the slot.

A write that leaves the slot as the position found it records nothing there.

Either way, the values of the other positions stay. -/
theorem recordStorageWrite_at (b : AccessListBuilder) (address : Address) (key : Bytes32)
    (value : U256) (index : UInt32) :
    (((b.recordStorageWrite address key value).accounts[address]?.bind
        fun r => r.storageChanges[key]?).bind (·[index]?)) =
      if index = b.index then (if b.startStorage address key ≠ value then some value else none)
      else ((b.accounts[address]?.bind fun r => r.storageChanges[key]?).bind (·[index]?)) := by
  unfold recordStorageWrite record
  split
  · rename_i hne
    cases h : b.accounts[address]? with
    | none =>
      simp [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getD_eq_getD_getElem?, h,
        eq_comm (a := index)]
    | some r =>
      simp only [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getD_eq_getD_getElem?, h,
        Std.compare_eq_iff_eq, ↓reduceIte, Option.getD_some, Option.bind_some,
        eq_comm (a := index)]
      split
      · rfl
      · cases r.storageChanges[key]? <;> simp
  · rename_i heq
    cases h : b.accounts[address]? with
    | none =>
      simp [Std.ExtTreeMap.getD_eq_getD_getElem?, h,
        dropSlotChange]
    | some r =>
      have := dropSlotChange_at r.storageChanges key b.index index
      simp only [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getD_eq_getD_getElem?, h,
        Std.compare_eq_iff_eq, ↓reduceIte, Option.getD_some, Option.bind_some] at this ⊢
      exact this

/-- A storage write that leaves the slot as the position found it records the key as read.

The account then joins the list, as EIP-7928 counts such a write as a read. -/
theorem mem_storageReads_recordStorageWrite {b : AccessListBuilder} {address : Address}
    {key : Bytes32} {value : U256} (h : b.startStorage address key = value) :
    ∃ r, (b.recordStorageWrite address key value).accounts[address]? = some r ∧
      key ∈ r.storageReads := by
  unfold recordStorageWrite record
  simp only [h, ne_eq, not_true_eq_false, ↓reduceIte, Std.ExtTreeMap.getElem?_insert_self,
    Option.some.injEq, exists_eq_left']
  exact Std.ExtTreeSet.mem_insert_self

end AccessListBuilder

end EthLib.Execution.Blocks
