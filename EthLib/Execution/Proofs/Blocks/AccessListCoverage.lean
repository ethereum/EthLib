module

public import EthLib.Execution.Proofs.Blocks.AccessListBuilder

/-!
# Proofs: the builder records every account and key that a call touched

When a transaction or a system call ends, the builder records what it did.

Every account that the call read or wrote then has a record.

Every storage key that it read or wrote is then named by the record of its account.

A key is named when it has a change at some position, or when it counts as read.

A write that leaves a slot as its position found it records no change there, only a read.

So a written key may appear among the reads of its account rather than among its changes.

A later call never drops a record or a named key.

The list that the builder gives holds an entry for each record, with each named key.

Source: [EIP-7928][eip7928], which asks the list to hold every account and key that the block
accessed.

[eip7928]: https://eips.ethereum.org/EIPS/eip-7928#recording-semantics-by-change-type
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.State (TransactionState)

/-- The record of an account names a storage key when the key has a change, or was read. -/
def AccountRecord.NamesKey (r : AccountRecord) (key : Bytes32) : Prop :=
  (r.storageChanges.getD key ∅).isEmpty = false ∨ key ∈ r.storageReads

namespace AccessListBuilder

/-- The builder names a storage key of an account in the record of that account. -/
def NamesKey (b : AccessListBuilder) (address : Address) (key : Bytes32) : Prop :=
  ∃ r, b.accounts[address]? = some r ∧ r.NamesKey key

/-- The builder `b'` keeps every account that `b` records, and every key that `b` names. -/
def Extends (b b' : AccessListBuilder) : Prop :=
  (∀ address, address ∈ b.accounts → address ∈ b'.accounts) ∧
    ∀ address key, b.NamesKey address key → b'.NamesKey address key

/-- The builder records every account that the call `tx` read or wrote.

It also names every storage key that the call read or wrote. -/
def Covers (b : AccessListBuilder) (tx : TransactionState) : Prop :=
  (∀ address, address ∈ tx.accountReads → address ∈ b.accounts) ∧
    (∀ address, address ∈ tx.storageReads → address ∈ b.accounts) ∧
    (∀ address, address ∈ tx.accountWrites → address ∈ b.accounts) ∧
    (∀ address keys key, tx.storageReads[address]? = some keys → key ∈ keys →
      b.NamesKey address key) ∧
    (∀ address slots key, tx.storageWrites[address]? = some slots → key ∈ slots →
      b.NamesKey address key)

theorem extends_refl (b : AccessListBuilder) : b.Extends b :=
  ⟨fun _ h => h, fun _ _ h => h⟩

theorem Extends.trans {b b' b'' : AccessListBuilder} (h : b.Extends b') (h' : b'.Extends b'') :
    b.Extends b'' :=
  ⟨fun a ha => h'.1 a (h.1 a ha), fun a k hk => h'.2 a k (h.2 a k hk)⟩

/-- A builder that extends one that covers a call covers it too. -/
theorem Covers.mono {b b' : AccessListBuilder} {tx : TransactionState} (h : b.Covers tx)
    (hb : b.Extends b') : b'.Covers tx :=
  ⟨fun a ha => hb.1 a (h.1 a ha), fun a ha => hb.1 a (h.2.1 a ha),
    fun a ha => hb.1 a (h.2.2.1 a ha), fun a ks k hks hk => hb.2 a k (h.2.2.2.1 a ks k hks hk),
    fun a s k hs hk => hb.2 a k (h.2.2.2.2 a s k hs hk)⟩

/-! ## One step of the builder -/

/-- Changing the record of an account in a way that keeps its named keys extends the builder.

The account then has a record. -/
theorem record_extends (b : AccessListBuilder) (address : Address)
    {f : AccountRecord → AccountRecord} (hf : ∀ r key, r.NamesKey key → (f r).NamesKey key) :
    b.Extends (b.record address f) ∧ address ∈ (b.record address f).accounts := by
  refine ⟨⟨fun a ha => ?_, fun a k ⟨r, hr, hk⟩ => ?_⟩, ?_⟩
  · simp [record, Std.ExtTreeMap.mem_insert, ha]
  · by_cases hEq : address = a
    · subst hEq
      refine ⟨f r, ?_, hf r k hk⟩
      simp [record, Std.ExtTreeMap.getD_eq_getD_getElem?, hr]
    · refine ⟨r, ?_, hk⟩
      simp [record, Std.ExtTreeMap.getElem?_insert, hEq, hr]
  · simp [record]

/-- Changing a record that keeps its named keys, if the account has one, extends the builder. -/
theorem amend_extends (b : AccessListBuilder) (address : Address)
    {f : AccountRecord → AccountRecord} (hf : ∀ r key, r.NamesKey key → (f r).NamesKey key) :
    b.Extends (b.amend address f) := by
  refine ⟨fun a ha => ?_, fun a k ⟨r, hr, hk⟩ => ?_⟩
  · simpa [amend, Std.ExtTreeMap.mem_modify] using ha
  · by_cases hEq : address = a
    · subst hEq
      exact ⟨f r, by simp [amend, hr], hf r k hk⟩
    · exact ⟨r, by simp [amend, Std.ExtTreeMap.getElem?_modify, hEq, hr], hk⟩

/-- A change of the balance, the nonce or the code extends the builder. -/
theorem setField_extends {α : Type} (b : AccessListBuilder) (address : Address) (changed : Bool)
    (value : α) (field : AccountRecord → Std.ExtTreeMap UInt32 α)
    (update : AccountRecord → Std.ExtTreeMap UInt32 α → AccountRecord)
    (hchanges : ∀ r m, (update r m).storageChanges = r.storageChanges)
    (hreads : ∀ r m, (update r m).storageReads = r.storageReads) :
    b.Extends (b.setField address changed value field update) := by
  have keep : ∀ (m : AccountRecord → Std.ExtTreeMap UInt32 α) r key,
      r.NamesKey key → (update r (m r)).NamesKey key := by
    intro m r key hk
    simpa [AccountRecord.NamesKey, hchanges, hreads] using hk
  unfold setField
  split
  · exact (record_extends b address (keep _)).1
  · exact amend_extends b address (keep _)

/-- An account write extends the builder, and gives the account a record. -/
theorem recordAccountWrite_extends {b b' : AccessListBuilder} {tx : TransactionState}
    {address : Address} {written : Option State.Account}
    (h : b.recordAccountWrite tx address written = .ok b') :
    b.Extends b' ∧ address ∈ b'.accounts := by
  refine ⟨?_, mem_recordAccountWrite h⟩
  unfold recordAccountWrite at h
  dsimp only at h
  have hid := (record_extends b address (f := id) fun _ _ hk => hk).1
  have keep : ∀ {α : Type} {c : AccessListBuilder} {changed : Bool} {value : α}
      {field : AccountRecord → Std.ExtTreeMap UInt32 α}
      {update : AccountRecord → Std.ExtTreeMap UInt32 α → AccountRecord},
      (∀ r m, (update r m).storageChanges = r.storageChanges) →
      (∀ r m, (update r m).storageReads = r.storageReads) → b.Extends c →
      b.Extends (c.setField address changed value field update) :=
    fun hchanges hreads hc => hc.trans (setField_extends _ _ _ _ _ _ hchanges hreads)
  split at h
  all_goals
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact keep (fun _ _ => rfl) (fun _ _ => rfl) (keep (fun _ _ => rfl) (fun _ _ => rfl)
      (keep (fun _ _ => rfl) (fun _ _ => rfl) hid))

/-- Dropping the value of a slot at a position keeps the values of every other slot. -/
theorem dropSlotChange_getD_of_ne (changes : Std.ExtTreeMap Bytes32 (Std.ExtTreeMap UInt32 U256))
    {key other : Bytes32} (index : UInt32) (hne : key ≠ other) :
    (dropSlotChange changes key index).getD other ∅ = changes.getD other ∅ := by
  unfold dropSlotChange
  split
  · rfl
  · dsimp only
    split <;> simp [Std.ExtTreeMap.getD_erase, Std.ExtTreeMap.getD_insert, hne]

/-- A storage write extends the builder, and names its key in the record of its account.

The key has a change when the write changed the slot, and counts as read otherwise. -/
theorem recordStorageWrite_extends (b : AccessListBuilder) (address : Address) (key : Bytes32)
    (value : U256) :
    b.Extends (b.recordStorageWrite address key value) ∧
      (b.recordStorageWrite address key value).NamesKey address key := by
  unfold recordStorageWrite
  split
  · refine ⟨(record_extends b address fun r k hk => ?_).1, ?_⟩
    · by_cases hEq : key = k
      · subst hEq
        left
        simp [Std.ExtTreeMap.getD_insert_self]
      · simpa [AccountRecord.NamesKey, Std.ExtTreeMap.getD_insert, hEq] using hk
    · refine ⟨_, Std.ExtTreeMap.getElem?_insert_self, ?_⟩
      left
      simp [Std.ExtTreeMap.getD_insert_self]
  · refine ⟨(record_extends b address fun r k hk => ?_).1, ?_⟩
    · by_cases hEq : key = k
      · subst hEq
        exact Or.inr Std.ExtTreeSet.mem_insert_self
      · rcases hk with hk | hk
        · left
          simpa [dropSlotChange_getD_of_ne _ _ hEq] using hk
        · exact Or.inr (Std.ExtTreeSet.mem_insert.mpr (Or.inr hk))
    · exact ⟨_, Std.ExtTreeMap.getElem?_insert_self, Or.inr Std.ExtTreeSet.mem_insert_self⟩

/-! ## The folds of a call -/

/-- A fold whose every step extends the builder and meets a lasting goal meets it for all. -/
theorem foldl_extends {α : Type} (f : AccessListBuilder → α → AccessListBuilder)
    (goal : AccessListBuilder → α → Prop)
    (hgoal : ∀ b b' x, b.Extends b' → goal b x → goal b' x)
    (hf : ∀ b x, b.Extends (f b x) ∧ goal (f b x) x) :
    ∀ (l : List α) (b : AccessListBuilder),
      b.Extends (l.foldl f b) ∧ ∀ x ∈ l, goal (l.foldl f b) x
  | [], b => ⟨extends_refl b, by simp⟩
  | x :: l, b => by
    obtain ⟨hext, hall⟩ := foldl_extends f goal hgoal hf l (f b x)
    refine ⟨(hf b x).1.trans hext, fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hgoal _ _ _ hext (hf b y).2
    · exact hall y hy

/-- A fold that can fail, whose every step extends the builder and meets a lasting goal. -/
theorem foldlM_extends {α ε : Type} (f : AccessListBuilder → α → Except ε AccessListBuilder)
    (goal : AccessListBuilder → α → Prop)
    (hgoal : ∀ b b' x, b.Extends b' → goal b x → goal b' x)
    (hf : ∀ b x b', f b x = .ok b' → b.Extends b' ∧ goal b' x) :
    ∀ (l : List α) (b b' : AccessListBuilder), l.foldlM f b = .ok b' →
      b.Extends b' ∧ ∀ x ∈ l, goal b' x
  | [], b, b', h => by
    cases h
    exact ⟨extends_refl b, by simp⟩
  | x :: l, b, b', h => by
    rw [List.foldlM_cons, bind_ok_iff] at h
    obtain ⟨mid, hmid, h⟩ := h
    obtain ⟨hext, hall⟩ := foldlM_extends f goal hgoal hf l mid b' h
    refine ⟨(hf b x mid hmid).1.trans hext, fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hgoal _ _ _ hext (hf b y mid hmid).2
    · exact hall y hy

/-- The writes to the storage of one account name every written key. -/
theorem foldl_recordStorageWrite (b : AccessListBuilder) (address : Address)
    (slots : Std.ExtTreeMap Bytes32 U256) :
    b.Extends (slots.foldl (fun b key value => b.recordStorageWrite address key value) b) ∧
      ∀ key ∈ slots,
        (slots.foldl (fun b key value => b.recordStorageWrite address key value) b).NamesKey
          address key := by
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  obtain ⟨hext, hall⟩ := foldl_extends _ (fun b (x : Bytes32 × U256) => b.NamesKey address x.1)
    (fun _ _ _ h hk => h.2 _ _ hk)
    (fun b x => recordStorageWrite_extends b address x.1 x.2) slots.toList b
  refine ⟨hext, fun key hkey => ?_⟩
  obtain ⟨value, hvalue⟩ := Option.isSome_iff_exists.mp
    (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hkey)
  exact hall (key, value) (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hvalue)

/-- After it records a call, the builder extends the builder before, and covers the call.

The call may be a transaction or a system call. -/
theorem recordTransaction_covers {b b' : AccessListBuilder} {tx : TransactionState}
    (h : b.recordTransaction tx = .ok b') : b.Extends b' ∧ b'.Covers tx := by
  unfold recordTransaction at h
  obtain ⟨b₃, h₃, h⟩ := bind_ok_iff.mp h
  cases h
  -- The accounts read.
  rw [Std.ExtTreeSet.foldl_eq_foldl_toList] at h₃
  obtain ⟨e₁, c₁⟩ := foldl_extends (fun b address => b.record address id)
    (fun b address => address ∈ b.accounts) (fun _ _ _ h ha => h.1 _ ha)
    (fun b address => record_extends b address fun _ _ hk => hk) tx.accountReads.toList b
  -- The storage keys read.
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList] at h₃
  obtain ⟨e₂, c₂⟩ := foldl_extends
    (fun b (x : Address × Std.ExtTreeSet Bytes32) => b.record x.1 fun r =>
      { r with storageReads := r.storageReads.insertMany x.2.toList })
    (fun b x => x.1 ∈ b.accounts ∧ ∀ key ∈ x.2, b.NamesKey x.1 key)
    (fun _ _ _ h ⟨ha, hk⟩ => ⟨h.1 _ ha, fun key hkey => h.2 _ _ (hk key hkey)⟩)
    (fun b x => by
      have grow := record_extends b x.1 (f := fun r =>
        { r with storageReads := r.storageReads.insertMany x.2.toList }) fun r key hk => by
          rcases hk with hk | hk
          · exact Or.inl hk
          · exact Or.inr (Std.ExtTreeSet.mem_insertMany_list.mpr (Or.inl hk))
      refine ⟨grow.1, grow.2, fun key hkey => ⟨_, Std.ExtTreeMap.getElem?_insert_self, Or.inr ?_⟩⟩
      exact Std.ExtTreeSet.mem_insertMany_list.mpr
        (Or.inr (List.elem_iff.mpr (Std.ExtTreeSet.mem_toList.mpr hkey))))
    tx.storageReads.toList _
  -- The accounts written.
  rw [Std.ExtTreeMap.foldlM_eq_foldlM_toList] at h₃
  obtain ⟨e₃, c₃⟩ := foldlM_extends
    (fun b (x : Address × Option State.Account) => b.recordAccountWrite tx x.1 x.2)
    (fun b x => x.1 ∈ b.accounts) (fun _ _ _ h ha => h.1 _ ha)
    (fun _ _ _ hx => recordAccountWrite_extends hx) _ _ _ h₃
  -- The storage keys written.
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  obtain ⟨e₄, c₄⟩ := foldl_extends
    (fun b (x : Address × Std.ExtTreeMap Bytes32 U256) =>
      x.2.foldl (fun b key value => b.recordStorageWrite x.1 key value) b)
    (fun b x => ∀ key ∈ x.2, b.NamesKey x.1 key)
    (fun _ _ (x : Address × Std.ExtTreeMap Bytes32 U256) h hk key hkey =>
      h.2 x.1 key (hk key hkey))
    (fun b x => foldl_recordStorageWrite b x.1 x.2) tx.storageWrites.toList b₃
  have e₂₄ := e₃.trans e₄
  have e₁₄ := e₂.trans e₂₄
  refine ⟨e₁.trans e₁₄, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, ?_, ?_⟩
  · exact e₁₄.1 _ (c₁ a (Std.ExtTreeSet.mem_toList.mpr ha))
  · obtain ⟨keys, hkeys⟩ := Option.isSome_iff_exists.mp
      (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp ha)
    exact e₂₄.1 _ (c₂ (a, keys) (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hkeys)).1
  · obtain ⟨written, hw⟩ := Option.isSome_iff_exists.mp
      (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp ha)
    exact e₄.1 _ (c₃ (a, written) (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hw))
  · intro a keys key hkeys hkey
    exact e₂₄.2 _ _
      ((c₂ (a, keys) (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hkeys)).2 key hkey)
  · intro a slots key hslots hkey
    exact c₄ (a, slots) (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hslots) key hkey

/-! ## The list -/

/-- Each account with a record has an entry in the list. -/
theorem mem_build {b : AccessListBuilder} {address : Address} (h : address ∈ b.accounts) :
    ∃ entry ∈ b.build, entry.address = address := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp h)
  refine ⟨r.toChanges address, List.mem_mergeSort.mpr (List.mem_map.mpr
    ⟨(address, r), Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hr, rfl⟩), rfl⟩

/-- Each named key is in the entry of its account: among its changed slots, or its reads. -/
theorem namesKey_build {b : AccessListBuilder} {address : Address} {key : Bytes32}
    (h : b.NamesKey address key) :
    ∃ entry ∈ b.build, entry.address = address ∧
      (U256.fromBeBytes key ∈ entry.storageChanges.map (·.slot) ∨
        U256.fromBeBytes key ∈ entry.storageReads) := by
  obtain ⟨r, hr, hk⟩ := h
  refine ⟨r.toChanges address, List.mem_mergeSort.mpr (List.mem_map.mpr
    ⟨(address, r), Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hr, rfl⟩), rfl, ?_⟩
  simp only [AccountRecord.toChanges]
  by_cases hempty : (r.storageChanges.getD key ∅).isEmpty = false
  · left
    obtain ⟨values, hvalues⟩ : ∃ values, r.storageChanges[key]? = some values := by
      cases hc : r.storageChanges[key]? with
      | none => simp [Std.ExtTreeMap.getD_eq_getD_getElem?, hc] at hempty
      | some values => exact ⟨values, rfl⟩
    rw [Std.ExtTreeMap.getD_eq_getD_getElem?, hvalues, Option.getD_some] at hempty
    refine List.mem_map.mpr ⟨_, List.mem_mergeSort.mpr (List.mem_map.mpr ⟨(key, values),
      List.mem_filter.mpr ⟨Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hvalues, ?_⟩,
      rfl⟩), rfl⟩
    simp [hempty]
  · right
    have hread := hk.resolve_left hempty
    refine List.mem_mergeSort.mpr (List.mem_map.mpr ⟨key, List.mem_filter.mpr
      ⟨Std.ExtTreeSet.mem_toList.mpr hread, ?_⟩, rfl⟩)
    simpa using hempty

end AccessListBuilder

end EthLib.Execution.Blocks
