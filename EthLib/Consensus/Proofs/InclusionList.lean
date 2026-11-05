module

public import EthLib.Consensus.InclusionList

/-!
# Proofs: the inclusion lists a node keeps

A new list never changes a stored list, and never clears an equivocator.

A first list is stored, and a second, different list marks its member.

The transactions that count are those of the members that never equivocated, each once.

The bits of the timely lists are among the bits of all lists.

The bits of the store are inclusive of themselves, and more bits stay inclusive.
-/

@[expose] public section

namespace EthLib.Consensus.InclusionListStore

variable {store : InclusionListStore} {slot : Slot} {root : Root}

theorem modify_self {α : Type} (map : Slot → Root → α) (change : α → α) :
    modify map slot root change slot root = change (map slot root) := by
  simp [modify]

theorem modify_other {α : Type} (map : Slot → Root → α) (change : α → α) {slot' : Slot}
    {root' : Root} (other : ¬(slot' = slot ∧ root' = root)) :
    modify map slot root change slot' root' = map slot' root' := by
  simp [modify, other]

theorem lookup_append_of_some {member : ValidatorIndex}
    {entries : List (ValidatorIndex × InclusionListEntry)} {entry : InclusionListEntry}
    (extra : ValidatorIndex × InclusionListEntry) (found : entries.lookup member = some entry) :
    (entries ++ [extra]).lookup member = some entry := by
  induction entries with
  | nil => simp at found
  | cons head tail ih =>
    obtain ⟨key, value⟩ := head
    cases same : member == key
    · simp only [List.cons_append, List.lookup, same] at found ⊢
      exact ih found
    · simpa [List.lookup, same] using found

theorem lookup_append_of_none {member : ValidatorIndex}
    {entries : List (ValidatorIndex × InclusionListEntry)} (entry : InclusionListEntry)
    (missing : entries.lookup member = none) :
    (entries ++ [(member, entry)]).lookup member = some entry := by
  induction entries with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨key, value⟩ := head
    cases same : member == key
    · simp only [List.cons_append, List.lookup, same] at missing ⊢
      exact ih missing
    · simp [List.lookup, same] at missing

/-- A stored list stays stored, whatever list arrives. -/
theorem lookup_process {member : ValidatorIndex} {entry : InclusionListEntry}
    (signed : SignedInclusionList) (timely : Bool)
    (found : (store.inclusionLists slot root).lookup member = some entry) :
    ((store.process signed timely).inclusionLists slot root).lookup member = some entry := by
  unfold process
  dsimp only
  split
  · split <;> exact found
  · by_cases key : slot = signed.message.slot ∧ root = signed.message.dependentRoot
    · obtain ⟨rfl, rfl⟩ := key
      simp only [modify_self]
      exact lookup_append_of_some _ found
    · simpa [modify_other _ _ key] using found

/-- An equivocator stays an equivocator, whatever list arrives. -/
theorem mem_equivocators_process {member : ValidatorIndex} (signed : SignedInclusionList)
    (timely : Bool) (marked : member ∈ store.equivocators slot root) :
    member ∈ (store.process signed timely).equivocators slot root := by
  unfold process
  dsimp only
  split
  · split
    · exact marked
    · by_cases key : slot = signed.message.slot ∧ root = signed.message.dependentRoot
      · obtain ⟨rfl, rfl⟩ := key
        simp only [modify_self]
        split
        · exact marked
        · exact List.mem_append_left _ marked
      · simpa [modify_other _ _ key] using marked
  · exact marked

/-- The first list of a member is stored, with its timeliness. -/
theorem lookup_process_of_none (signed : SignedInclusionList) (timely : Bool)
    (missing : (store.inclusionLists signed.message.slot signed.message.dependentRoot).lookup
      signed.message.validatorIndex = none) :
    ((store.process signed timely).inclusionLists signed.message.slot
        signed.message.dependentRoot).lookup signed.message.validatorIndex =
      some ⟨signed, timely⟩ := by
  unfold process
  dsimp only
  simp only [missing, modify_self]
  exact lookup_append_of_none _ missing

/-- A list that differs from the stored list of its member marks the member. -/
theorem mem_equivocators_process_of_ne (signed : SignedInclusionList) (timely : Bool)
    {stored : InclusionListEntry}
    (found : (store.inclusionLists signed.message.slot signed.message.dependentRoot).lookup
      signed.message.validatorIndex = some stored)
    (differs : stored.signedInclusionList.message ≠ signed.message) :
    signed.message.validatorIndex ∈
      (store.process signed timely).equivocators signed.message.slot
        signed.message.dependentRoot := by
  unfold process
  dsimp only
  simp only [found, differs, ite_false, modify_self]
  split
  · assumption
  · exact List.mem_append_right _ (List.mem_singleton_self _)

/-- A transaction counts exactly when a counted entry holds it. -/
theorem mem_transactions {onlyTimely : Bool} {transaction : InclusionListTransaction} :
    transaction ∈ store.transactions slot root onlyTimely ↔
      ∃ member entry, (member, entry) ∈ store.inclusionLists slot root ∧
        member ∉ store.equivocators slot root ∧ (onlyTimely = true → entry.timely = true) ∧
        transaction ∈ entry.signedInclusionList.message.transactions.data.toList := by
  unfold transactions counted
  rw [List.mem_eraseDups]
  simp only [List.mem_flatMap, List.mem_filter, Prod.exists, Bool.and_eq_true,
    decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  constructor
  · rintro ⟨member, entry, ⟨mem, notMarked, timely⟩, has⟩
    refine ⟨member, entry, mem, notMarked, fun only => ?_, has⟩
    rcases timely with h | h
    · simp [only] at h
    · exact h
  · rintro ⟨member, entry, mem, notMarked, timely, has⟩
    refine ⟨member, entry, ⟨mem, notMarked, ?_⟩, has⟩
    cases onlyTimely
    · exact .inl rfl
    · exact .inr (timely rfl)

theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup := by
  -- The recursion removes the head from the tail, so it runs on the length.
  suffices ∀ n, ∀ l : List α, l.length ≤ n → l.eraseDups.Nodup from this _ l (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro l short
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp short)]
    exact List.nodup_nil
  | succ n ih =>
    intro l short
    cases l with
    | nil => exact List.nodup_nil
    | cons head tail =>
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr ⟨fun mem => ?_, ih _ ?_⟩
      · rw [List.mem_eraseDups, List.mem_filter] at mem
        simp at mem
      · exact Nat.le_trans (List.length_filter_le _ _) (by simpa using short)

/-- Each transaction that counts comes once. -/
theorem nodup_transactions (onlyTimely : Bool) :
    (store.transactions slot root onlyTimely).Nodup :=
  nodup_eraseDups _

/-- A bit is set exactly when the member of its seat has an entry that counts. -/
theorem bits_getElem {preset : Preset} (committee : InclusionListCommittee preset)
    (onlyTimely : Bool) (i : Fin preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat) :
    (store.bits committee slot root onlyTimely).bits[i] =
      (store.counted slot root onlyTimely).any (·.1 == committee[i]) := by
  simp [bits]

/-- A member counted among the timely lists is counted among all lists. -/
theorem bits_timely_le {preset : Preset} (committee : InclusionListCommittee preset)
    (i : Fin preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat)
    (set : (store.bits committee slot root true).bits[i] = true) :
    (store.bits committee slot root false).bits[i] = true := by
  rw [bits_getElem] at set ⊢
  simp only [counted, List.any_eq_true, List.mem_filter, Bool.and_eq_true] at set ⊢
  obtain ⟨entry, ⟨mem, notMarked, -⟩, same⟩ := set
  exact ⟨entry, ⟨mem, notMarked, by simp⟩, same⟩

/-- Some bits are inclusive exactly when they set every bit that the store sets. -/
theorem isInclusive_iff {preset : Preset} {committee : InclusionListCommittee preset}
    {bits : InclusionListBits preset} {onlyTimely : Bool} :
    store.isInclusive committee slot root bits onlyTimely = true ↔
      ∀ i : Fin preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat,
        (store.bits committee slot root onlyTimely).bits[i] = true → bits.bits[i] = true := by
  simp [isInclusive, List.all_eq_true, Bool.or_eq_true]
  constructor
  · intro all i own
    rcases all i with h | h
    · simp [own] at h
    · exact h
  · intro all i
    by_cases own : (store.bits committee slot root onlyTimely).bits[i] = true
    · exact .inr (all i own)
    · exact .inl (by simpa using own)

/-- The bits of the store are inclusive of themselves. -/
theorem isInclusive_self {preset : Preset} (committee : InclusionListCommittee preset)
    (onlyTimely : Bool) :
    store.isInclusive committee slot root (store.bits committee slot root onlyTimely)
      onlyTimely = true :=
  isInclusive_iff.mpr fun _ own => own

/-- Bits that set more stay inclusive. -/
theorem isInclusive_mono {preset : Preset} {committee : InclusionListCommittee preset}
    {fewer more : InclusionListBits preset} {onlyTimely : Bool}
    (le : ∀ i : Fin preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat,
      fewer.bits[i] = true → more.bits[i] = true)
    (inclusive : store.isInclusive committee slot root fewer onlyTimely = true) :
    store.isInclusive committee slot root more onlyTimely = true :=
  isInclusive_iff.mpr fun i own => le i (isInclusive_iff.mp inclusive i own)

end EthLib.Consensus.InclusionListStore
