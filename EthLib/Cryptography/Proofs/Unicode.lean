module

public import EthLib.Cryptography.Unicode
import EthLib.Base.Proofs.Toolchain.ArrayBinSearch

/-!
# Proofs: NFKD normalization

Canonical ordering only reorders characters.

Text below U+00A0, which holds all of ASCII, is already in NFKD form.
-/

@[expose] public section

namespace EthLib.Cryptography.Unicode

/-! ## Lookups in the tables -/

/-- A value found in a table belongs to an entry of that code point. -/
theorem exists_mem_of_lookup_eq_some {α : Type} [Inhabited α] {table : Array (Nat × α)}
    {code : Nat} {value : α} (h : lookup table code = some value) :
    ∃ entry ∈ table, entry.1 = code ∧ entry.2 = value := by
  unfold lookup at h
  obtain ⟨entry, found, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨mem, below, above⟩ := Base.Toolchain.Array.binSearch_some found
  -- The entry found is neither below nor above the code point, so it has that code point.
  refine ⟨entry, mem, ?_, rfl⟩
  simp only [decide_eq_false_iff_not, Nat.not_lt] at below above
  omega

/-- A code point below every key of a table has no value in it. -/
theorem lookup_eq_none_of_lt {α : Type} [Inhabited α] {table : Array (Nat × α)} {code bound : Nat}
    (keys : table.toList.all (fun entry => decide (bound ≤ entry.1)) = true)
    (below : code < bound) :
    lookup table code = none := by
  cases h : lookup table code with
  | none => rfl
  | some value =>
    -- A value would come from an entry of that code point, which lies below every key.
    obtain ⟨entry, mem, rfl, -⟩ := exists_mem_of_lookup_eq_some h
    have := List.all_eq_true.mp keys entry (Array.mem_toList_iff.mpr mem)
    simp only [decide_eq_true_eq] at this
    omega

/-- Every key of the combining classes is at least U+0300. -/
theorem combiningClasses_keys :
    Data.combiningClasses.toList.all (fun entry => decide (0x300 ≤ entry.1)) = true := by
  -- The table is a concatenation of small parts, and each part is checked on its own.
  simp only [Data.combiningClasses, Array.toList_append, List.all_append, Bool.and_eq_true]
  and_intros <;> decide +kernel

/-- Every key of the decompositions is at least U+00A0. -/
theorem decompositions_keys :
    Data.decompositions.toList.all (fun entry => decide (0xA0 ≤ entry.1)) = true := by
  -- The table is a concatenation of small parts, and each part is checked on its own.
  simp only [Data.decompositions, Array.toList_append, List.all_append, Bool.and_eq_true]
  and_intros <;> decide +kernel

/-! ## Characters below U+00A0 -/

/-- A character below U+0300 is a starter, of combining class zero. -/
theorem combiningClass_of_lt {c : Char} (below : c.toNat < 0x300) : combiningClass c = 0 := by
  unfold combiningClass
  rw [lookup_eq_none_of_lt combiningClasses_keys below]
  rfl

/-- A character below U+00A0 decomposes to itself. -/
theorem decompose_of_lt {c : Char} (below : c.toNat < 0xA0) : decompose c = [c] := by
  unfold decompose
  -- Not a Hangul syllable, and not in the table, so the character stays as it is.
  have notHangul : ¬(0xAC00 ≤ c.toNat ∧ c.toNat < 0xAC00 + 11172) := by omega
  simp only [notHangul, ↓reduceIte, lookup_eq_none_of_lt decompositions_keys below,
    Option.getD_none, List.map_cons, List.map_nil, Char.ofNat_toNat]

/-! ## Canonical ordering -/

/-- Inserting a mark into a run only reorders the run. -/
theorem insertMark_perm (c : Char) (rank : Nat) (marks : List (Char × Nat)) :
    ((insertMark c rank marks).map Prod.fst).Perm (c :: marks.map Prod.fst) := by
  induction marks with
  | nil => simp [insertMark]
  | cons m rest ih =>
    unfold insertMark
    split
    · simp
    · -- The mark goes past the first entry, so the two swap.
      simp only [List.map_cons]
      exact (ih.cons m.1).trans (List.Perm.swap c m.1 _)

/-- A fold whose steps keep the characters seen, in some order, keeps them all. -/
private theorem foldl_perm (f : Array Char × List (Char × Nat) → Char →
      Array Char × List (Char × Nat))
    (step : ∀ acc c, ((f acc c).1.toList ++ (f acc c).2.map Prod.fst).Perm
      (acc.1.toList ++ acc.2.map Prod.fst ++ [c])) :
    ∀ (chars : List Char) (acc : Array Char × List (Char × Nat)),
      ((chars.foldl f acc).1.toList ++ (chars.foldl f acc).2.map Prod.fst).Perm
        (acc.1.toList ++ acc.2.map Prod.fst ++ chars)
  | [], acc => by simp
  | c :: chars, acc => by
    simp only [List.foldl_cons]
    refine (foldl_perm f step chars (f acc c)).trans ?_
    -- One step, then the rest.
    have := (step acc c).append_right chars
    simpa [List.append_assoc] using this

/-- The output of such a fold from an empty start, then its last run, reorders the input. -/
private theorem foldl_flush_perm (f : Array Char × List (Char × Nat) → Char →
      Array Char × List (Char × Nat))
    (step : ∀ acc c, ((f acc c).1.toList ++ (f acc c).2.map Prod.fst).Perm
      (acc.1.toList ++ acc.2.map Prod.fst ++ [c]))
    (chars : List Char) :
    (match chars.foldl f ((#[] : Array Char), []) with
      | (out, marks) => (out ++ marks.map Prod.fst).toList).Perm chars := by
  have key := foldl_perm f step chars ((#[] : Array Char), [])
  revert key
  -- Name the result of the fold, so the match on it reduces.
  generalize chars.foldl f ((#[] : Array Char), []) = result
  obtain ⟨out, marks⟩ := result
  simp

/-- Canonical ordering only reorders the characters. -/
theorem canonicalOrder_perm (chars : List Char) : (canonicalOrder chars).Perm chars := by
  unfold canonicalOrder
  apply foldl_flush_perm
  · intro acc c
    obtain ⟨out, marks⟩ := acc
    dsimp only
    split
    · simp
    · simp only [List.append_assoc]
      refine List.Perm.append_left _ ?_
      exact (insertMark_perm c _ marks).trans (List.perm_append_singleton c _).symm

/-- A fold whose steps push a starter onto an empty run leaves a list of starters as it is. -/
private theorem foldl_starters (f : Array Char × List (Char × Nat) → Char →
      Array Char × List (Char × Nat))
    (step : ∀ out c, combiningClass c = 0 → f (out, []) c = (out.push c, [])) :
    ∀ (chars : List Char) (out : Array Char), (∀ c ∈ chars, combiningClass c = 0) →
      chars.foldl f (out, []) = (out ++ chars.toArray, [])
  | [], out, _ => by simp
  | c :: chars, out, starters => by
    simp only [List.foldl_cons, step out c (starters c (by simp))]
    rw [foldl_starters f step chars (out.push c) (fun d hd => starters d (by simp [hd]))]
    simp

/-- Canonical ordering leaves a list of starters as it is. -/
theorem canonicalOrder_of_starters {chars : List Char}
    (starters : ∀ c ∈ chars, combiningClass c = 0) : canonicalOrder chars = chars := by
  unfold canonicalOrder
  rw [foldl_starters _ (fun out c h => by simp [h]) chars #[] starters]
  simp

/-! ## NFKD -/

/-- Text below U+00A0, which holds all of ASCII, is its own NFKD form. -/
theorem nfkd_of_lt {text : String} (below : ∀ c ∈ text.toList, c.toNat < 0xA0) :
    nfkd text = text := by
  unfold nfkd
  -- Each character decomposes to itself.
  have same : ∀ chars : List Char, (∀ c ∈ chars, c.toNat < 0xA0) →
      chars.flatMap decompose = chars := by
    intro chars low
    induction chars with
    | nil => rfl
    | cons c rest ih =>
      rw [List.flatMap_cons, decompose_of_lt (low c (by simp)),
        ih fun d hd => low d (by simp [hd])]
      rfl
  -- Each character is a starter, so ordering changes nothing.
  rw [same _ below]
  rw [canonicalOrder_of_starters fun c hc => combiningClass_of_lt (by have := below c hc; omega)]
  exact String.ofList_toList

end EthLib.Cryptography.Unicode
