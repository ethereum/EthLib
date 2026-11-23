module

public import EthLib.Base.Json

/-!
# Proofs: reading a JSON text from a position

The reader walks a text by its positions, without a list of its characters.

Each step is described here by the characters after a position.

So a step reads like an operation on a list: whitespace is dropped, a run of digits is spanned.
-/

@[expose] public section

namespace EthLib.Base.Json

variable {text : String}

/-- The characters of a text from a position to its end. -/
def after (p : text.Pos) : List Char :=
  (text.sliceFrom p).copy.toList

/-! ## The characters after a position -/

/-- All the characters of a text come after its first position. -/
theorem after_startPos (text : String) : after text.startPos = text.toList := by
  simp [after]

/-- No character comes after the end of a text, and the end is the only such position. -/
theorem after_eq_nil_iff {p : text.Pos} : after p = [] ↔ p = text.endPos := by
  constructor
  · intro h
    -- The text splits at the position into what is before it and the empty text.
    have empty : (text.sliceFrom p).copy = "" := by
      rw [← String.toList_inj]
      simpa [after] using h
    have splits : p.Splits (text.sliceTo p).copy "" := by
      have := p.splits
      rwa [empty] at this
    exact (String.Pos.splits_empty_right_iff.1 splits).1
  · rintro rfl
    simp [after]

/-- The characters after a position that is not the end are its character, then those after it. -/
theorem after_eq_get_cons {p : text.Pos} (hp : p ≠ text.endPos) :
    after p = p.get hp :: after (p.next hp) := by
  have splits := String.Pos.splits_next_right p hp
  simp [after, splits.copy_sliceFrom_eq]

/-- A position with a character after it is not the end, and the character is the one read there. -/
theorem after_eq_cons {p : text.Pos} {c : Char} {cs : List Char} (h : after p = c :: cs) :
    ∃ hp : p ≠ text.endPos, p.get hp = c ∧ after (p.next hp) = cs := by
  have hp : p ≠ text.endPos := fun e => by simp [(after_eq_nil_iff).2 e] at h
  rw [after_eq_get_cons hp, List.cons.injEq] at h
  exact ⟨hp, h.1, h.2⟩

/-- Two positions of a text with the same characters after them are equal. -/
theorem eq_of_after_eq {p q : text.Pos} (h : after p = after q) : p = q := by
  have same : (text.sliceFrom p).copy = (text.sliceFrom q).copy := by
    rw [← String.toList_inj]
    simpa [after] using h
  have splits := q.splits
  rw [← same] at splits
  exact p.splits.pos_eq_of_eq_right splits

/-- The text between two positions is the characters that the second position leaves out. -/
theorem extract_of_after : ∀ (chars : List Char) {p q : text.Pos},
    after p = chars ++ after q → p ≤ q ∧ text.extract p q = String.ofList chars
  | [], p, q, h => by
    obtain rfl := eq_of_after_eq (by simpa using h)
    exact ⟨String.Pos.le_refl _,
      by simp [String.extract_eq_copy_slice _ _ (String.Pos.le_refl _)]⟩
  | c :: chars, p, q, h => by
    obtain ⟨hp, hc, hn⟩ := after_eq_cons (by simpa using h)
    obtain ⟨le, extract⟩ := extract_of_after chars hn
    have lt : p < q := Std.lt_of_lt_of_le String.Pos.lt_next le
    refine ⟨Std.le_of_lt lt, ?_⟩
    rw [String.extract_eq_copy_slice _ _ (Std.le_of_lt lt), String.copy_slice_eq_append_of_lt lt]
    rw [String.extract_eq_copy_slice _ _ le] at extract
    simp [extract, hc]

/-! ## The steps of the reader -/

/-- The whitespace skipped from a position is the whitespace that starts its characters. -/
theorem after_skipWhitespace (p : text.Pos) :
    after (skipWhitespace p) = (after p).dropWhile whitespace := by
  induction p using WellFounded.induction (String.Pos.wellFounded_gt) with
  | h p ih =>
    rw [skipWhitespace]
    split
    · rename_i e
      simp [e, (after_eq_nil_iff).2 rfl]
    · rename_i hp
      rw [after_eq_get_cons hp]
      split
      · rename_i w
        rw [ih _ String.Pos.lt_next, List.dropWhile_cons_of_pos w]
      · rename_i w
        rw [after_eq_get_cons hp, List.dropWhile_cons_of_neg w]

/-- One character is read when it comes next. -/
theorem expect_of_after {p : text.Pos} {c : Char} {cs : List Char} (h : after p = c :: cs) :
    ∃ q, expect p c = some q ∧ after q = cs := by
  obtain ⟨hp, hc, hn⟩ := after_eq_cons h
  exact ⟨p.next hp, by simp [expect, hp, hc], hn⟩

/-- A character that does not come next is not read. -/
theorem expect_eq_none {p : text.Pos} {c : Char} (h : (after p).head? ≠ some c) :
    expect p c = none := by
  unfold expect
  split
  · rfl
  · rename_i hp
    rw [after_eq_get_cons hp] at h
    simp only [List.head?_cons, ne_eq, Option.some.injEq] at h
    simp [h]

/-- What a read character leaves is the characters after it. -/
theorem after_of_expect {p q : text.Pos} {c : Char} (h : expect p c = some q) :
    after p = c :: after q := by
  unfold expect at h
  split at h
  · simp at h
  · rename_i hp
    split at h
    · rename_i hc
      obtain rfl := Option.some.inj h
      rw [after_eq_get_cons hp, hc]
    · simp at h

/-- The characters a string holds without an escape run to the first one that needs it. -/
theorem after_plainEnd (p : text.Pos) :
    after (plainEnd p) = (after p).dropWhile plain := by
  induction p using WellFounded.induction (String.Pos.wellFounded_gt) with
  | h p ih =>
    rw [plainEnd]
    split
    · rename_i e
      simp [e, (after_eq_nil_iff).2 rfl]
    · rename_i hp
      rw [after_eq_get_cons hp]
      split
      · rename_i go
        rw [ih _ String.Pos.lt_next, List.dropWhile_cons_of_pos go]
      · rename_i stop
        rw [after_eq_get_cons hp, List.dropWhile_cons_of_neg stop]

/-- The text copied from a run of characters without an escape is that run. -/
theorem extract_plainEnd (p : text.Pos) :
    text.extract p (plainEnd p) = String.ofList ((after p).takeWhile plain) := by
  obtain ⟨-, extract⟩ := extract_of_after ((after p).takeWhile plain) (p := p) (q := plainEnd p)
    (by rw [after_plainEnd, List.takeWhile_append_dropWhile])
  exact extract

/-- The digits from a position give the value of the run of digits that starts there.

The count grows by the length of the run, and the position moves past it. -/
theorem digits_eq (p : text.Pos) (value count : Nat) :
    ∃ q, digits p value count =
        (((after p).takeWhile digit).foldl digitStep value,
          count + ((after p).takeWhile digit).length, q) ∧
      after q = (after p).dropWhile digit := by
  induction p using WellFounded.induction (String.Pos.wellFounded_gt) generalizing value count with
  | h p ih =>
    rw [digits]
    split
    · rename_i e
      exact ⟨p, by simp [e, (after_eq_nil_iff).2 rfl], by simp [e, (after_eq_nil_iff).2 rfl]⟩
    · rename_i hp
      dsimp only
      split
      · rename_i d
        obtain ⟨q, eq, rest⟩ :=
          ih (p.next hp) String.Pos.lt_next (digitStep value (p.get hp)) (count + 1)
        refine ⟨q, ?_, ?_⟩
        · rw [eq, after_eq_get_cons hp, List.takeWhile_cons_of_pos d]
          simp only [List.foldl_cons, List.length_cons]
          refine Prod.ext rfl (Prod.ext ?_ rfl)
          simp only
          omega
        · rw [rest, after_eq_get_cons hp, List.dropWhile_cons_of_pos d]
      · rename_i d
        refine ⟨p, ?_, ?_⟩
        · rw [after_eq_get_cons hp, List.takeWhile_cons_of_neg d]
          simp
        · rw [after_eq_get_cons hp, List.dropWhile_cons_of_neg d]

end EthLib.Base.Json
