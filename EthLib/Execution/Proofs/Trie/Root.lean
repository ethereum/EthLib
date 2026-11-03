module

public import EthLib.Execution.Trie.Root

/-!
# Proofs: `Trie.Root`

- The budget of `patricialize` never runs out: any budget above the longest path, counted from the level, gives the same node.
- The root of the empty map is the hash of `0x80`, secured or not.
- A map with an empty value has no root, and every other map's keys and values reach `patricialize` unchanged, in order.
-/

@[expose] public section

namespace EthLib.Execution.Trie

open EthLib.Base
open EthLib.Serialization.Rlp

/-! ## The longest path -/

/-- Folding from any start value gives the larger of the start and the longest path. -/
theorem foldl_longestPath (obj : List (List Nibble × ByteArray)) (start : Nat) :
    obj.foldl (fun longest (key, _) => max longest key.length) start = max start (longestPath obj) := by
  induction obj generalizing start with
  | nil => simp [longestPath]
  | cons entry rest ih =>
    -- One step of the fold on both sides, then the induction hypothesis twice.
    simp only [longestPath, List.foldl_cons] at ih ⊢
    rw [ih, ih (max 0 entry.1.length)]
    omega

/-- The longest path is at most `n` exactly when every path is. -/
theorem longestPath_le_iff (obj : List (List Nibble × ByteArray)) (n : Nat) :
    longestPath obj ≤ n ↔ ∀ entry ∈ obj, entry.1.length ≤ n := by
  induction obj with
  | nil => simp [longestPath]
  | cons entry rest ih =>
    have h := foldl_longestPath rest (max 0 entry.1.length)
    simp only [longestPath, List.foldl_cons] at h ih ⊢
    rw [h, List.forall_mem_cons, ← ih]
    omega

/-- Keeping some of the keys keeps the longest path or shortens it. -/
theorem longestPath_filter_le (obj : List (List Nibble × ByteArray)) (p : List Nibble × ByteArray → Bool) :
    longestPath (obj.filter p) ≤ longestPath obj := by
  rw [longestPath_le_iff]
  intro entry h
  exact (longestPath_le_iff obj _).mp (Nat.le_refl _) entry (List.mem_filter.mp h).1

/-! ## One step of `patricialize` -/

/-- `mapMVector` gives the same result for two functions that agree on every entry. -/
theorem mapMVector_congr {α β ε : Type} {f g : α → Except ε β} :
    (xs : List α) → (∀ x ∈ xs, f x = g x) → mapMVector f xs = mapMVector g xs
  | [], _ => rfl
  | x :: rest, h => by
    simp only [mapMVector]
    rw [h x List.mem_cons_self, mapMVector_congr rest fun y hy => h y (List.mem_cons_of_mem x hy)]

/-- A fold that takes minimums ends at most at its start. -/
theorem foldl_min_le (obj : List (List Nibble × ByteArray)) (f : List Nibble × ByteArray → Nat) (start : Nat) :
    obj.foldl (fun length entry => min length (f entry)) start ≤ start := by
  induction obj generalizing start with
  | nil => exact Nat.le_refl _
  | cons entry rest ih => exact Nat.le_trans (ih _) (Nat.min_le_left _ _)

/-- One step gives the same node for two ways of making the nested calls, when they agree on the calls the step makes.

- An extension calls on the same keys, at a level above `level` and at most the longest path.
- A branch calls on the keys of each next nibble, one level down. -/
theorem patricializeStep_congr (hash : ByteArray → Hash32)
    {recurse₁ recurse₂ : List (List Nibble × ByteArray) → Nat → Except RlpError (Option InternalNode)}
    {obj : List (List Nibble × ByteArray)} {level : Nat}
    (hextension : ∀ deeper, level < deeper → deeper ≤ longestPath obj → recurse₁ obj deeper = recurse₂ obj deeper)
    (hbranch : ∀ nibble : Nibble,
      recurse₁ (obj.filter fun (key, _) => key[level]? = some nibble) (level + 1)
        = recurse₂ (obj.filter fun (key, _) => key[level]? = some nibble) (level + 1)) :
    patricializeStep hash recurse₁ obj level = patricializeStep hash recurse₂ obj level := by
  match obj, hextension, hbranch with
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | (arbitraryKey, arbitraryValue) :: second :: rest, hextension, hbranch =>
    simp only [patricializeStep]
    -- The run is at most the rest of the first path, so an extension lands at most at its end.
    have hrun := foldl_min_le ((arbitraryKey, arbitraryValue) :: second :: rest)
      (fun entry => commonPrefixLength (arbitraryKey.drop level) (entry.1.drop level)) (arbitraryKey.drop level).length
    have hdrop : (arbitraryKey.drop level).length = arbitraryKey.length - level := List.length_drop
    have hfirst : arbitraryKey.length ≤ longestPath ((arbitraryKey, arbitraryValue) :: second :: rest) :=
      (longestPath_le_iff ((arbitraryKey, arbitraryValue) :: second :: rest) _).mp (Nat.le_refl _)
        (arbitraryKey, arbitraryValue) List.mem_cons_self
    split
    · rename_i hpositive
      rw [hextension _ (by omega) (by omega)]
    · -- Each child is the filter of one nibble, on which the two agree.
      congr 1
      apply mapMVector_congr
      intro nibble _
      rw [hbranch nibble]

/-- With fewer than two keys, a step makes no nested call. -/
theorem patricializeStep_of_length_lt (hash : ByteArray → Hash32)
    (recurse₁ recurse₂ : List (List Nibble × ByteArray) → Nat → Except RlpError (Option InternalNode))
    {obj : List (List Nibble × ByteArray)} (hlength : obj.length < 2) (level : Nat) :
    patricializeStep hash recurse₁ obj level = patricializeStep hash recurse₂ obj level := by
  match obj, hlength with
  | [], _ => rfl
  | [_], _ => rfl

/-- A call on no key gives no node, whatever the budget. -/
theorem patricializeAux_nil (hash : ByteArray → Hash32) (fuel level : Nat) :
    patricializeAux hash fuel [] level = .ok none := by
  cases fuel <;> rfl

/-! ## The budget never runs out -/

/-- A budget fits a call when the call has fewer than two keys, or every path ends before `level + fuel`. -/
def Fits (obj : List (List Nibble × ByteArray)) (level fuel : Nat) : Prop :=
  obj.length < 2 ∨ longestPath obj < level + fuel

/-- One more unit of a budget that fits changes nothing. -/
theorem patricializeAux_succ (hash : ByteArray → Hash32) :
    (fuel : Nat) → (obj : List (List Nibble × ByteArray)) → (level : Nat) → Fits obj level fuel →
      patricializeAux hash (fuel + 1) obj level = patricializeAux hash fuel obj level
  | fuel, obj, level, .inl hlength => by
    cases fuel <;> exact patricializeStep_of_length_lt hash _ _ hlength level
  | 0, obj, level, .inr hlongest => by
    -- Every path ends before `level`, so no extension is made and every child has no key.
    apply patricializeStep_congr
    · intro deeper hdeeper hle
      omega
    · intro nibble
      have hempty : (obj.filter fun (key, _) => key[level]? = some nibble) = [] := by
        rw [List.filter_eq_nil_iff]
        intro entry hmem
        have := (longestPath_le_iff obj _).mp (Nat.le_refl _) entry hmem
        simp [List.getElem?_eq_none (show entry.1.length ≤ level by omega)]
      rw [hempty, patricializeAux_nil]
  | fuel + 1, obj, level, .inr hlongest => by
    -- Each nested call fits the smaller budget, so the induction hypothesis applies to it.
    apply patricializeStep_congr
    · intro deeper hdeeper hle
      exact patricializeAux_succ hash fuel obj deeper (.inr (by omega))
    · intro nibble
      exact patricializeAux_succ hash fuel _ (level + 1)
        (.inr (Nat.lt_of_le_of_lt (longestPath_filter_le obj _) (by omega)))

/-- Any larger budget than one that fits changes nothing. -/
theorem patricializeAux_add (hash : ByteArray → Hash32) {obj : List (List Nibble × ByteArray)} {level fuel : Nat}
    (hfits : Fits obj level fuel) (extra : Nat) :
    patricializeAux hash (fuel + extra) obj level = patricializeAux hash fuel obj level := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
    rw [← Nat.add_assoc, patricializeAux_succ hash _ obj level (hfits.imp_right fun h => by omega), ih]

/-- Every budget that reaches past the longest path gives the node of `patricialize`. -/
theorem patricializeAux_eq_patricialize (hash : ByteArray → Hash32) {obj : List (List Nibble × ByteArray)}
    {level fuel : Nat} (hfuel : longestPath obj < level + fuel) :
    patricializeAux hash fuel obj level = patricialize hash obj level := by
  have hfits : Fits obj level fuel := .inr hfuel
  have hdefault : Fits obj level (longestPath obj + 1) := .inr (by omega)
  -- Both budgets give the node of their sum.
  rw [patricialize, ← patricializeAux_add hash hfits (longestPath obj + 1),
    ← patricializeAux_add hash hdefault fuel, Nat.add_comm]

/-! ## The root -/

/-- The empty map's root is the hash of `0x80`, the encoding of the empty byte string, secured or not. -/
theorem root_empty (hash : ByteArray → Hash32) (secured : Bool) :
    root hash ⟨secured, []⟩ = .ok (hash ⟨#[0x80]⟩) := rfl

/-- A map with an empty value has no root. -/
theorem prepareData_emptyValue (hash : ByteArray → Hash32) (secured : Bool) :
    (data : List (ByteArray × ByteArray)) → (∃ entry ∈ data, entry.2.size = 0) →
      prepareData hash data secured = .error .emptyValue
  | (key, value) :: rest, ⟨entry, hmem, hempty⟩ => by
    by_cases hvalue : value.size = 0
    · simp only [prepareData, List.mapM_cons, hvalue, ↓reduceIte]
      rfl
    · -- The first value is not empty, so the empty one is further on.
      have hrest : ∃ entry ∈ rest, entry.2.size = 0 := by
        rcases List.mem_cons.mp hmem with rfl | h
        · exact absurd hempty hvalue
        · exact ⟨entry, h, hempty⟩
      have hrestError := prepareData_emptyValue hash secured rest hrest
      simp only [prepareData] at hrestError
      simp only [prepareData, List.mapM_cons, hvalue, ↓reduceIte, hrestError]
      rfl

/-- A map with an empty value has no root. -/
theorem root_emptyValue (hash : ByteArray → Hash32) (trie : Trie) (h : ∃ entry ∈ trie.data, entry.2.size = 0) :
    root hash trie = .error .emptyValue := by
  simp only [root, prepareData_emptyValue hash trie.secured trie.data h]
  rfl

/-- With no empty value, each key becomes its path, after hashing in a secured trie, and keeps its value and its place. -/
theorem prepareData_ok (hash : ByteArray → Hash32) (secured : Bool) :
    (data : List (ByteArray × ByteArray)) → (∀ entry ∈ data, entry.2.size ≠ 0) →
      prepareData hash data secured
        = .ok (data.map fun (preimage, value) => (keyPath hash secured preimage, value))
  | [], _ => rfl
  | (key, value) :: rest, h => by
    have hrest := prepareData_ok hash secured rest fun entry hmem => h entry (List.mem_cons_of_mem _ hmem)
    simp only [prepareData] at hrest
    simp only [prepareData, List.mapM_cons, h (key, value) List.mem_cons_self, ↓reduceIte, hrest]
    rfl

end EthLib.Execution.Trie
