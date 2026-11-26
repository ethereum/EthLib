module

public import EthLib.Base.List
import Std.Data.TreeMap.Lemmas
import Std.Data.TreeSet.Lemmas

/-!
# `Base.Proofs.List`

Facts about lists that Lean core does not prove and that several layers use.

They cover duplicates, sums and their bounds, the front of a list, searches in arrays and maxima.

They also invert the readers of a prefix and of a suffix.

The prefix reader is also a test of the prefix, then a drop of its length.

A table with a key set reads that value at the key, and the old values at the other keys.
-/

@[expose] public section

namespace EthLib.Base

/-- A table with a key set reads the value it was set to at that key. -/
theorem lookup_replaceKey_self {κ α : Type} [BEq κ] [LawfulBEq κ] (pairs : List (κ × α))
    (key : κ) (value : α) : (replaceKey pairs key value).lookup key = some value := by
  unfold replaceKey
  by_cases h : pairs.any (·.1 == key) = true
  · simp only [h, ↓reduceIte]
    induction pairs with
    | nil => simp at h
    | cons e t ih =>
      by_cases he : e.1 = key
      · simp [he]
      · have hb : (e.1 == key) = false := by simpa using he
        simp only [List.any_cons, hb, Bool.false_or] at h
        have he' : (key == e.1) = false := by simpa using Ne.symm he
        simp [List.lookup, he, he', ih h]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    induction pairs with
    | nil => simp
    | cons e t ih =>
      by_cases he : e.1 = key
      · simp [he] at h
      · have hb : (e.1 == key) = false := by simpa using he
        simp only [List.any_cons, hb, Bool.false_or] at h
        have he' : (key == e.1) = false := by simpa using Ne.symm he
        simp [List.lookup, he', ih h]

/-- A table with a key set reads as before at every other key. -/
theorem lookup_replaceKey_of_ne {κ α : Type} [BEq κ] [LawfulBEq κ] (pairs : List (κ × α))
    {key other : κ} (value : α) (ne : other ≠ key) :
    (replaceKey pairs key value).lookup other = pairs.lookup other := by
  unfold replaceKey
  have hk : (other == key) = false := by simpa using ne
  by_cases hc : pairs.any (·.1 == key) = true
  · simp only [hc, ↓reduceIte]
    clear hc
    induction pairs with
    | nil => simp
    | cons e t ih =>
      by_cases he : e.1 = key
      · simp [List.lookup, he, hk, ih]
      · by_cases ho : other = e.1
        · simp [List.lookup, he, ho]
        · have ho' : (other == e.1) = false := by simpa using ho
          simp [List.lookup, he, ho', ih]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    clear hc
    induction pairs with
    | nil => simp [List.lookup, hk]
    | cons e t ih =>
      by_cases ho : other = e.1
      · simp [List.lookup, ho]
      · have ho' : (other == e.1) = false := by simpa using ho
        simp [List.lookup, ho', ih]

/-- A list that starts with a prefix leaves what follows the prefix. -/
theorem dropPrefix?_append {α : Type} [DecidableEq α] :
    (pre rest : List α) → dropPrefix? pre (pre ++ rest) = some rest
  | [], _ => rfl
  | c :: pre, rest => by simp [dropPrefix?, dropPrefix?_append pre rest]

/-- A list from which a prefix leaves a rest is that prefix, then the rest. -/
theorem eq_append_of_dropPrefix? {α : Type} [DecidableEq α] :
    {pre cs rest : List α} → dropPrefix? pre cs = some rest → cs = pre ++ rest
  | [], cs, rest, h => by
    simp only [dropPrefix?, Option.some.injEq] at h
    simp [h]
  | c :: pre, d :: cs, rest, h => by
    simp only [dropPrefix?] at h
    split at h
    · rename_i same
      simp [same, eq_append_of_dropPrefix? h]
    · cases h
  | _ :: _, [], _, h => by simp [dropPrefix?] at h

/-- The rest after a prefix, read as a test of the prefix, then a drop of its length. -/
theorem dropPrefix?_eq {α : Type} [DecidableEq α] :
    (pre cs : List α) → dropPrefix? pre cs =
      if pre.isPrefixOf cs then some (cs.drop pre.length) else none
  | [], cs => by simp [dropPrefix?]
  | _ :: _, [] => by simp [dropPrefix?]
  | p :: pre, c :: cs => by
    by_cases h : p = c
    · subst h
      simp [dropPrefix?, dropPrefix?_eq pre cs]
    · simp [dropPrefix?, h]

/-- A list that ends with a suffix gives back the start. -/
theorem dropSuffix?_append {α : Type} [DecidableEq α] (start suf : List α) :
    dropSuffix? suf (start ++ suf) = some start := by
  simp [dropSuffix?]

/-- A list that gives back a start is the start followed by the suffix. -/
theorem eq_append_of_dropSuffix? {α : Type} [DecidableEq α] {suf cs start : List α}
    (h : dropSuffix? suf cs = some start) : cs = start ++ suf := by
  unfold dropSuffix? at h
  split at h
  · rename_i hs
    cases h
    exact (List.suffix_iff_eq_append.mp (List.isSuffixOf_iff_suffix.mp hs)).symm
  · cases h

/-- Removing the duplicates of a list leaves a list in which each element comes once. -/
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

/-- Removing the duplicates of a list by a test keeps a part of it, in order. -/
theorem eraseDupsBy_sublist {α : Type} (r : α → α → Bool) :
    ∀ l : List α, (l.eraseDupsBy r).Sublist l
  | [] => List.Sublist.slnil
  | head :: tail => by
    rw [List.eraseDupsBy_cons]
    exact ((eraseDupsBy_sublist r _).trans List.filter_sublist).cons_cons head
termination_by l => l.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- The first items of a zip are a sublist of the first list. -/
theorem map_fst_zip_sublist {α β : Type} (xs : List α) (ys : List β) :
    ((xs.zip ys).map Prod.fst).Sublist xs := by
  rw [List.zip_eq_zip_take_min, List.map_fst_zip (by simp)]
  exact List.take_sublist _ _

/-- The keys of a list without repeated keys are its keys without duplicates. -/
theorem map_eraseDupsBy {α β : Type} [BEq β] (key : α → β) :
    ∀ l : List α, (l.eraseDupsBy fun a b => key a == key b).map key = (l.map key).eraseDups
  | [] => rfl
  | head :: tail => by
    rw [List.eraseDupsBy_cons, List.map_cons, map_eraseDupsBy key, List.map_cons,
      List.eraseDups_cons, List.filter_map]
    congr 3
termination_by l => l.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- An element that a filter keeps sits in the list after kept elements and dropped ones. -/
theorem eq_append_cons_of_filter {α : Type} {p : α → Bool} {l before after : List α} {a : α}
    (kept : l.filter p = before ++ a :: after) :
    ∃ front back, l = front ++ a :: back ∧ ∀ x ∈ front, x ∈ before ∨ p x = false := by
  obtain ⟨l₁, l₂, rfl, first, second⟩ := List.filter_eq_append_iff.1 kept
  obtain ⟨m₁, m₂, rfl, dropped, -, -⟩ := List.filter_eq_cons_iff.1 second
  refine ⟨l₁ ++ m₁, m₂, by simp, fun x mem => ?_⟩
  rcases List.mem_append.1 mem with early | late
  · by_cases keep : p x = true
    · exact .inl (first ▸ List.mem_filter.2 ⟨early, keep⟩)
    · exact .inr (by simpa using keep)
  · exact .inr (by simpa using dropped x late)

/-- Each element that removing repeated keys keeps is the first of its key in the list. -/
theorem eq_append_cons_of_mem_eraseDupsBy {α β : Type} [BEq β] [LawfulBEq β] (key : α → β)
    {a : α} : ∀ l : List α, a ∈ l.eraseDupsBy (fun x y => key x == key y) →
      ∃ front back, l = front ++ a :: back ∧ ∀ x ∈ front, key x ≠ key a
  | [], mem => by simp at mem
  | head :: tail, mem => by
    rw [List.eraseDupsBy_cons, List.mem_cons] at mem
    rcases mem with rfl | later
    · exact ⟨[], tail, rfl, by simp⟩
    · -- The element is first of its key among the elements of another key than the head.
      obtain ⟨front, back, split, first⟩ := eq_append_cons_of_mem_eraseDupsBy key _ later
      have other : key a ≠ key head := by
        have kept := (List.mem_filter.1 (split ▸ List.mem_append_right front
          (List.mem_cons_self (a := a) (l := back))))
        simpa using kept.2
      obtain ⟨front', back', rfl, sorted⟩ := eq_append_cons_of_filter split
      refine ⟨head :: front', back', rfl, fun x mem => ?_⟩
      rcases List.mem_cons.1 mem with rfl | rest
      · exact fun same => other same.symm
      · rcases sorted x rest with known | dropped
        · exact first x known
        · -- A dropped element has the key of the head, which is not the key of the element.
          have keyed : key x = key head := by simpa using dropped
          exact fun same => other (same ▸ keyed)
termination_by l => l.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Two maps that agree on a list keep the same elements of it. -/
theorem filterMap_congr {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  -- Mathlib proves the same fact, and this copy keeps the base layer free of Mathlib.
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h a (by simp),
      filterMap_congr fun b hb => h b (by simp [hb])]

/-- Each term at least `low` makes the sum at least the count times `low`. -/
theorem le_sum_map {α : Type} {f : α → Nat} {low : Nat} :
    ∀ {xs : List α}, (∀ x ∈ xs, low ≤ f x) → xs.length * low ≤ (xs.map f).sum
  | [], _ => by simp
  | x :: xs, h => by
    have hx := h x List.mem_cons_self
    have := le_sum_map (xs := xs) fun y hy => h y (List.mem_cons_of_mem x hy)
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.succ_mul]
    omega

/-- Each term at most `high` makes the sum at most the count times `high`. -/
theorem sum_map_le {α : Type} {f : α → Nat} {high : Nat} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x ≤ high) → (xs.map f).sum ≤ xs.length * high
  | [], _ => by simp
  | x :: xs, h => by
    have hx := h x List.mem_cons_self
    have := sum_map_le (xs := xs) fun y hy => h y (List.mem_cons_of_mem x hy)
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.succ_mul]
    omega

/-- Bounds on each term of a sum bound it by the sum of those bounds. -/
theorem sum_map_le_sum_map {α : Type} {f g : α → Nat} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x ≤ g x) → (xs.map f).sum ≤ (xs.map g).sum
  | [], _ => by simp
  | x :: xs, h => by
    have hx := h x List.mem_cons_self
    have := sum_map_le_sum_map (xs := xs) fun y hy => h y (List.mem_cons_of_mem x hy)
    simp only [List.map_cons, List.sum_cons]
    omega

/-- A factor on the left of every term comes out of the sum. -/
theorem sum_map_mul_left {α : Type} (factor : Nat) (f : α → Nat) :
    ∀ xs : List α, (xs.map fun x => factor * f x).sum = factor * (xs.map f).sum
  | [] => by simp
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons, Nat.mul_add, sum_map_mul_left factor f xs]

/-- A factor on the right of every term comes out of the sum. -/
theorem sum_map_mul_right {α : Type} (f : α → Nat) (factor : Nat) :
    ∀ xs : List α, (xs.map fun x => f x * factor).sum = (xs.map f).sum * factor
  | [] => by simp
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons, Nat.add_mul, sum_map_mul_right f factor xs]

/-- The quotients of the terms sum to at most the quotient of the sum. -/
theorem sum_map_div_le {α : Type} (f : α → Nat) (divisor : Nat) :
    ∀ xs : List α, (xs.map fun x => f x / divisor).sum ≤ (xs.map f).sum / divisor
  | [] => by simp
  | x :: xs => by
    have rest := sum_map_div_le f divisor xs
    simp only [List.map_cons, List.sum_cons]
    rcases Nat.eq_zero_or_pos divisor with zero | positive
    · subst zero
      simp only [Nat.div_zero] at rest ⊢
      omega
    · refine (Nat.le_div_iff_mul_le positive).mpr ?_
      have first := Nat.div_mul_le_self (f x) divisor
      have second := Nat.div_mul_le_self (xs.map f).sum divisor
      have kept := Nat.mul_le_mul_right divisor rest
      rw [Nat.add_mul]
      omega

/-- Dropping the terms that are 0 keeps a sum. -/
theorem sum_map_filter_ne_zero {α : Type} (f : α → Nat) :
    ∀ xs : List α, ((xs.filter fun x => f x ≠ 0).map f).sum = (xs.map f).sum
  | [] => rfl
  | x :: xs => by
    have ih := sum_map_filter_ne_zero f xs
    by_cases hx : f x = 0 <;> simp_all

/-- Two lists without repeats that each hold every element with a nonzero term give the same sum. -/
theorem sum_map_eq_of_nodup {α : Type} {f : α → Nat} {xs ys : List α} (dx : xs.Nodup)
    (dy : ys.Nodup) (hx : ∀ a, f a ≠ 0 → a ∈ xs) (hy : ∀ a, f a ≠ 0 → a ∈ ys) :
    (xs.map f).sum = (ys.map f).sum := by
  rw [← sum_map_filter_ne_zero f xs, ← sum_map_filter_ne_zero f ys]
  refine List.Perm.sum_nat (List.Perm.map f ?_)
  refine (List.perm_ext_iff_of_nodup (dx.filter _) (dy.filter _)).mpr fun a => ?_
  simp only [List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => ⟨hy a h.2, h.2⟩, fun h => ⟨hx a h.2, h.2⟩⟩

/-- A change of one term of a sum over distinct elements changes the sum by the same amount.

The two functions agree at every element other than `a`, which the list holds. -/
theorem sum_map_add_eq_of_eq_off {α : Type} {f g : α → Nat} {a : α}
    (h : ∀ x, x ≠ a → g x = f x) :
    ∀ {xs : List α}, xs.Nodup → a ∈ xs → (xs.map g).sum + f a = (xs.map f).sum + g a
  | [], _, ha => absurd ha List.not_mem_nil
  | x :: xs, d, ha => by
    obtain ⟨hx, d⟩ := List.nodup_cons.mp d
    simp only [List.map_cons, List.sum_cons]
    by_cases hxa : x = a
    · subst hxa
      have hrest : xs.map g = xs.map f :=
        List.map_congr_left fun y hy => h y fun e => hx (e ▸ hy)
      rw [hrest]
      omega
    · have ha' : a ∈ xs := by
        rcases List.mem_cons.mp ha with e | e
        · exact absurd e.symm hxa
        · exact e
      have := sum_map_add_eq_of_eq_off h d ha'
      rw [h x hxa]
      omega

/-- A sum of a value where a test holds, and zero elsewhere, is its sum over the passing entries. -/
theorem sum_map_ite_eq_sum_filter {α : Type} (test : α → Prop) [DecidablePred test]
    (value : α → Nat) (entries : List α) :
    (entries.map fun entry => if test entry then value entry else 0).sum =
      ((entries.filter fun entry => test entry).map value).sum := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => by_cases passes : test entry <;> simp [passes, ih]

/-- Dropping the front where a test holds keeps each member that fails the test. -/
theorem mem_dropWhile_of_eq_false {α : Type} {test : α → Bool} {member : α}
    (failed : test member = false) {list : List α} (found : member ∈ list) :
    member ∈ list.dropWhile test := by
  rw [← List.takeWhile_append_dropWhile (p := test) (l := list), List.mem_append] at found
  rcases found with taken | kept
  · have passed := List.all_eq_true.mp List.all_takeWhile member taken
    rw [failed] at passed
    cases passed
  · exact kept

/-- Numbering the first `i` elements of a list gives the first `i` elements of the numbered list. -/
theorem zipIdx_take {α : Type} (l : List α) (i : Nat) : (l.take i).zipIdx = l.zipIdx.take i := by
  apply List.ext_getElem?
  intro n
  simp only [List.getElem?_zipIdx, List.getElem?_take]
  split <;> simp

/-- An array holds an element that passes a test whenever a search for one finds it. -/
theorem any_eq_true_of_find?_eq_some {α : Type} {p : α → Bool} {xs : Array α} {x : α}
    (found : xs.find? p = some x) : xs.any p = true :=
  Array.any_eq_true'.mpr ⟨x, Array.mem_of_find?_eq_some found, Array.find?_some found⟩

/-- Each element of a list of numbers is at most their largest, folded from zero. -/
theorem le_foldr_max : ∀ {values : List Nat} {value : Nat}, value ∈ values →
    value ≤ values.foldr max 0
  | _ :: _, _, .head _ => Nat.le_max_left _ _
  | _ :: _, _, .tail _ member => Nat.le_trans (le_foldr_max member) (Nat.le_max_right _ _)

/-- A first match of a longer array that lies in a prefix is the first match there. -/
theorem _root_.Array.findIdx?_of_prefix {α : Type} {u s : Array α} {p : α → Bool} {k : Nat}
    (inside : k < s.size) (same : ∀ j < s.size, u[j]? = s[j]?) (found : u.findIdx? p = some k) :
    s.findIdx? p = some k := by
  obtain ⟨lt, hit, earlier⟩ := Array.findIdx?_eq_some_iff_getElem.mp found
  have get : ∀ j (lj : j < s.size) (lu : j < u.size), u[j] = s[j] := by
    intro j lj lu
    have := same j lj
    rw [Array.getElem?_eq_getElem lu, Array.getElem?_eq_getElem lj] at this
    exact Option.some.inj this
  refine Array.findIdx?_eq_some_iff_getElem.mpr ⟨inside, ?_, fun j lt' => ?_⟩
  · rw [← get k inside lt]; exact hit
  · rw [← get j (Nat.lt_trans lt' inside) (Nat.lt_trans lt' lt)]; exact earlier j lt'

/-- If pieces of one nonzero length determine their values, so do the joined pieces. -/
theorem flatMap_inj_of_length {α β : Type} {f : α → List β} {n : Nat} (pos : 0 < n)
    (length : ∀ x, (f x).length = n) (inj : ∀ x y, f x = f y → x = y) :
    ∀ {l l' : List α}, l.flatMap f = l'.flatMap f → l = l' := by
  intro l
  induction l with
  | nil =>
    intro l' h
    cases l' with
    | nil => rfl
    | cons y l' =>
      have := congrArg List.length h
      simp only [List.flatMap_nil, List.flatMap_cons, List.length_nil, List.length_append,
        length] at this
      omega
  | cons x l ih =>
    intro l' h
    cases l' with
    | nil =>
      have := congrArg List.length h
      simp only [List.flatMap_nil, List.flatMap_cons, List.length_nil, List.length_append,
        length] at this
      omega
    | cons y l' =>
      simp only [List.flatMap_cons] at h
      obtain ⟨hxy, hl⟩ := List.append_inj h (by rw [length, length])
      rw [inj x y hxy, ih hl]

/-- The set built by the pass that finds a repeated element holds exactly the list's elements. -/
private theorem foldr_later_contains {α : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]
    [BEq α] [LawfulBEq α] (l : List α) (y : α) :
    (l.foldr (init := ((∅ : Std.TreeSet α), (none : Option α))) fun x (later, found) =>
      (later.insert x, if later.contains x then some x else found)).1.contains y =
      decide (y ∈ l) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    -- Inserting the head adds it to the set of the tail.
    simp only [List.foldr_cons, Std.TreeSet.contains_insert, ih, List.mem_cons]
    by_cases h : x = y <;> simp [h, Ne.symm]

/-- No element of the empty list occurs again. -/
@[simp] theorem firstRepeated_nil {α : Type} [Ord α] :
    firstRepeated ([] : List α) = none :=
  rfl

/-- The first element that occurs again: the head when the tail holds it, else that of the tail. -/
theorem firstRepeated_cons {α : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]
    [BEq α] [LawfulBEq α] (x : α) (l : List α) :
    firstRepeated (x :: l) = if x ∈ l then some x else firstRepeated l := by
  -- One step of the pass looks the head up in the set of the tail, which holds the tail.
  simp only [firstRepeated, List.foldr_cons, foldr_later_contains, decide_eq_true_eq]

/-- A list has no element that occurs again exactly when no element occurs twice in it. -/
theorem firstRepeated_eq_none_iff {α : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]
    [BEq α] [LawfulBEq α] (l : List α) :
    firstRepeated l = none ↔ l.Nodup := by
  induction l with
  | nil => simp [firstRepeated]
  | cons x l ih =>
    -- The head repeats exactly when the tail holds it, and otherwise the tail decides.
    rw [firstRepeated_cons, List.nodup_cons]
    by_cases hx : x ∈ l <;> simp [hx, ih]

/-- The scan finds nothing exactly when no element occurs twice, as a test of the list. -/
@[simp] theorem isNone_firstRepeated {α : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]
    [DecidableEq α] (l : List α) : (firstRepeated l).isNone = decide l.Nodup := by
  rw [Bool.eq_iff_iff, Option.isNone_iff_eq_none, decide_eq_true_iff, firstRepeated_eq_none_iff]

/-- The scan finds an element exactly when some element occurs twice, as a test of the list. -/
@[simp] theorem isSome_firstRepeated {α : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]
    [DecidableEq α] (l : List α) : (firstRepeated l).isSome = !decide l.Nodup := by
  rw [← Option.not_isNone, isNone_firstRepeated]

/-- The element that occurs again occurs at least twice. -/
theorem two_le_count_of_firstRepeated {α : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]
    [BEq α] [LawfulBEq α] {l : List α} {x : α} (h : firstRepeated l = some x) : 2 ≤ l.count x := by
  induction l with
  | nil => simp [firstRepeated] at h
  | cons y l ih =>
    rw [firstRepeated_cons] at h
    by_cases hy : y ∈ l
    · -- The head is the repeated element, once at the front and once in the tail.
      obtain rfl : y = x := Option.some.inj (by simpa [hy] using h)
      have := List.count_pos_iff.mpr hy
      simp only [List.count_cons_self]
      omega
    · -- Otherwise the tail already holds the element twice.
      have := ih (by simpa [hy] using h)
      have : l.count x ≤ (y :: l).count x := List.count_le_count_cons
      omega

/-- The first place of an element in two joined lists, from the places in each. -/
private theorem idxOf?_append {α : Type} [BEq α] [LawfulBEq α] (a : α) (l₁ l₂ : List α) :
    (l₁ ++ l₂).idxOf? a =
      if a ∈ l₁ then l₁.idxOf? a else (l₂.idxOf? a).map (· + l₁.length) := by
  induction l₁ with
  | nil => simp
  | cons x l₁ ih =>
    by_cases hx : x = a
    · simp [List.idxOf?_cons, hx]
    · by_cases ha : a ∈ l₁ <;> simp [List.idxOf?_cons, hx, ha, ih, Ne.symm hx, Option.map_map,
        Function.comp_def, Nat.add_assoc]

/-- The scan from a place, given the set of a prefix, finds the first later repeat. -/
private theorem firstRepeatIndexFrom_eq_find? {α : Type} [Ord α] [Std.TransOrd α]
    [Std.LawfulEqOrd α] [BEq α] [LawfulBEq α] (pre l : List α) (earlier : Std.TreeSet α)
    (h : ∀ y, earlier.contains y = decide (y ∈ pre)) :
    firstRepeatIndexFrom earlier pre.length l =
      ((l.zipIdx pre.length).find? fun (c, i) => (pre ++ l).idxOf? c ≠ some i).map (·.2) := by
  induction l generalizing pre earlier with
  | nil => simp [firstRepeatIndexFrom]
  | cons x xs ih =>
    by_cases hx : x ∈ pre
    · -- The head lies in the prefix, so its first place is earlier and the scan stops here.
      obtain ⟨k, hk⟩ :=
        Option.ne_none_iff_exists'.mp (mt List.idxOf?_eq_none_iff.mp (not_not_intro hx))
      have hlt := (List.idxOf?_eq_some_iff.mp hk).1
      rw [firstRepeatIndexFrom, ite_eq_left (by simp [h, hx])]
      simp [List.zipIdx_cons, idxOf?_append, hx, hk, Nat.ne_of_lt hlt]
    · -- The head is new, so its first place is its own and the scan goes on with it in the prefix.
      rw [firstRepeatIndexFrom, ite_eq_right (by simp [h, hx])]
      have := ih (pre ++ [x]) (earlier.insert x) (fun y => by
        by_cases hy : x = y <;> simp [Std.TreeSet.contains_insert, h, hy, Ne.symm])
      simp only [List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append] at this
      rw [this]
      simp [List.zipIdx_cons, idxOf?_append, hx, List.idxOf?_cons]

/-- The scan for a repeat finds the first place whose element occurs at an earlier place. -/
theorem firstRepeatIndex_eq_find? {α : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]
    [BEq α] [LawfulBEq α] (l : List α) :
    firstRepeatIndex l = (l.zipIdx.find? fun (c, i) => l.idxOf? c ≠ some i).map (·.2) := by
  -- The scan starts with the empty prefix and the empty set.
  simpa [firstRepeatIndex] using firstRepeatIndexFrom_eq_find? [] l ∅ (by simp)

/-- The scan from a set finds nothing when no element occurs twice or lies in the set. -/
private theorem firstRepeatIndexFrom_eq_none_iff {α : Type} [Ord α] [Std.TransOrd α]
    [Std.LawfulEqOrd α] (earlier : Std.TreeSet α) (place : Nat) (l : List α) :
    firstRepeatIndexFrom earlier place l = none ↔
      l.Nodup ∧ ∀ x ∈ l, earlier.contains x = false := by
  induction l generalizing earlier place with
  | nil => simp [firstRepeatIndexFrom]
  | cons x xs ih =>
    by_cases hx : earlier.contains x = true
    · simp [firstRepeatIndexFrom, hx]
    · -- Past the head, the set holds it, so the tail must avoid it.
      rw [firstRepeatIndexFrom, ite_eq_right hx, ih]
      simp only [Std.TreeSet.contains_insert, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
        List.nodup_cons, ne_eq, Std.compare_eq_iff_eq, List.forall_mem_cons,
        Bool.not_eq_true] at hx ⊢
      constructor
      · rintro ⟨hn, ha⟩
        exact ⟨⟨fun hm => (ha x hm).1 rfl, hn⟩, hx, fun a h => (ha a h).2⟩
      · rintro ⟨⟨hm, hn⟩, -, ha⟩
        exact ⟨hn, fun a h => ⟨fun e => hm (e ▸ h), ha a h⟩⟩

/-- The scan for a repeat finds nothing exactly when no element occurs twice. -/
theorem firstRepeatIndex_eq_none_iff {α : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]
    (l : List α) : firstRepeatIndex l = none ↔ l.Nodup := by
  -- The empty set holds no element.
  simp [firstRepeatIndex, firstRepeatIndexFrom_eq_none_iff]

/-- The first place of an element in an array with one more element at the end. -/
private theorem idxOf?_push {α : Type} [BEq α] [LawfulBEq α] (d : Array α) (x y : α) :
    (d.push x).idxOf? y = if y ∈ d then d.idxOf? y else if x == y then some d.size else none := by
  rcases d with ⟨d⟩
  rw [List.push_toArray, List.idxOf?_toArray, List.idxOf?_toArray, idxOf?_append]
  by_cases hy : y ∈ d <;> by_cases hx : x = y <;> simp [hy, hx, List.idxOf?_cons]

/-- From a tree that agrees with the search, the one pass gives what the search gives. -/
private theorem distinctPlaces_foldl {α : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]
    [BEq α] [LawfulBEq α] (l : List α) (distinct : Array α) (places : Array Nat)
    (seen : Std.TreeMap α Nat) (h : ∀ y, seen.get? y = distinct.idxOf? y) :
    (fun r => (r.1, r.2.1)) (l.foldl (init := (distinct, places, seen))
      fun (distinct, places, seen) x =>
        match seen.get? x with
        | some j => (distinct, places.push j, seen)
        | none => (distinct.push x, places.push distinct.size, seen.insert x distinct.size)) =
    l.foldl (fun acc x =>
      match acc.1.idxOf? x with
      | some j => (acc.1, acc.2.push j)
      | none => (acc.1.push x, acc.2.push acc.1.size)) (distinct, places) := by
  induction l generalizing distinct places seen with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, List.foldl_cons]
    cases hc : distinct.idxOf? x with
    | some j =>
      -- A repeat leaves the distinct elements and the tree as they were.
      simp only [(h x).trans hc]
      exact ih _ _ _ h
    | none =>
      -- A new element takes the next place in both the array and the tree.
      simp only [(h x).trans hc]
      refine ih _ _ _ fun y => ?_
      have hx : x ∉ distinct := Array.idxOf?_eq_none_iff.mp hc
      rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert,
        ← Std.TreeMap.get?_eq_getElem?, h, idxOf?_push]
      by_cases hxy : x = y
      · subst hxy
        simp [hx]
      · by_cases hy : y ∈ distinct
        · simp [hxy, hy]
        · simp [hxy, hy, Array.idxOf?_eq_none_iff.mpr hy]

/-- The one-pass removal of repeats gives the removal that searches the distinct elements. -/
theorem distinctPlaces_eq_foldl {α : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]
    [BEq α] [LawfulBEq α] (l : List α) :
    distinctPlaces l = l.foldl (fun acc x =>
      match acc.1.idxOf? x with
      | some j => (acc.1, acc.2.push j)
      | none => (acc.1.push x, acc.2.push acc.1.size)) (#[], #[]) := by
  -- The empty tree maps nothing, as the empty array has no place to give.
  exact distinctPlaces_foldl l #[] #[] ∅ fun y => by simp [Std.TreeMap.get?_eq_getElem?]

/-! ## Folds, orderings and duplicates -/

/-- `n` is below a fold of minimums exactly when it is below the start and below every term. -/
theorem le_foldl_min_iff {α : Type} (f : α → Nat) (n : Nat) :
    (l : List α) → (start : Nat) →
      (n ≤ l.foldl (fun length entry => min length (f entry)) start ↔
        n ≤ start ∧ ∀ entry ∈ l, n ≤ f entry)
  | [], start => by simp
  | entry :: rest, start => by
    simp only [List.foldl_cons, le_foldl_min_iff f n rest, List.forall_mem_cons, Nat.le_min]
    exact and_assoc

/-- A fold of minimums does not depend on the order of its terms. -/
theorem foldl_min_perm {α : Type} (f : α → Nat) {l l' : List α} (hperm : l.Perm l')
    (start : Nat) :
    l.foldl (fun length entry => min length (f entry)) start =
      l'.foldl (fun length entry => min length (f entry)) start := by
  apply Nat.le_antisymm
  · have h := (le_foldl_min_iff f _ l start).mp (Nat.le_refl _)
    exact (le_foldl_min_iff f _ l' start).mpr
      ⟨h.1, fun entry hmem => h.2 entry (hperm.mem_iff.mpr hmem)⟩
  · have h := (le_foldl_min_iff f _ l' start).mp (Nat.le_refl _)
    exact (le_foldl_min_iff f _ l start).mpr
      ⟨h.1, fun entry hmem => h.2 entry (hperm.mem_iff.mp hmem)⟩

/-- A fold that keeps the value of the last entry that satisfies `p` gives it, or its start. -/
theorem foldl_last {α β : Type} (p : α → Bool) (value : α → β) :
    (l : List α) → (start : β) →
      l.foldl (fun acc entry => if p entry then value entry else acc) start
        = (((l.filter p).getLast?).map value).getD start
  | [], _ => rfl
  | entry :: rest, start => by
    rw [List.foldl_cons, foldl_last p value rest]
    by_cases h : p entry
    · simp only [h, ↓reduceIte, List.filter_cons_of_pos h, List.getLast?_cons]
      cases (rest.filter p).getLast? <;> rfl
    · simp [h, List.filter_cons_of_neg h]

/-- Two orderings of a list with at most one entry are the same list. -/
theorem eq_of_perm_of_length_le_one {α : Type} {l l' : List α} (hperm : l.Perm l')
    (hlength : l.length ≤ 1) : l = l' := by
  match l, hlength with
  | [], _ => exact List.Perm.nil_eq hperm
  | [x], _ => exact (List.perm_singleton.mp hperm.symm).symm

/-- A list without duplicates whose entries are all `c` has at most one entry. -/
theorem length_le_one_of_nodup {α : Type} {c : α} :
    (l : List α) → l.Nodup → (∀ x ∈ l, x = c) → l.length ≤ 1
  | [], _, _ => Nat.zero_le _
  | [_], _, _ => Nat.le_refl _
  | x :: y :: _, hnodup, hall => by
    have hx := hall x List.mem_cons_self
    have hy := hall y (List.mem_cons_of_mem _ List.mem_cons_self)
    exact ((List.nodup_cons.mp hnodup).1 ((hx.trans hy.symm) ▸ List.mem_cons_self)).elim

/-- A list whose image has no duplicates has none itself. -/
theorem nodup_of_map {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup) : l.Nodup :=
  List.Pairwise.of_map f (fun _ _ hne heq => hne (congrArg f heq)) h

/-- An injective function keeps a list free of duplicates. -/
theorem nodup_map_of_injective {α β : Type} {f : α → β} (hinjective : Function.Injective f)
    {l : List α} (h : l.Nodup) : (l.map f).Nodup :=
  List.Pairwise.map f (fun _ _ hne heq => hne (hinjective heq)) h

end EthLib.Base
