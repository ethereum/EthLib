module

public import EthLib.Base.List

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

end EthLib.Base
