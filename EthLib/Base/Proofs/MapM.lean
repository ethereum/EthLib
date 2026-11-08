module

public import EthLib.Base.Except

/-!
# `Base.Proofs.MapM`

What a successful map over a list in `Except` returns.

Lean core proves no such facts for `Except`, and every layer needs them.

- The map has one output for each input.
- Two lists that map to one list are equal, when the function is injective on their items.
- A run of checks passes exactly when each check passes.
- A loop that never stops early passes exactly when each step passes.
- The function succeeds on every input.
- Each output is the image of an input.
- The map succeeds, and returns no error, when the function succeeds on every input.
- A function that returns a known value on every input maps to the list of those values.
- A part of each output that its input fixes comes out in the order of the inputs.
- Output `i` is the image of input `i`, for a list, an array or a vector.
- A map returns a list exactly when it has one output per input, each the image of its input.
- Two functions that agree on every entry of a vector map it to one result.
- A failed map fails on some input, and succeeds on every input before it.
- A property that each step keeps holds after a successful fold.
- A successful fold reads only inputs that its steps accept.
- A fold of steps that each succeed with a pure step is the pure fold.

A mapped error leaves a success unchanged.
-/

@[expose] public section

namespace EthLib.Base

variable {ε α β : Type} {f : α → Except ε β}

/-- A map over a nonempty list succeeds exactly when it succeeds on the head and on the tail. -/
theorem mapM_cons_ok {x : α} {xs : List α} {ys : List β} :
    (x :: xs).mapM f = .ok ys ↔
      ∃ y rest, f x = .ok y ∧ xs.mapM f = .ok rest ∧ ys = y :: rest := by
  rw [List.mapM_cons]
  cases hx : f x <;> cases hxs : xs.mapM f <;>
    simp [bind, Except.bind, pure, Except.pure, eq_comm]

/-- A successful map has one output for each input. -/
theorem mapM_ok_length {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys) :
    ys.length = xs.length := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    simp [← h]
  | cons x xs ih =>
    obtain ⟨_, rest, _, tail, rfl⟩ := mapM_cons_ok.mp h
    simp [ih tail]

/-- Two lists that a function maps to one list are equal, when it is injective on their items. -/
theorem mapM_ok_injective {xs ys : List α} {zs : List β}
    (hinjective : ∀ x ∈ xs, ∀ y ∈ ys, ∀ z, f x = .ok z → f y = .ok z → x = y)
    (hx : xs.mapM f = .ok zs) (hy : ys.mapM f = .ok zs) : xs = ys := by
  induction xs generalizing ys zs with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hx
    subst hx
    cases ys with
    | nil => rfl
    | cons y ys =>
      obtain ⟨_, _, _, _, h⟩ := mapM_cons_ok.mp hy
      cases h
  | cons x xs ih =>
    obtain ⟨z, rest, hz, hrest, rfl⟩ := mapM_cons_ok.mp hx
    cases ys with
    | nil => cases hy
    | cons y ys =>
      obtain ⟨z', rest', hz', hrest', h⟩ := mapM_cons_ok.mp hy
      obtain ⟨rfl, rfl⟩ := List.cons.inj h
      -- The heads have one output, and the tails map to one list.
      rw [hinjective x (by simp) y (by simp) z hz hz',
        ih (fun x hx y hy => hinjective x (by simp [hx]) y (by simp [hy])) hrest hrest']

/-- A run of checks over a list passes exactly when each check passes. -/
theorem forM_ok_iff {xs : List α} {check : α → Except ε Unit} :
    xs.forM check = .ok () ↔ ∀ x ∈ xs, check x = .ok () := by
  induction xs with
  | nil => simp [List.forM, pure, Except.pure]
  | cons x xs ih =>
    simp only [List.forM, bind_unit_ok_iff, List.forall_mem_cons]
    exact and_congr_right fun _ => ih

/-- A loop with no state passes exactly when each step passes.

No step may stop the loop early. -/
theorem forIn_unit_ok_iff {xs : List α} {body : α → PUnit → Except ε (ForInStep PUnit)}
    (hnd : ∀ x, body x PUnit.unit ≠ .ok (.done PUnit.unit)) :
    forIn xs PUnit.unit body = .ok PUnit.unit ↔
      ∀ x ∈ xs, body x PUnit.unit = .ok (.yield PUnit.unit) := by
  induction xs with
  | nil => simp [pure, Except.pure]
  | cons x xs ih =>
    rw [List.forIn_cons, List.forall_mem_cons]
    cases h : body x PUnit.unit with
    | error e => simp [bind, Except.bind]
    | ok s =>
      cases s with
      | done u => exact absurd h (hnd x)
      | yield u => simpa [bind, Except.bind] using ih

/-- Each input of a successful map has its output among the outputs. -/
theorem exists_mem_of_mapM_ok {xs : List α} {ys : List β}
    (made : xs.mapM f = .ok ys) {x : α} (member : x ∈ xs) : ∃ y ∈ ys, f x = .ok y := by
  induction xs generalizing ys with
  | nil => simp at member
  | cons head tail ih =>
    obtain ⟨y, rest, first, others, rfl⟩ := mapM_cons_ok.mp made
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨y, List.mem_cons_self, first⟩
    · obtain ⟨y', member', step⟩ := ih others member
      exact ⟨y', List.mem_cons_of_mem _ member', step⟩

/-- A successful map succeeds on every input. -/
theorem mapM_ok_of_mem {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys) :
    ∀ x ∈ xs, ∃ y, f x = .ok y := fun _ member =>
  let ⟨y, _, step⟩ := exists_mem_of_mapM_ok h member
  ⟨y, step⟩

/-- Each output of a successful map is the image of an input. -/
theorem mapM_ok_mem {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys) :
    ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    simp [← h]
  | cons x xs ih =>
    obtain ⟨y, rest, head, tail, rfl⟩ := mapM_cons_ok.mp h
    intro y' member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨x, List.mem_cons_self, head⟩
    · obtain ⟨x', member', image⟩ := ih tail y' member
      exact ⟨x', List.mem_cons_of_mem x member', image⟩

/-- A map succeeds when the function succeeds on every input. -/
theorem mapM_exists_ok {xs : List α} (h : ∀ x ∈ xs, ∃ y, f x = .ok y) :
    ∃ ys, xs.mapM f = .ok ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨y, head⟩ := h x List.mem_cons_self
    obtain ⟨rest, tail⟩ := ih fun x' member => h x' (List.mem_cons_of_mem x member)
    exact ⟨y :: rest, mapM_cons_ok.mpr ⟨y, rest, head, tail, rfl⟩⟩

/-- A function that returns `g x` on every input `x` maps the list to its image under `g`. -/
theorem mapM_eq_ok_map {g : α → β} {xs : List α} (h : ∀ x ∈ xs, f x = .ok (g x)) :
    xs.mapM f = .ok (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    exact mapM_cons_ok.mpr ⟨g x, xs.map g, h x List.mem_cons_self,
      ih fun x' member => h x' (List.mem_cons_of_mem x member), rfl⟩

/-- A successful map keeps, in order, each part of an output that its input fixes. -/
theorem map_of_mapM_ok {γ : Type} {p : β → γ} {q : α → γ} (hpart : ∀ x y, f x = .ok y → p y = q x)
    {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys) : ys.map p = xs.map q := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    simp [← h]
  | cons x xs ih =>
    obtain ⟨y, rest, head, tail, rfl⟩ := mapM_cons_ok.mp h
    simp [hpart x y head, ih tail]

/-- Output `i` of a successful map is the image of input `i`. -/
theorem mapM_ok_getElem {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys)
    (i : Nat) (hi : i < xs.length) :
    f xs[i] = .ok (ys[i]'(by rw [mapM_ok_length h]; exact hi)) := by
  induction xs generalizing ys i with
  | nil => exact absurd hi (Nat.not_lt_zero i)
  | cons x xs ih =>
    obtain ⟨y, rest, head, tail, rfl⟩ := mapM_cons_ok.mp h
    cases i with
    | zero => exact head
    | succ i => exact ih tail i (Nat.lt_of_succ_lt_succ hi)

/-- A map returns a list exactly when it has one output per input, each the image of its input. -/
theorem mapM_eq_ok_iff {xs : List α} {ys : List β} :
    xs.mapM f = .ok ys ↔
      ∃ h : ys.length = xs.length, ∀ (i : Nat) (hi : i < xs.length), f xs[i] = .ok ys[i] := by
  constructor
  · intro h
    exact ⟨mapM_ok_length h, fun i hi => mapM_ok_getElem h i hi⟩
  · rintro ⟨hlen, hget⟩
    induction xs generalizing ys with
    | nil =>
      cases ys with
      | nil => rfl
      | cons => simp at hlen
    | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
        -- The head maps to the head, and the tail to the tail, by the same index shifted by one.
        refine mapM_cons_ok.mpr ⟨y, ys, hget 0 (by simp), ih (by simpa using hlen) ?_, rfl⟩
        intro i hi
        exact hget (i + 1) (by simpa using hi)

/-- Output `i` of a successful map over a vector is the image of input `i`. -/
theorem vector_mapM_ok_getElem {n : Nat} {xs : Vector α n} {ys : Vector β n}
    (h : xs.mapM f = .ok ys) (i : Nat) (hi : i < n) : f xs[i] = .ok ys[i] := by
  have onArray : xs.toArray.mapM f = .ok ys.toArray := by
    rw [← Vector.toArray_mapM, h]
    rfl
  have onList : xs.toArray.toList.mapM f = .ok ys.toArray.toList := by
    rw [← Array.toList_mapM, onArray]
    rfl
  have := mapM_ok_getElem onList i (by simpa using hi)
  simpa using this

/-- A map over a vector returns a vector exactly when each output is the image of its input. -/
theorem vector_mapM_eq_ok_iff {n : Nat} {xs : Vector α n} {ys : Vector β n} :
    xs.mapM f = .ok ys ↔ ∀ (i : Nat) (hi : i < n), f xs[i] = .ok ys[i] := by
  refine ⟨fun h i hi => vector_mapM_ok_getElem h i hi, fun each => ?_⟩
  -- The map over the entries as a list returns the entries of the outputs.
  have onList : xs.toArray.toList.mapM f = .ok ys.toArray.toList :=
    mapM_eq_ok_iff.mpr ⟨by simp, fun i hi => by simpa using each i (by simpa using hi)⟩
  have onArray : Vector.toArray <$> xs.mapM f = .ok ys.toArray := by
    rw [Vector.toArray_mapM, Array.mapM_eq_mapM_toList, onList]
    rfl
  cases mapped : xs.mapM f with
  | error e => rw [mapped] at onArray; cases onArray
  | ok zs =>
    rw [mapped] at onArray
    exact congrArg Except.ok (Vector.toArray_inj.mp (Except.ok.inj onArray))

/-- Two functions that agree on every entry of a vector map it to one result. -/
theorem vector_mapM_congr {n : Nat} {xs : Vector α n} {g : α → Except ε β}
    (agree : ∀ (i : Nat) (hi : i < n), f xs[i] = g xs[i]) : xs.mapM f = xs.mapM g := by
  have onList : ∀ ys : List α, (∀ x ∈ ys, f x = g x) → ys.mapM f = ys.mapM g := by
    intro ys
    induction ys with
    | nil => intro _; rfl
    | cons y ys ih =>
      intro same
      simp only [List.mapM_cons, same y (by simp), ih fun x member => same x (by simp [member])]
  have onArray : Vector.toArray <$> xs.mapM f = Vector.toArray <$> xs.mapM g := by
    rw [Vector.toArray_mapM, Vector.toArray_mapM, Array.mapM_eq_mapM_toList,
      Array.mapM_eq_mapM_toList, onList]
    intro x member
    rw [Array.mem_toList_iff, Vector.mem_toArray_iff, Vector.mem_iff_getElem] at member
    obtain ⟨i, hi, rfl⟩ := member
    exact agree i hi
  cases first : xs.mapM f <;> cases second : xs.mapM g <;>
    simp_all [Functor.map, Except.map, Vector.toArray_inj]

/-- A successful map over an array keeps its size, and output `i` is the image of input `i`. -/
theorem array_mapM_ok {xs : Array α} {ys : Array β} (h : xs.mapM f = .ok ys) :
    ys.size = xs.size ∧
      ∀ (i : Nat) (hi : i < xs.size) (hj : i < ys.size), f xs[i] = .ok ys[i] := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : xs.toList.mapM f with
  | error e => rw [hl] at h; cases h
  | ok zs =>
    rw [hl] at h
    have hys : zs.toArray = ys := Except.ok.inj h
    subst hys
    have hlen := mapM_ok_length hl
    refine ⟨by simpa using hlen, fun i hi hj => ?_⟩
    have hi' : i < xs.toList.length := by simpa using hi
    simpa using mapM_ok_getElem hl i hi'

/-- A map over an array succeeds when the function succeeds on every entry. -/
theorem array_mapM_exists_ok {xs : Array α} (h : ∀ x ∈ xs, ∃ y, f x = .ok y) :
    ∃ ys, xs.mapM f = .ok ys := by
  obtain ⟨ys, hys⟩ := mapM_exists_ok (f := f) (xs := xs.toList)
    fun x hx => h x (Array.mem_toList_iff.mp hx)
  refine ⟨ys.toArray, ?_⟩
  rw [Array.mapM_eq_mapM_toList, hys]
  rfl

/-- A map over an array that succeeds on every entry returns no error. -/
theorem array_mapM_ne_error {xs : Array α} {e : ε} (h : ∀ x ∈ xs, ∃ y, f x = .ok y) :
    xs.mapM f ≠ .error e := by
  obtain ⟨ys, hys⟩ := array_mapM_exists_ok h
  rw [hys]
  exact fun h => nomatch h

/-- Every output of a successful map over an array is the image of some input. -/
theorem array_mapM_ok_mem {xs : Array α} {ys : Array β} (h : xs.mapM f = .ok ys) :
    ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : xs.toList.mapM f with
  | error e => rw [hl] at h; cases h
  | ok zs =>
    rw [hl] at h
    have hys : zs.toArray = ys := Except.ok.inj h
    subst hys
    intro y hy
    obtain ⟨x, hmem, hx⟩ := mapM_ok_mem hl y (List.mem_toArray.mp hy)
    exact ⟨x, Array.mem_toList_iff.mp hmem, hx⟩

/-- A failed map fails with its error on some input, and succeeds on every input before it. -/
theorem mapM_error {xs : List α} {e : ε} (h : xs.mapM f = .error e) :
    ∃ i, ∃ hi : i < xs.length, f xs[i] = .error e ∧
      ∀ k (hk : k < i), ∃ y, f (xs[k]'(Nat.lt_trans hk hi)) = .ok y := by
  induction xs with
  | nil => simp [List.mapM_nil, pure, Except.pure] at h
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e' =>
      rw [hx] at h
      cases h
      exact ⟨0, by simp, hx, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    | ok y =>
      cases hxs : xs.mapM f with
      | ok rest =>
        rw [hx, hxs] at h
        cases h
      | error e' =>
        rw [hx, hxs] at h
        cases h
        obtain ⟨i, hi, hfail, hbefore⟩ := ih hxs
        refine ⟨i + 1, by simpa using hi, hfail, fun k hk => ?_⟩
        cases k with
        | zero => exact ⟨y, hx⟩
        | succ k => exact hbefore k (Nat.lt_of_succ_lt_succ hk)

/-- A computation with its error mapped succeeds with a value exactly when the computation does. -/
theorem mapError_ok_iff {ε' : Type} {g : ε → ε'} {result : Except ε α} {value : α} :
    result.mapError g = .ok value ↔ result = .ok value := by
  cases result <;> simp [Except.mapError]

/-- A property that each successful step keeps holds after a successful fold. -/
theorem foldlM_ok_invariant {g : β → α → Except ε β} (P : β → Prop)
    (step : ∀ b x b', P b → g b x = .ok b' → P b') :
    ∀ {xs : List α} {b b' : β}, P b → xs.foldlM g b = .ok b' → P b'
  | [], _, _, holds, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ holds
  | x :: _, b, _, holds, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, rest⟩ := computed
    exact foldlM_ok_invariant P step (step b x middle holds first) rest

/-- Every input of a successful fold meets a condition that each successful step checks. -/
theorem foldlM_forall_of_ok {σ : Type} {g : σ → α → Except ε σ} {P : α → Prop}
    (step : ∀ acc x r, g acc x = .ok r → P x) :
    ∀ (xs : List α) init out, xs.foldlM g init = .ok out → ∀ x ∈ xs, P x
  | [], _, _, _, _, member => absurd member List.not_mem_nil
  | x :: xs, init, out, computed, y, member => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, rest⟩ := computed
    rcases List.mem_cons.mp member with rfl | member
    · exact step init y middle first
    · exact foldlM_forall_of_ok step xs middle out rest y member

/-- A fold whose every step succeeds with a pure step returns the pure fold. -/
theorem foldlM_eq_ok_foldl {σ : Type} {g : σ → α → Except ε σ} {step : σ → α → σ}
    {L : List α} (pureStep : ∀ acc x, x ∈ L → g acc x = .ok (step acc x)) :
    ∀ init, L.foldlM g init = .ok (L.foldl step init) := by
  induction L with
  | nil => intro init; rfl
  | cons x xs ih =>
    intro init
    rw [List.foldlM_cons, pureStep init x List.mem_cons_self, List.foldl_cons]
    simp only [bind, Except.bind]
    exact ih (fun acc y member => pureStep acc y (List.mem_cons_of_mem x member)) _

/-- Each element of a list gives a result when the monadic flat map over the list succeeds. -/
theorem flatMapM_ok_of_mem {α β ε : Type} {f : α → Except ε (List β)} :
    ∀ {xs : List α} {ys : List β}, xs.flatMapM f = .ok ys → ∀ x ∈ xs, ∃ zs, f x = .ok zs
  | [], _, _, _, mem => by cases mem
  | x :: xs, ys, h, y, mem => by
    rw [List.flatMapM_cons, bind_ok_iff] at h
    obtain ⟨zs, first, h⟩ := h
    rw [bind_ok_iff] at h
    obtain ⟨rest, restOk, -⟩ := h
    rcases List.mem_cons.mp mem with rfl | mem
    · exact ⟨zs, first⟩
    · exact flatMapM_ok_of_mem restOk y mem

/-- An element of a monadic flat map comes from the list of one element, and each such counts. -/
theorem mem_of_flatMapM_ok {α β ε : Type} {f : α → Except ε (List β)} :
    ∀ {xs : List α} {ys : List β}, xs.flatMapM f = .ok ys →
      ∀ y, y ∈ ys ↔ ∃ x ∈ xs, ∃ zs, f x = .ok zs ∧ y ∈ zs
  | [], ys, h, y => by
    simp only [List.flatMapM_nil, pure, Except.pure, Except.ok.injEq] at h
    simp [← h]
  | x :: xs, ys, h, y => by
    rw [List.flatMapM_cons, bind_ok_iff] at h
    obtain ⟨zs, first, h⟩ := h
    rw [bind_ok_iff] at h
    obtain ⟨rest, restOk, h⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [List.mem_append, mem_of_flatMapM_ok restOk]
    constructor
    · rintro (mem | ⟨x', mem', zs', ok', mem''⟩)
      · exact ⟨x, List.mem_cons_self, zs, first, mem⟩
      · exact ⟨x', List.mem_cons_of_mem _ mem', zs', ok', mem''⟩
    · rintro ⟨x', mem', zs', ok', mem''⟩
      rcases List.mem_cons.mp mem' with rfl | mem'
      · rw [first, Except.ok.injEq] at ok'
        exact .inl (ok' ▸ mem'')
      · exact .inr ⟨x', mem', zs', ok', mem''⟩

/-- A monadic filter map in `Except` succeeds when each call succeeds. -/
theorem filterMapM_ok_of_forall {α β ε : Type} {f : α → Except ε (Option β)} :
    ∀ {l : List α}, (∀ x ∈ l, ∃ y, f x = .ok y) → ∃ out, l.filterMapM f = .ok out
  | [], _ => ⟨[], rfl⟩
  | x :: l, each => by
    obtain ⟨y, first⟩ := each x List.mem_cons_self
    obtain ⟨rest, restOk⟩ :=
      filterMapM_ok_of_forall fun x' mem => each x' (List.mem_cons_of_mem _ mem)
    cases y with
    | none => exact ⟨rest, by simp [List.filterMapM_cons, first, restOk, bind, Except.bind]⟩
    | some z =>
      exact ⟨z :: rest, by simp [List.filterMapM_cons, first, restOk, bind, Except.bind, pure,
        Except.pure]⟩

end EthLib.Base
