module

/-!
# `Base.Proofs.MapM`

What a successful map over a list in `Except` returns.

Lean core proves no such facts for `Except`, and every layer needs them.

- The map has one output for each input.
- The function succeeds on every input.
- Each output is the image of an input.
- The map succeeds when the function succeeds on every input.
- A function that returns a known value on every input maps to the list of those values.
- A part of each output that its input fixes comes out in the order of the inputs.
- Output `i` is the image of input `i`.
- A failed map fails on some input, and succeeds on every input before it.

A mapped error leaves a success unchanged.

A sequence of two computations succeeds when both steps succeed.
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

/-- A successful map succeeds on every input. -/
theorem mapM_ok_of_mem {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys) :
    ∀ x ∈ xs, ∃ y, f x = .ok y := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨y, rest, head, tail, rfl⟩ := mapM_cons_ok.mp h
    intro x' member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨y, head⟩
    · exact ih tail x' member

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

/-- Two steps in sequence succeed exactly when the first succeeds with some value.

The second step must then succeed on that value. -/
theorem bind_ok_iff {x : Except ε α} {g : α → Except ε β} {y : β} :
    x >>= g = .ok y ↔ ∃ a, x = .ok a ∧ g a = .ok y := by
  cases x <;> simp [bind, Except.bind]

end EthLib.Base
