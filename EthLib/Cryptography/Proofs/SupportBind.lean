module

public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import ToMathlib.Control.WriterT

/-!
# Proofs: an output of a bind or a map, for the kernel

An output of a bind is an output of its continuation on an output of its first step.

The image of an output under a map is an output of the mapped computation.

The library lemma states the bind through the generic monad instances.

A do block builds it through the free monad's own instances.

The two forms agree by unfolding, but the kernel compares them inside a support.

It then unfolds the support, which recurses over the computation, and so runs it.

The library has a form at the free monad's instances, for an oracle computation.

The lemmas here state the bind at a uniform computation, as a do block does, for any computation.

They apply the continuation to a value only inside an equation.

A lemma instantiated with a continuation applies it, and the kernel does not reduce that.

So the kernel compares the continuation applied, and the form a proof gives, as two computations.

The same holds for a map, for two names of one output, and for a simulated bind.

Each lemma here holds for any computation, so the kernel checks it without running one.
-/

@[expose] public section

namespace OracleComp

variable {α β : Type}

/-- A value of the first step and an output of the continuation on it give an output of a bind.

The output is stated for any computation that the continuation applied equals. -/
theorem mem_support_bind_of_eq (x : ProbComp α) (k : α → ProbComp β) {a : α} {y : β}
    (first : a ∈ support x) (next : ∀ c, k a = c → y ∈ support c) : y ∈ support (x >>= k) :=
  (mem_support_bind_iff x k y).2 ⟨a, first, next _ rfl⟩

/-- An output of a bind is an output of the continuation on some value of the first step.

The output is stated for any computation that the continuation applied equals. -/
theorem exists_eq_of_mem_support_bind (x : ProbComp α) (k : α → ProbComp β) {y : β}
    (h : y ∈ support (x >>= k)) : ∃ a ∈ support x, ∀ c, k a = c → y ∈ support c := by
  obtain ⟨a, first, next⟩ := (mem_support_bind_iff x k y).1 h
  exact ⟨a, first, fun _ same => same ▸ next⟩

/-- The image of an output of a computation is an output of the mapped computation.

The image is stated for any value it equals.

It holds for any computation, so the kernel checks it without running one. -/
theorem mem_support_map_of_eq (f : α → β) (c : ProbComp α) {a : α} {b : β}
    (h : a ∈ support c) (hb : f a = b) : b ∈ support (f <$> c) := by
  rw [support_map]
  exact ⟨a, h, hb⟩

/-- An output of a computation is one of any equal computation, under any equal name. -/
theorem mem_support_congr {c c' : ProbComp α} {x y : α}
    (h : x ∈ support c) (sameComputation : c = c') (same : x = y) : y ∈ support c' :=
  sameComputation ▸ same ▸ h

/-- An output of a map is the function applied to an output of the computation. -/
theorem exists_eq_of_mem_support_map (x : ProbComp α) (f : α → β) {y : β}
    (h : y ∈ support (f <$> x)) : ∃ a ∈ support x, f a = y := by
  rw [support_map] at h
  exact h

/-- The image of an output of a computation is an output of any computation equal to its map.

The image is stated for any value it equals. -/
theorem mem_support_of_map_eq {x : ProbComp α} {y : ProbComp β} (f : α → β)
    (hxy : f <$> x = y) {a : α} (ha : a ∈ support x) {b : β} (hb : f a = b) :
    b ∈ support y := by
  subst hxy
  exact mem_support_map_of_eq f x ha hb

/-- An output of two binds that return a combination of both values combines outputs of both.

The second output is stated for any computation that the continuation applied equals. -/
theorem exists_eq_of_mem_support_bind_bind_pure {γ : Type} (x : ProbComp α)
    (k : α → ProbComp β) (mk : α → β → γ) {r : γ}
    (h : r ∈ support (x >>= fun a => k a >>= fun b => pure (mk a b))) :
    ∃ a b, a ∈ support x ∧ (∀ c, k a = c → b ∈ support c) ∧ mk a b = r := by
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  exact ⟨a, b, ha, fun _ same => same ▸ hb, rfl⟩

/-- An output of a bind simulated with a state comes from an output of its first step.

The rest is an output of the continuation simulated from the first step's state.

It is stated for any computation that the continuation simulated equals. -/
theorem exists_eq_of_mem_support_simulateQ_bind {ι σ : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) (mx : OracleComp spec α)
    (my : α → OracleComp spec β) (s : σ) {y : β × σ}
    (h : y ∈ support ((simulateQ impl (mx >>= my)).run s)) :
    ∃ a s', (a, s') ∈ support ((simulateQ impl mx).run s) ∧
      ∀ c, (simulateQ impl (my a)).run s' = c → y ∈ support c := by
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at h
  obtain ⟨⟨a, s'⟩, ha, h⟩ := h
  exact ⟨a, s', ha, fun _ same => same ▸ h⟩

/-- An output of a bind simulated with a trace comes from outputs of its two steps.

The trace is the first step's trace followed by the continuation's.

The continuation's output is stated for any computation that the continuation simulated equals. -/
theorem exists_eq_of_mem_support_simulateQ_writerT_bind {ι ω : Type} {spec : OracleSpec ι}
    [EmptyCollection ω] [Append ω] [LawfulAppend ω] (impl : QueryImpl spec (WriterT ω ProbComp))
    (mx : OracleComp spec α) (my : α → OracleComp spec β) {y : β × ω}
    (h : y ∈ support (simulateQ impl (mx >>= my)).run) :
    ∃ a w, (a, w) ∈ support (simulateQ impl mx).run ∧
      ∀ c, (simulateQ impl (my a)).run = c →
        ∃ b w', (b, w') ∈ support c ∧ y = (b, w ++ w') := by
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at h
  obtain ⟨⟨a, w⟩, ha, h⟩ := h
  rw [support_map] at h
  obtain ⟨⟨b, w'⟩, hb, rfl⟩ := h
  exact ⟨a, w, ha, fun _ same => ⟨b, w', same ▸ hb, rfl⟩⟩

end OracleComp
