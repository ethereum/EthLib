module

public import VCVio.OracleComp.ProbComp.Basic

/-!
# Proofs: an output of a bind, for the kernel

An output of a bind is an output of its continuation on an output of its first step.

The library lemma states the bind through the generic monad instances.

A do block builds it through the free monad's own instances.

The two forms agree by unfolding, but the kernel compares them inside a support.

It then unfolds the support, which recurses over the computation, and so runs it.

The library has a form at the free monad's instances, for an oracle computation.

The lemmas here state the bind at a uniform computation, as a do block does, for any computation.

They apply the continuation to a value only inside an equation.

A lemma instantiated with a continuation applies it, and the kernel does not reduce that.

So the kernel compares the continuation applied, and the form a proof gives, as two computations.
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

end OracleComp
