module

public import EthLib.Execution.Proofs.Evm.Logic.Loop

/-!
# Proofs: upper bounds on the gas that a run spends

A triple with a cost reaches its postcondition with at most that cost less gas than at its start.

The bounds compose along straight-line code, branches and loops.

They are stated for the meter of one counter of gas.

Before Glamsterdam, that is the meter of the fork.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork)

variable {fork : Fork}

/-- From every frame that `P` holds of, the steps of `S` reach a frame that `Q` holds of.

The run spends at most `cost` gas, net of the gas that comes back during the run. -/
def Costs (S : Evm fork Nat → Evm fork Nat → Prop) (P Q : Evm fork Nat → Prop)
    (cost : Nat) : Prop :=
  -- The bound is a sum, with no truncated subtraction.
  ∀ evm, P evm → ∃ after, Reaches S evm after ∧ Q after ∧ evm.gas ≤ after.gas + cost

namespace Costs

variable {S : Evm fork Nat → Evm fork Nat → Prop} {P P' Q Q' R : Evm fork Nat → Prop}
  {cost cost₁ cost₂ : Nat}

/-- A triple with a cost is a triple. -/
theorem toTriple (h : Costs S P Q cost) : Triple S P Q := fun evm hp =>
  let ⟨after, hr, hq, _⟩ := h evm hp
  ⟨after, hr, hq⟩

/-- A triple whose two ends hold gas that differ by at most `cost` is a triple with that cost.

It serves when the precondition and the postcondition name the gas of the frame. -/
theorem of_triple (h : Triple S P Q) (gas : ∀ a b, P a → Q b → a.gas ≤ b.gas + cost) :
    Costs S P Q cost := fun evm hp =>
  let ⟨after, hr, hq⟩ := h evm hp
  ⟨after, hr, hq, gas evm after hp hq⟩

/-- A bound on the cost over some steps holds over the steps of a larger relation. -/
theorem mono_steps {S' : Evm fork Nat → Evm fork Nat → Prop} (larger : ∀ {a b}, S a b → S' a b)
    (h : Costs S P Q cost) : Costs S' P Q cost := fun evm hp =>
  let ⟨after, hr, hq, hg⟩ := h evm hp
  ⟨after, hr.mono larger, hq, hg⟩

/-- A precondition that implies the postcondition needs no step and spends nothing. -/
theorem of_imp (h : ∀ evm, P evm → Q evm) : Costs S P Q 0 := fun evm hp =>
  ⟨evm, .refl evm, h evm hp, Nat.le_refl _⟩

/-- A bound on the cost holds of every larger bound. -/
theorem mono (h : Costs S P Q cost₁) (le : cost₁ ≤ cost₂) : Costs S P Q cost₂ := fun evm hp =>
  let ⟨after, hr, hq, hg⟩ := h evm hp
  ⟨after, hr, hq, by omega⟩

/-- Consequence: a stronger precondition and a weaker postcondition keep the cost. -/
theorem consequence (h : Costs S P Q cost) (pre : ∀ evm, P' evm → P evm)
    (post : ∀ evm, Q evm → Q' evm) : Costs S P' Q' cost := fun evm hp =>
  let ⟨after, hr, hq, hg⟩ := h evm (pre evm hp)
  ⟨after, hr, post after hq, hg⟩

/-- Straight-line code: the cost of two runs in sequence is the sum of their costs. -/
theorem seq (first : Costs S P Q cost₁) (second : Costs S Q R cost₂) :
    Costs S P R (cost₁ + cost₂) := fun evm hp =>
  let ⟨mid, h₁, hq, g₁⟩ := first evm hp
  let ⟨after, h₂, hr, g₂⟩ := second mid hq
  ⟨after, h₁.trans h₂, hr, by omega⟩

/-- Straight-line code whose second run needs `need₂` gas at its start.

The first run needs `need₁`, and from `cost₁ + need₂` gas it leaves at least `need₂`. -/
theorem seq_need {need₁ need₂ : Nat}
    (first : Costs S (fun evm => P evm ∧ need₁ ≤ evm.gas) Q cost₁)
    (second : Costs S (fun evm => Q evm ∧ need₂ ≤ evm.gas) R cost₂) :
    Costs S (fun evm => P evm ∧ max need₁ (cost₁ + need₂) ≤ evm.gas) R (cost₁ + cost₂) :=
  fun evm ⟨hp, hn⟩ => by
    have l₁ := Nat.le_max_left need₁ (cost₁ + need₂)
    have l₂ := Nat.le_max_right need₁ (cost₁ + need₂)
    obtain ⟨mid, h₁, hq, g₁⟩ := first evm ⟨hp, by omega⟩
    obtain ⟨after, h₂, hr, g₂⟩ := second mid ⟨hq, by omega⟩
    exact ⟨after, h₁.trans h₂, hr, by omega⟩

/-- Two cases of the precondition: the cost is the larger of the two. -/
theorem cases {P₁ P₂ : Evm fork Nat → Prop} (h₁ : Costs S P₁ Q cost₁)
    (h₂ : Costs S P₂ Q cost₂) :
    Costs S (fun evm => P₁ evm ∨ P₂ evm) Q (max cost₁ cost₂) := fun evm hp =>
  hp.elim (fun h => (h₁.mono (Nat.le_max_left _ _)) evm h)
    (fun h => (h₂.mono (Nat.le_max_right _ _)) evm h)

/-- A branch on a condition: the cost is the larger of the costs of the two sides. -/
theorem byCases (c : Prop) (pos : Costs S (fun evm => P evm ∧ c) Q cost₁)
    (neg : Costs S (fun evm => P evm ∧ ¬c) Q cost₂) : Costs S P Q (max cost₁ cost₂) :=
  (cases pos neg).consequence (fun _ hp => (Classical.em c).elim (fun h => .inl ⟨hp, h⟩)
    fun h => .inr ⟨hp, h⟩) fun _ h => h

/-- An invariant that every step keeps holds at both ends, at the same cost. -/
theorem invariant (h : Costs S P Q cost) (keeps : ∀ {a b}, S a b → R a → R b) :
    Costs S (fun evm => P evm ∧ R evm) (fun evm => Q evm ∧ R evm) cost :=
  fun evm ⟨hp, hr⟩ =>
    let ⟨after, hreach, hq, hg⟩ := h evm hp
    ⟨after, hreach, ⟨hq, hreach.invariant (S := S) keeps hr⟩, hg⟩

/-- A loop: the run with `k + 1` runs left costs `cost k`, and the exit costs `exitCost`.

From the invariant at `n`, the loop costs the sum of its runs and its exit.

The invariant carries the gas that each run needs. -/
theorem loop {I : Nat → Evm fork Nat → Prop} {cost : Nat → Nat} {exitCost : Nat}
    (body : ∀ k, Costs S (I (k + 1)) (I k) (cost k)) (exit : Costs S (I 0) Q exitCost) :
    ∀ n, Costs S (I n) Q (Triple.loopCost cost n + exitCost)
  | 0 => exit.mono (by simp [Triple.loopCost])
  | n + 1 => ((body n).seq (loop body exit n)).mono (by simp only [Triple.loopCost]; omega)

/-- A loop whose run may lower the measure by more than one, and costs at most `cost`.

From the invariant at `n`, at most `n` runs and the exit follow. -/
theorem loop_lt {I : Nat → Evm fork Nat → Prop} {cost exitCost : Nat}
    (body : ∀ k, Costs S (I (k + 1)) (fun evm => ∃ j < k + 1, I j evm) cost)
    (exit : Costs S (I 0) Q exitCost) (n : Nat) : Costs S (I n) Q (n * cost + exitCost) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => exact exit.mono (by omega)
    | succ k =>
      intro evm hp
      obtain ⟨mid, h₁, ⟨j, hj, hi⟩, g₁⟩ := body k evm hp
      obtain ⟨after, h₂, hq, g₂⟩ := ih j hj mid hi
      -- The later runs number at most `k`, as the measure fell to `j ≤ k`.
      have hjk : j * cost ≤ k * cost := Nat.mul_le_mul_right _ (by omega)
      exact ⟨after, h₁.trans h₂, hq, by rw [Nat.succ_mul]; omega⟩

end Costs

end EthLib.Execution.Evm.Logic
