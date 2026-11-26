module

public import VCVio.OracleComp.SimSemantics.Append.Core
public import ToMathlib.Control.WriterT
public import PolyFun.PFunctor.Free.Cost

/-!
# Proofs: charge bounds through a sum of bounds, a nested sum of oracles and a simulation

Two charge bounds combine into one bound for a weighted sum of the charges.

A run with a state and a log is charged as the computation it runs.
-/

@[expose] public section

namespace PFunctor.FreeM

variable {P : PFunctor} {α : Type*}

/-- Two charge bounds give one for the first charge plus `S` times the second. -/
theorem IsChargeBound.add_mul {x : FreeM P α} {c₁ c₂ : P.A → ℕ} {B₁ B₂ s₁ s₂ : ℕ}
    (h₁ : IsChargeBound x c₁ B₁ s₁) (h₂ : IsChargeBound x c₂ B₂ s₂) (S : ℕ) :
    IsChargeBound x (fun a => c₁ a + c₂ a * S) (B₁ + B₂ * S) (s₁ + s₂ * S) := by
  -- The pair of amounts `(x, y)` weighs `x + y * S`, which is additive and monotone.
  let weigh : ℕ × ℕ →+o ℕ :=
    { toFun := fun p => p.1 + p.2 * S
      map_zero' := by simp
      map_add' := fun p p' => by simp only [Prod.fst_add, Prod.snd_add]; ring
      monotone' := fun _ _ h =>
        add_le_add (Prod.le_def.1 h).1 (Nat.mul_le_mul_right S (Prod.le_def.1 h).2) }
  exact (isChargeBound_prod_iff.2 ⟨h₁, h₂⟩).map weigh

end PFunctor.FreeM

namespace OracleComp

open OracleSpec PFunctor.FreeM

/-! ## Lifts into a nested sum

A lift of a computation into `(a + b) + c` resolves through `a + (b + c)`.

The lemmas on one summand of a sum read the lift of computations instead.
-/

section NestedSum

variable {κ₁ κ₂ κ₃ : Type} {a : OracleSpec κ₁} {b : OracleSpec κ₂} {c : OracleSpec κ₃}

/-- A computation over `a + b` lifts to `(a + b) + c` the same way by both routes. -/
theorem liftComp_eq_liftM_add_add {α : Type} (oa : OracleComp (a + b) α) :
    oa.liftComp ((a + b) + c) = (liftM oa : OracleComp ((a + b) + c) α) := by
  rw [liftM_eq_liftComp_liftM, ← liftComp_eq_liftM]
  exact (liftComp_liftComp (fun t => by rcases t with n | i <;> rfl) oa).symm

/-- Queries over `a + b` lifted to `(a + b) + c` are answered by the left handler. -/
theorem simulateQ_add_liftM_add_add {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl₁ : QueryImpl (a + b) m) (impl₂ : QueryImpl c m) {α : Type} (oa : OracleComp (a + b) α) :
    simulateQ (impl₁ + impl₂) (liftM oa : OracleComp ((a + b) + c) α) = simulateQ impl₁ oa := by
  rw [← liftComp_eq_liftM_add_add, simulateQ_add_liftComp_sum_left]

end NestedSum

/-! ## The charge of a run with a state and a log -/

section RunCharge

variable {ι₀ ι₁ : Type} {spec : OracleSpec ι₀} {spec' : OracleSpec ι₁} {σ L : Type}
  [EmptyCollection L] [Append L] [LawfulAppend L]

/-- **A run with a state and a log is charged as the computation it runs.**

Let the answer to each query `t`, from every state, cost at most `c t` under `d`.

A computation within `B` under `c` then runs within `B` under `d`, from every state. -/
theorem isChargeBound_run_simulateQ {ω : Type} [AddMonoid ω] [Preorder ω] [AddLeftMono ω]
    [AddRightMono ω] (impl : QueryImpl spec (StateT σ (WriterT L (OracleComp spec'))))
    {c : spec.Domain → ω} {d : spec'.Domain → ω}
    (hstep : ∀ t s, IsChargeBound ((impl t).run s).run d (c t))
    {α : Type} {oa : OracleComp spec α} {B spent : ω} (h : IsChargeBound oa c B spent) (s : σ) :
    IsChargeBound ((simulateQ impl oa).run s).run d B spent := by
  induction oa using OracleComp.inductionOn generalizing spent s with
  | pure x => exact h
  | query_bind t k ih =>
    replace h := (isChargeBound_lift_bind_iff' (P := spec.toPFunctor) (c := c) t k).1 h
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, WriterT.run_bind']
    have hstep' := (hstep t s).add_left spent
    rw [add_zero] at hstep'
    exact hstep'.bind_of_le h.1 fun p s' hs' =>
      (isChargeBound_map_iff' _ _).2 ((ih p.1.1 (h.2 p.1.1) p.1.2).mono_spent hs')

end RunCharge

end OracleComp
