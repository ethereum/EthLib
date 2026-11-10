module

public import EthLib.Cryptography.Proofs.Bls.Security.PopGame
public import EthLib.Cryptography.Proofs.Bls.Security.Reduction
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Proofs: sampling one hash of the aggregate game before the run

The reduction for aggregates programs the key hashes with the hash of the forged message.

So it must know that hash before the run, while the game samples it at the first call.

This file shows that the two orders give the same distribution.

A variant of the message hash fixes to `z` the scalar of its new message at position `j`.

Positions count from 0, as in the reduction for one key.

Running the game with a uniform `z` sampled first is then the game itself.

The argument is the usual one for lazy sampling, for one sample.

- Before the message at position `j`, a step either ignores `z` or uses it as its fresh sample.
- After it, the two oracles agree.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Security

open OracleComp OracleSpec ENNReal

/-! ## One sample drawn early -/

section Generic

variable {ι : Type} {spec : OracleSpec ι} {σ F : Type} [SampleableType F]

/-- The oracles `implAt z` use `z` for one sample of the oracles `impl`.

Once that sample is used, they agree with `impl`.

Before it, a step either ignores `z`, or uses it and reaches a state where it is used.

In the second case, the step of `impl` is that step with `z` uniform. -/
structure EagerAt (impl : QueryImpl spec (StateT σ ProbComp))
    (implAt : F → QueryImpl spec (StateT σ ProbComp)) (used : σ → Prop) : Prop where
  /-- After the sample is used, the oracles agree. -/
  agree : ∀ z t st, used st → (implAt z t).run st = (impl t).run st
  /-- The oracles `impl` never forget that the sample is used. -/
  keep : QueryImpl.PreservesInv impl used
  /-- Before the sample is used, a step ignores `z`, or uses it as `impl` uses a fresh sample. -/
  step : ∀ t st, ¬used st →
    (∀ z, (implAt z t).run st = (impl t).run st) ∨
      ((∀ z, ∀ x ∈ support ((implAt z t).run st), used x.2) ∧
        (impl t).run st =ᵈ (($ᵗ F) >>= fun z => (implAt z t).run st))

/-- From a state where the sample is used, the oracles `implAt z` run as the oracles `impl`. -/
theorem EagerAt.run_eq_of_used {impl : QueryImpl spec (StateT σ ProbComp)}
    {implAt : F → QueryImpl spec (StateT σ ProbComp)} {used : σ → Prop}
    (h : EagerAt impl implAt used) (z : F) {α : Type} (oa : OracleComp spec α) :
    ∀ st, used st → (simulateQ (implAt z) oa).run st =ᵈ (simulateQ impl oa).run st := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro st _; exact EvalDistEq.rfl
  | query_bind t k ih =>
    intro st hst
    simp only [simulateQ_query_bind, StateT.run_bind, liftM, monadLift_self,
      OracleQuery.input_query, OracleQuery.cont_query, id]
    rw [h.agree z t st hst]
    exact EvalDistEq.bind_congr_of_support _ fun p hp => ih p.1 p.2 (h.keep t st hst p hp)

/-- **Eager sampling.** Drawing `z` first gives the distribution of drawing the sample when used. -/
theorem EagerAt.evalDist_run {impl : QueryImpl spec (StateT σ ProbComp)}
    {implAt : F → QueryImpl spec (StateT σ ProbComp)} {used : σ → Prop}
    (h : EagerAt impl implAt used) {α : Type} (oa : OracleComp spec α) (st : σ) :
    (simulateQ impl oa).run st =ᵈ (($ᵗ F) >>= fun z => (simulateQ (implAt z) oa).run st) := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a => exact (EvalDistEq.bind_const _ _).symm
  | query_bind t k ih =>
    by_cases hst : used st
    · exact (EvalDistEq.trans (EvalDistEq.bind_right _ fun z =>
        h.run_eq_of_used z (query t >>= k) st hst) (EvalDistEq.bind_const _ _)).symm
    simp only [simulateQ_query_bind, StateT.run_bind, liftM, monadLift_self,
      OracleQuery.input_query, OracleQuery.cont_query, id]
    rcases h.step t st hst with ha | ⟨hu, hb⟩
    · simp only [ha]
      refine EvalDistEq.trans ?_ (EvalDistEq.bind_bind_swap _ _ _).symm
      exact EvalDistEq.bind_right _ fun p => ih p.1 p.2
    · refine (EvalDistEq.bind_left hb _).trans ?_
      rw [bind_assoc]
      refine EvalDistEq.bind_right _ fun z => EvalDistEq.bind_congr_of_support _ fun p hp => ?_
      exact (h.run_eq_of_used z (k p.1) p.2 (hu z p hp)).symm

end Generic

/-! ## The message hash with one scalar fixed -/

variable {F G₁ G₂ M : Type} [DecidableEq M] [CommRing F] [SampleableType F]
  [AddCommGroup G₂] [Module F G₂]

/-- The random oracle `H` with the scalar of its new message at position `j` fixed to `z`.

The new message at position `j` hashes to `z • g2`; every other call is as in `H`. -/
def hashAt (g₂ : G₂) (j : ℕ) (z : F) (m : M) : StateT (State F M) ProbComp G₂ := fun st =>
  match lookup m st.table with
  | some _ => hash g₂ m st
  | none =>
    if st.table.length = j then
      pure (z • g₂, { st with table := st.table ++ [(m, z)], calls := st.calls + 1 })
    else hash g₂ m st

/-- The signing oracle under `a`, on the message hash with its scalar at `j` fixed to `z`. -/
def signAt (g₂ : G₂) (a : F) (j : ℕ) (z : F) (m : M) : StateT (State F M) ProbComp G₂ :=
  fun st => (fun w => (a • w.1, { w.2 with signed := w.2.signed ++ [m] })) <$> hashAt g₂ j z m st

/-- Away from a new message at position `j`, the hash with a fixed scalar is the hash. -/
theorem hashAt_eq_hash {g₂ : G₂} {j : ℕ} {z : F} {m : M} {st : State F M}
    (h : lookup m st.table = none → st.table.length ≠ j) : hashAt g₂ j z m st = hash g₂ m st := by
  unfold hashAt
  split
  · rfl
  · next hl => simp [h hl]

/-- A new message at position `j` hashes to `z • g2`. -/
theorem hashAt_of_new {g₂ : G₂} {j : ℕ} {z : F} {m : M} {st : State F M}
    (hl : lookup m st.table = none) (hj : st.table.length = j) :
    hashAt g₂ j z m st =
      pure (z • g₂, { st with table := st.table ++ [(m, z)], calls := st.calls + 1 }) := by
  unfold hashAt
  simp [hl, hj]

/-- A hash call never shortens the table. -/
theorem length_le_of_mem_support_hash {g₂ : G₂} {m : M} {st : State F M} {w : G₂ × State F M}
    (hw : w ∈ support (hash g₂ m st)) : st.table.length ≤ w.2.table.length := by
  rcases (mem_support_hash (st := st) hw).2.1 with h | ⟨e, h⟩ <;> simp [h]

namespace Pop

variable [DecidableEq G₁] [AddCommGroup G₁] [Module F G₁]

/-- The oracles of the aggregate game, with the message hash scalar at `j` fixed to `z`. -/
def implAt (g₂ : G₂) (a : F) (j : ℕ) (z : F) :
    QueryImpl (Spec M G₁ G₂) (StateT (State F G₁ M) ProbComp)
  | .inl n => fun st => (·, st) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl (.inl m)) => (onMsg (hashAt g₂ j z m) : StateT (State F G₁ M) ProbComp G₂)
  | .inr (.inl (.inr m)) => (onMsg (signAt g₂ a j z m) : StateT (State F G₁ M) ProbComp G₂)
  | .inr (.inr x) => (keyHash g₂ x : StateT (State F G₁ M) ProbComp G₂)

omit [AddCommGroup G₁] [Module F G₁] in
/-- The oracles with the message scalar at `j` fixed draw it early, compared with the game's.

The sample is used once the message table has more than `j` entries. -/
theorem eagerAt_implAt (g₂ : G₂) (a : F) (j : ℕ) :
    EagerAt (impl (M := M) (G₁ := G₁) g₂ a) (implAt g₂ a j)
      fun st => j < st.msg.table.length := by
  refine ⟨?_, ?_, ?_⟩
  · intro z t st hst
    rcases t with n | (m | m) | x
    · rfl
    · show (fun w => _) <$> hashAt g₂ j z m st.msg = (fun w => _) <$> hash g₂ m st.msg
      rw [hashAt_eq_hash fun _ => by omega]
    · show (fun w => _) <$> ((fun w => _) <$> hashAt g₂ j z m st.msg) =
        (fun w => _) <$> ((fun w => _) <$> hash g₂ m st.msg)
      rw [hashAt_eq_hash fun _ => by omega]
    · rfl
  · intro t st hst x hx
    rcases t with n | (m | m) | y
    · change x ∈ support ((·, st) <$> _) at hx
      simp only [support_map, Set.mem_image] at hx
      obtain ⟨_, -, rfl⟩ := hx
      exact hst
    · change x ∈ support ((fun w => _) <$> hash g₂ m st.msg) at hx
      simp only [support_map, Set.mem_image] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      exact lt_of_lt_of_le hst (length_le_of_mem_support_hash hw)
    · change x ∈ support ((fun w => _) <$> ((fun w => _) <$> hash g₂ m st.msg)) at hx
      simp only [support_map, Set.mem_image] at hx
      obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hx
      exact lt_of_lt_of_le hst (length_le_of_mem_support_hash hw)
    · change x ∈ support (keyHash g₂ y st) at hx
      unfold keyHash at hx
      split at hx
      · simp only [support_pure, Set.mem_singleton_iff] at hx
        subst hx
        exact hst
      · simp only [support_map, Set.mem_image] at hx
        obtain ⟨_, -, rfl⟩ := hx
        exact hst
  · intro t st hst
    rcases t with n | (m | m) | y
    · exact Or.inl fun _ => rfl
    · by_cases hnew : lookup m st.msg.table = none ∧ st.msg.table.length = j
      · right
        refine ⟨fun z x hx => ?_, ?_⟩
        · change x ∈ support ((fun w => _) <$> hashAt g₂ j z m st.msg) at hx
          rw [hashAt_of_new hnew.1 hnew.2] at hx
          simp only [map_pure, support_pure, Set.mem_singleton_iff] at hx
          subst hx
          simp [hnew.2]
        · show (fun w => _) <$> hash g₂ m st.msg =ᵈ
            (($ᵗ F) >>= fun z => (fun w => _) <$> hashAt g₂ j z m st.msg)
          simp only [hash_of_lookup_none hnew.1, hashAt_of_new hnew.1 hnew.2,
            map_eq_bind_pure_comp,
            bind_assoc, pure_bind, Function.comp_apply]
          rfl
      · left
        intro z
        show (fun w => _) <$> hashAt g₂ j z m st.msg = (fun w => _) <$> hash g₂ m st.msg
        rw [hashAt_eq_hash fun hl hj => hnew ⟨hl, hj⟩]
    · by_cases hnew : lookup m st.msg.table = none ∧ st.msg.table.length = j
      · right
        refine ⟨fun z x hx => ?_, ?_⟩
        · change x ∈ support ((fun w => _) <$> ((fun w => _) <$> hashAt g₂ j z m st.msg)) at hx
          rw [hashAt_of_new hnew.1 hnew.2] at hx
          simp only [map_pure, support_pure, Set.mem_singleton_iff] at hx
          subst hx
          simp [hnew.2]
        · show (fun w => _) <$> ((fun w => _) <$> hash g₂ m st.msg) =ᵈ
            (($ᵗ F) >>= fun z => (fun w => _) <$> ((fun w => _) <$> hashAt g₂ j z m st.msg))
          simp only [hash_of_lookup_none hnew.1, hashAt_of_new hnew.1 hnew.2,
            map_eq_bind_pure_comp,
            bind_assoc, pure_bind, Function.comp_apply]
          rfl
      · left
        intro z
        show (fun w => _) <$> ((fun w => _) <$> hashAt g₂ j z m st.msg) =
          (fun w => _) <$> ((fun w => _) <$> hash g₂ m st.msg)
        rw [hashAt_eq_hash fun hl hj => hnew ⟨hl, hj⟩]
    · exact Or.inl fun _ => rfl

omit [AddCommGroup G₁] [Module F G₁] in
/-- A run of the game's oracles is distributed as the run that draws the scalar at `j` first. -/
theorem run_impl_eq_uniform_implAt {α : Type} (g₂ : G₂) (a : F) (j : ℕ)
    (oa : OracleComp (Spec M G₁ G₂) α) (st : State F G₁ M) :
    (simulateQ (impl g₂ a) oa).run st =ᵈ
      (($ᵗ F) >>= fun z => (simulateQ (implAt g₂ a j z) oa).run st) :=
  (eagerAt_implAt g₂ a j).evalDist_run oa st

/-- The aggregate game, with the message hash scalar at `j` drawn right after the secret key. -/
def experimentAt (scheme : Scheme G₁ G₂) (adversary : Adversary G₁ G₂ M) (j : ℕ) :
    ProbComp (Bool × State F G₁ M) := do
  let a ← $ᵗ F
  let z ← $ᵗ F
  let pk := a • scheme.g₁
  let (w, st) ← (do
    let hpk ← keyHash scheme.g₂ pk
    simulateQ (implAt scheme.g₂ a j z) (run adversary pk (a • hpk))).run State.init
  return (wins scheme pk st.msg.signed w, st)

/-- **The aggregate game with one message scalar drawn first.**

For every position `j`, the game is distributed as the game that draws that scalar after the key. -/
theorem experiment_eq_experimentAt (scheme : Scheme G₁ G₂) (adversary : Adversary G₁ G₂ M)
    (j : ℕ) : experiment (F := F) scheme adversary =ᵈ experimentAt scheme adversary j := by
  unfold experiment experimentAt
  refine EvalDistEq.bind_right _ fun a => ?_
  simp only [StateT.run_bind, bind_assoc]
  refine (EvalDistEq.bind_right _ fun (p : G₂ × State F G₁ M) =>
    EvalDistEq.bind_left (run_impl_eq_uniform_implAt scheme.g₂ a j _ p.2) _).trans ?_
  simp only [bind_assoc]
  exact EvalDistEq.bind_bind_swap _ _ _

end Pop

end EthLib.Cryptography.Bls.Security
