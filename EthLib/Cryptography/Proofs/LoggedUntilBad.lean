module

public import VCVio.OracleComp.SimSemantics.StateT.UntilBad
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.EvalDist.ProbabilityBounds
public import ToMathlib.Control.WriterT
public import VCVio.EvalDist.Monad.Disagreement.Measure

/-!
# Proofs: two logged oracles that differ only on a bad answer

A handler answers each query, appends the answer's entries to a log, and replies with the answer.

A second handler logs the same entries, but may reply otherwise when they hold a bad entry.

Run over the same stateful oracle, the two runs agree until a bad entry is logged.

So an event of the first run, with no bad entry in its log, has at most its mass in the second run.

This is the fundamental lemma of game playing, for handlers that log their answers.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal

namespace EthLib.Cryptography

section LogReply

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {W : Type}

/-- Answer each query through a handler, log its answer's entries, and reply with a map of it. -/
def logReply (impl : QueryImpl spec (OracleComp spec'))
    (entry : (t : spec.Domain) → spec.Range t → List W)
    (reply : (t : spec.Domain) → spec.Range t → spec.Range t) :
    QueryImpl spec (WriterT (List W) (OracleComp spec')) := fun t =>
  WriterT.mk ((fun u => (reply t u, entry t u)) <$> impl t)

/-- The same handler, with the log kept as a state. -/
def logReplyState (impl : QueryImpl spec (OracleComp spec'))
    (entry : (t : spec.Domain) → spec.Range t → List W)
    (reply : (t : spec.Domain) → spec.Range t → spec.Range t) :
    QueryImpl spec (StateT (List W) (OracleComp spec')) := fun t =>
  StateT.mk fun log => (fun u => (reply t u, log ++ entry t u)) <$> impl t

/-- From a log `log`, the state handler ends with `log` followed by the writer's log. -/
theorem run_simulateQ_logReplyState (impl : QueryImpl spec (OracleComp spec'))
    (entry : (t : spec.Domain) → spec.Range t → List W)
    (reply : (t : spec.Domain) → spec.Range t → spec.Range t)
    {α : Type} (oa : OracleComp spec α) (log : List W) :
    (simulateQ (logReplyState impl entry reply) oa).run log =
      (fun p => (p.1, log ++ p.2)) <$> (simulateQ (logReply impl entry reply) oa).run := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure x => simp
  | query_bind t k ih =>
    simp [logReplyState, logReply, ih, List.append_assoc]

variable {τ : Type} (ro : QueryImpl spec' (StateT τ ProbComp))
  (impl : QueryImpl spec (OracleComp spec'))
  (entry : (t : spec.Domain) → spec.Range t → List W)

/-- **Identical until a bad entry is logged.**

Two handlers log the same entries of each answer.

The second replies with `reply t u` instead of `u`, but only when the entries of `u` hold a bad one.

Both are run over a second, stateful handler, such as a random oracle.

An event of the first run, with no bad entry in its log, has at most its mass in the second run. -/
theorem prEvent_logReply_and_not_bad_le
    (reply : (t : spec.Domain) → spec.Range t → spec.Range t) (bad : W → Prop)
    (hentry : ∀ t u, entry t (reply t u) = entry t u)
    (hreply : ∀ t u, (∀ w ∈ entry t u, ¬bad w) → reply t u = u)
    {α : Type} (oa : OracleComp spec α) (s : τ) (P : (α × List W) × τ → Prop) :
    Pr{let z ← (simulateQ ro (simulateQ (logReply impl entry fun _ u => u) oa).run).run s}[
        P z ∧ ∀ w ∈ z.1.2, ¬bad w]
      ≤ Pr{let z ← (simulateQ ro (simulateQ (logReply impl entry reply) oa).run).run s}[P z] := by
  -- The writer's log is the state handler's, from the empty log.
  have hstate : ∀ r : (t : spec.Domain) → spec.Range t → spec.Range t,
      (simulateQ (logReply impl entry r) oa).run
        = (simulateQ (logReplyState impl entry r) oa).run [] := by
    intro r
    simp [run_simulateQ_logReplyState]
  -- Flattened, each handler extends the random oracle's run by the log.
  let aux : (t : spec.Domain) → τ → spec.Range t → τ → List W → List W :=
    fun t _ u _ log => log ++ entry t u
  have hflat : ∀ r : (t : spec.Domain) → spec.Range t → spec.Range t,
      (∀ t u, entry t (r t u) = entry t u) →
      (ro.mapStateTBase (logReplyState impl entry r)).flattenStateT
        = (ro ∘ₛ fun t => r t <$> impl t).extendStateLeft aux := by
    intro r hr
    funext t
    refine StateT.ext fun st => ?_
    simp [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, logReplyState, aux,
      QueryImpl.apply_compose, map_eq_bind_pure_comp, hr]
  let badSt : List W × τ → Prop := fun st => ∃ w ∈ st.1, bad w
  have hagree : QueryImpl.AgreeUntilBad
      ((ro ∘ₛ fun t => (fun u => u) <$> impl t).extendStateLeft aux)
      ((ro ∘ₛ fun t => reply t <$> impl t).extendStateLeft aux) badSt := by
    intro t st _ Q
    simp only [QueryImpl.extendStateLeft_apply, QueryImpl.apply_compose, simulateQ_map,
      StateT.run_map, id_map', bind_map_left]
    simp only [bind_pure_comp, prEvent_map]
    refine prEvent_congr _ _ _ fun p => ?_
    simp only [badSt, aux, hentry, not_exists, not_and]
    constructor
    · rintro ⟨hQ, hgood⟩
      rw [hreply t p.1 fun w hw => hgood w (List.mem_append_right _ hw)]
      exact ⟨hQ, hgood⟩
    · rintro ⟨hQ, hgood⟩
      rw [hreply t p.1 fun w hw => hgood w (List.mem_append_right _ hw)] at hQ
      exact ⟨hQ, hgood⟩
  have hpres : QueryImpl.PreservesInv
      ((ro ∘ₛ fun t => (fun u => u) <$> impl t).extendStateLeft aux) badSt := by
    intro t st hst z hz
    simp only [QueryImpl.extendStateLeft_apply, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨p, -, rfl⟩ := hz
    obtain ⟨w, hw, hbad⟩ := hst
    exact ⟨w, List.mem_append_left _ hw, hbad⟩
  have h := hagree.prEvent_simulateQ_run_and_not_bad_le hpres oa ([], s)
    fun z => P ((z.1, z.2.1), z.2.2)
  rw [hstate, hstate, simulateQ_mapStateTBase_run_eq_map_flattenStateT,
    simulateQ_mapStateTBase_run_eq_map_flattenStateT, prEvent_map, prEvent_map,
    hflat _ fun _ _ => rfl, hflat reply hentry]
  simpa [badSt] using h

end LogReply

/-- A bound on each continuation holds after a common draw.

Each continuation's event is bounded by another's plus a third event of the first. -/
theorem prEvent_bind_le_add {α β γ : Type} (mx : ProbComp α) (f : α → ProbComp β)
    (g : α → ProbComp γ) (p r : β → Prop) (q : γ → Prop)
    (h : ∀ x, Pr{let y ← f x}[p y] ≤ Pr{let z ← g x}[q z] + Pr{let y ← f x}[r y]) :
    Pr{let x ← mx; let y ← f x}[p y]
      ≤ Pr{let x ← mx; let z ← g x}[q z] + Pr{let x ← mx; let y ← f x}[r y] := by
  have hb := prEvent_bind_le_sum_add_of_support mx f p
    ![fun x ↦ q <$> g x, fun x ↦ r <$> f x] 0 (by
      intro x _
      simpa [Fin.sum_univ_two, prEvent_map] using h x)
  simpa [Fin.sum_univ_two, map_bind, prEvent_map, ← bind_assoc] using hb

end EthLib.Cryptography
