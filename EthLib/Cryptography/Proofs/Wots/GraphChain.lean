module

public import EthLib.Cryptography.Wots
public import VCVio.OracleComp.QueryTracking.RandomOracle.TouchRead.Unary

/-!
# WOTS+C chains in the eager graph interpreter

A chain edge has two public hash outputs at the same input digest.

The next edge consumes the low output and the cache retains the high output.

Source: leanXMSS draft, section "WOTS+C", chain equation for `C_(i,mu+1)`.

Revision: leanVM commit `4af2cdddd7cd41b9df2cc7e123e314a91b0b4462`.
-/

public section

open OracleComp OracleSpec

namespace EthLib.Cryptography.Wots.GraphChain

variable {ι X K R D : Type} {pub : OracleSpec ι} {n : Nat}

/-- The points for each of the two halves of each hash have the same input cell. -/
structure Schedule (G : CanonicalGraph pub X K R) (n : Nat) where
  /-- Cell containing a chain position, used at positions from zero to `n`. -/
  cell : Nat → X ⊕ K
  /-- First half of the hash reply at an edge. -/
  low : Fin n → K
  /-- Second half of the same reply. -/
  high : Fin n → K
  low_children (j : Fin n) : G.ch (low j) = [cell j.val]
  high_children (j : Fin n) : G.ch (high j) = [cell j.val]
  next (j : Fin n) : cell (j.val + 1) = .inr (low j)

variable {G : CanonicalGraph pub X K R} (S : Schedule G n) (e : D ≃ R)

/-- Query both halves of the actual public point and return the low digest. -/
@[expose] def publicStep (j : Fin n) (d : D) : OracleComp (pub.withLabels X K R) D := do
  let a ← query (spec := pub.withLabels X K R) (.inl (.inl (.inr (G.pt (S.low j) [e d]))))
  let _ ← query (spec := pub.withLabels X K R) (.inl (.inl (.inr (G.pt (S.high j) [e d]))))
  pure (e.symm (cast (G.range_eq (S.low j) [e d]) a))

/-- A chain prefix only touches both nodes of every intermediate edge. -/
def touchStep (j : Fin n) (_ : Unit) : OracleComp (pub.withLabels X K R) Unit := do
  touchCell (some (.inr (S.low j)))
  touchCell (some (.inr (S.high j)))

/-- The final edge reads the low node for the signature and touches the high node. -/
noncomputable def finalStep [Nonempty R] (j : Fin n) : OracleComp (pub.withLabels X K R) D := do
  let a ← readCell (some (.inr (S.low j)))
  touchCell (some (.inr (S.high j)))
  pure (e.symm a)

variable [DecidableEq ι] [DecidableEq X] [DecidableEq K] [SampleableType R]
  [∀ t, SampleableType (pub.Range t)]

private theorem step_of_cached (j : Fin n) (d : D) (st : RelabelState pub X K R)
    (hc : st.2 (S.cell j.val) = some (e d)) :
    (simulateQ G.eagerImpl (publicStep S e j d)).run st =
      (simulateQ G.eagerImpl (finalStep S e j)).run st := by
  have eqn := congrArg (fun p => (fun z => (e.symm z.1.1, z.2)) <$> p)
    (G.eagerImpl_unary_siblings_run_of_cached (S.low j) (S.high j) (S.cell j.val)
      (S.low_children j) (S.high_children j) st (e d) hc)
  simpa only [publicStep, finalStep, simulateQ_bind, simulateQ_pure, StateT.run_bind,
    StateT.run_pure, G.simulateQ_eagerImpl_touchCell, map_bind, map_pure, bind_map_left,
    StateT.run_map] using eqn

private theorem forget_step (j : Fin n) (st : RelabelState pub X K R) :
    (fun z => ((), z.2)) <$> (simulateQ G.eagerImpl (finalStep S e j)).run st =
      (simulateQ G.eagerImpl (touchStep S j ())).run st := by
  simp only [finalStep, touchStep, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    G.simulateQ_eagerImpl_touchCell, StateT.run_map, map_bind, map_pure, bind_map_left]
  simp only [← bind_pure_comp]

private theorem next_cell (j : Fin n) (st : RelabelState pub X K R) {z}
    (hz : z ∈ support ((simulateQ G.eagerImpl (finalStep S e j)).run st)) :
    z.2.2 (S.cell (j.val + 1)) = some (e z.1) := by
  rw [S.next]
  simp only [finalStep, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    G.eagerImpl_readCell_run, G.eagerImpl_touchCell_run, bind_map_left, mem_support_bind_iff,
    mem_support_pure_iff] at hz
  obtain ⟨first, hfirst, last, hlast, rfl⟩ := hz
  simpa using (RelabelState.le_and_cell_eq_of_mem_support_drawCell hlast).1.2
    (RelabelState.le_and_cell_eq_of_mem_support_drawCell hfirst).2

variable (step : Fin n → D → OracleComp (pub.withLabels X K R) D)
  (hstep : ∀ j d, simulateQ G.eagerImpl (step j d) = simulateQ G.eagerImpl (publicStep S e j d))

include hstep

private theorem advance (j : Fin n) (p : ProbComp (D × RelabelState pub X K R))
    (t : ProbComp (Unit × RelabelState pub X K R))
    (dropped : (fun z => ((), z.2)) <$> p = t)
    (stored : ∀ z ∈ support p, z.2.2 (S.cell j.val) = some (e z.1)) :
    (p >>= fun z => (simulateQ G.eagerImpl (step j z.1)).run z.2) =
      (t >>= fun z => (simulateQ G.eagerImpl (finalStep S e j)).run z.2) := by
  rw [← dropped, bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro z hz
  rw [hstep]
  exact step_of_cached S e j _ _ (stored z hz)

private theorem prefix_facts (start steps : Nat) (h : start + steps ≤ n)
    (d : D) (st : RelabelState pub X K R) (initial : st.2 (S.cell start) = some (e d)) :
    ((fun z => ((), z.2)) <$> (simulateQ G.eagerImpl (chain step start steps h d)).run st =
      (simulateQ G.eagerImpl (chain (touchStep S) start steps h ())).run st) ∧
    (∀ z ∈ support ((simulateQ G.eagerImpl (chain step start steps h d)).run st),
      z.2.2 (S.cell (start + steps)) = some (e z.1)) := by
  induction steps with
  | zero =>
    simp [chain, initial]
  | succ s ih =>
    have prev : start + s ≤ n := by omega
    let j : Fin n := ⟨start + s, by omega⟩
    obtain ⟨dropped, stored⟩ := ih prev
    have last := advance S e step hstep j _ _ dropped stored
    constructor
    -- Discarding the low digest turns the last read into another touch.
    · simp only [chain, simulateQ_bind, StateT.run_bind]
      rw [last, map_bind]
      exact OracleComp.bind_congr_of_forall_mem_support _ fun z _ => forget_step S e j z.2
    -- The high touch preserves the low value that feeds the next edge.
    · intro z hz
      simp only [chain, simulateQ_bind, StateT.run_bind] at hz
      rw [last, mem_support_bind_iff] at hz
      obtain ⟨w, _, hw⟩ := hz
      exact next_cell S e j w.2 hw

/-- Walk a positive number of steps from a cached input digest.

Each earlier step touches both output cells.

Only the low output of the final step is read.

The returned digest and complete public and label caches agree. -/
theorem chain_succ_run (start steps : Nat) (h : start + (steps + 1) ≤ n)
    (d : D) (st : RelabelState pub X K R) (initial : st.2 (S.cell start) = some (e d)) :
    (simulateQ G.eagerImpl (chain step start (steps + 1) h d)).run st =
      (simulateQ G.eagerImpl (do
        let _ ← chain (touchStep S) start steps (by omega) ()
        finalStep S e ⟨start + steps, by omega⟩)).run st := by
  obtain ⟨dropped, stored⟩ := prefix_facts S e step hstep start steps (by omega) d st initial
  simp only [chain, simulateQ_bind, StateT.run_bind]
  exact advance S e step hstep ⟨start + steps, by omega⟩ _ _ dropped stored

/-- A read of the start cell supplies the cached input for the entire walk.

The normalized walk operates from every initial state. -/
theorem chain_succ_from_read (start steps : Nat) (h : start + (steps + 1) ≤ n) :
    simulateQ G.eagerImpl (do
      let x ← readCell (some (S.cell start))
      chain step start (steps + 1) h (e.symm x)) =
    simulateQ G.eagerImpl (do
      touchCell (some (S.cell start))
      let _ ← chain (touchStep S) start steps (by omega) ()
      finalStep S e ⟨start + steps, by omega⟩) := by
  ext st : 1
  simp only [simulateQ_bind, StateT.run_bind, G.eagerImpl_readCell_run, G.eagerImpl_touchCell_run,
    bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro z hz
  have recorded := (RelabelState.le_and_cell_eq_of_mem_support_drawCell hz).2
  simpa only [simulateQ_bind, StateT.run_bind] using
    chain_succ_run S e step hstep start steps h (e.symm z.1) z.2 (by simpa using recorded)

/-- Read the requested chain position after touching the inputs and unused outputs of the walk. -/
noncomputable def walkFromRead (start : Nat) :
    (steps : Nat) → start + steps ≤ n → OracleComp (pub.withLabels X K R) D
  | 0, _ => e.symm <$> readCell (some (S.cell start))
  | steps + 1, h => do
    touchCell (some (S.cell start))
    let _ ← chain (touchStep S) start steps (by omega) ()
    finalStep S e ⟨start + steps, by omega⟩

/-- A zero-length walk reads its input directly.

A positive walk touches both halves of intermediate hashes and reads its final low output. -/
theorem chain_from_read (start steps : Nat) (h : start + steps ≤ n) :
    simulateQ G.eagerImpl (do
      let x ← readCell (some (S.cell start))
      chain step start steps h (e.symm x)) =
    simulateQ G.eagerImpl (walkFromRead S e start steps h) := by
  cases steps with
  | zero => simp [chain, walkFromRead, ← bind_pure_comp]
  | succ s => exact chain_succ_from_read S e step hstep start s h

end EthLib.Cryptography.Wots.GraphChain
