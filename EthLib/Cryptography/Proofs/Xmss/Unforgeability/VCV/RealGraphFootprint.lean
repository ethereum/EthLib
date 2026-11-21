module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealGraphBound
public import VCVio.OracleComp.QueryTracking.RandomOracle.Defer

/-!
# The original source tariff in the graph game

Each raw request can add a single physical input across both public hash rows.

The external graph keeps private starts in its label table.

The remaining random-oracle tables live inside the signing program.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient
open OracleComp OracleSpec HashSig SecretEncoding.Residual
open RandomOraclePairedValue
open scoped OracleSpec.PrimitiveQuery
namespace Footprint

variable {K : Type}
abbrev State (K : Type) := RelabelState PairedHashWord.HalfSpec StartKey K (BitVec digestBits)

/-- Count the low or high row of each physical public input once. -/
@[expose] def inputs (s : State K) : Set HashInput :=
  {b | (s.1 (.inl b)).isSome ∨ (s.1 (.inr b)).isSome}

open Classical in
/-- Expand a single original source request, retaining the residual caches inside the caller. -/
@[expose] noncomputable def inner (pp : PublicParam) :
    QueryImpl Source (StateT (ResidualCache pp) (OracleComp ChainWorld)) :=
  QueryImpl.compose (handler (pub := PairedHashWord.HalfSpec) (aux := Tick)
    (X := StartKey) (Z := OtherPrivate pp) (R := BitVec digestBits))
    (QueryImpl.compose (SecretEncoding.reindexQueries KeyBackend (privateKeyEquiv pp).symm)
      (Derivations.expand Tick PairedHashWord.halves))

open Classical in
theorem source_eq {α : Type} (pp : PublicParam) (body : OracleComp Source α)
    (s : ResidualCache pp) :
    residualProgram pp body s = (simulateQ (inner pp) body).run s := by
  unfold residualProgram keyedProgram inner
  rw [QueryImpl.simulateQ_compose, QueryImpl.simulateQ_compose]

variable (G : CanonicalGraph PairedHashWord.HalfSpec StartKey K (BitVec digestBits))

open Classical in
/-- Execute one source query against both local caches and the external relabelled graph. -/
@[expose] noncomputable def step (pp : PublicParam) : QueryImpl Source
    (StateT (ResidualCache pp × State K) ProbComp) := fun t => StateT.mk fun s =>
  (fun v => (v.1.1, v.1.2, v.2)) <$> (simulateQ G.relabelImpl ((inner pp t).run s.1)).run s.2

open Classical in
theorem run_step {α : Type} (pp : PublicParam) (body : OracleComp Source α)
    (l : ResidualCache pp) (s : State K) :
    (simulateQ G.relabelImpl ((simulateQ (inner pp) body).run l)).run s =
    (fun z => ((z.1, z.2.1), z.2.2)) <$> (simulateQ (step G pp) body).run (l, s) := by
  induction body using OracleComp.inductionOn generalizing l s with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, step,
      StateT.run_mk, bind_map_left]
    exact bind_congr fun w => ih w.1.1 w.1.2 w.2

open Classical in
private theorem draw_frame {α : Type} (p : ProbComp α) (s : State K) :
    (simulateQ G.relabelImpl (liftM p : OracleComp ChainWorld α)).run s = (·, s) <$> p := by
  induction p using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [liftM_bind, simulateQ_bind, StateT.run_bind, map_bind]
    have h : (simulateQ G.relabelImpl (liftM (liftM (unifSpec.query t) : ProbComp _) :
        OracleComp ChainWorld _)).run s = (·, s) <$> (liftM (unifSpec.query t) : ProbComp _) :=
      by
        have lift_query : (liftM (liftM (unifSpec.query t) : ProbComp _) : OracleComp ChainWorld _)
          =
            liftM (ChainWorld.query (.inl (.inl t))) := by rfl
        rw [lift_query, simulateQ_spec_query]
        exact G.relabelImpl_run_unif t s
    rw [h, bind_map_left]
    exact bind_congr fun v => ih v

open Classical in
private theorem public_frame (k : HashInput ⊕ HashInput) (s : State K) {w}
    (hit : w ∈ support ((G.relabelImpl (.inl (.inr k))).run s)) (other : HashInput ⊕ HashInput)
    (different : other ≠ k) : w.2.1 other = s.1 other := by
  by_cases ready : ∃ n vs, G.childVals s n = some vs ∧ G.pt n vs = k
  · obtain ⟨n, vs, children, rfl⟩ := ready
    rw [G.relabelImpl_run_pt children, support_map] at hit
    obtain ⟨u, hu, rfl⟩ := hit
    rw [RelabelState.drawCell_run, support_map] at hu
    obtain ⟨_, _, rfl⟩ := hu
    rfl
  · rw [G.relabelImpl_run_pub_of_not_exists ready, support_map] at hit
    obtain ⟨u, hu, rfl⟩ := hit
    exact (congrArg (fun c : PairedHashWord.HalfSpec.QueryCache => c other)
      (QueryImpl.withCaching_run_eq_cacheQuery uniformSampleImpl hu)).trans
        (QueryCache.cacheQuery_of_ne _ _ different)

open Classical in
private theorem public_inputs (k : HashInput ⊕ HashInput) (s : State K) {w}
    (hit : w ∈ support ((G.relabelImpl (.inl (.inr k))).run s)) :
    inputs w.2 ⊆ insert (k.elim id id) (inputs s) := by
  intro b present
  by_cases same : b = k.elim id id
  · exact Or.inl same
  · apply Set.mem_insert_of_mem
    have left : Sum.inl b ≠ k := fun eq => same (congrArg (Sum.elim id id) eq)
    have right : Sum.inr b ≠ k := fun eq => same (congrArg (Sum.elim id id) eq)
    simpa only [inputs, Set.mem_ofPred_eq, public_frame G k s hit _ left,
      public_frame G k s hit _ right] using present

open Classical in
private theorem private_frame (pp : PublicParam) (k : StartKey ⊕ OtherPrivate pp)
    (l : ResidualCache pp) (s : State K) {z} (run : z ∈ support
      ((simulateQ G.relabelImpl ((handler (pub := PairedHashWord.HalfSpec) (aux := Tick)
        (X := StartKey) (Z := OtherPrivate pp) (R := BitVec digestBits) (.inr k)).run l)).run s)) :
    z.2.1 = s.1 := by
  rcases k with x | other
  · simp [handler, G.relabelImpl_apply_inr, RelabelState.drawCell_run, Functor.map_map] at run
    obtain ⟨_, _, _, rfl⟩ := run
    rfl
  · simp [handler, draw_frame G, Functor.map_map] at run
    obtain ⟨_, _, _, rfl⟩ := run
    rfl

open Classical in
private theorem private_split (pp : PublicParam) (key : PrfInput) :
    inner pp (.inr key) = (do
      let lo ← handler (pub := PairedHashWord.HalfSpec) (aux := Tick)
        (X := StartKey) (Z := OtherPrivate pp) (R := BitVec digestBits)
        (.inr ((privateKeyEquiv pp).symm (.inl key)))
      let hi ← handler (pub := PairedHashWord.HalfSpec) (aux := Tick)
        (X := StartKey) (Z := OtherPrivate pp) (R := BitVec digestBits)
        (.inr ((privateKeyEquiv pp).symm (.inr key)))
      pure (PairedHashWord.halves.symm (lo, hi))) := by
  simp [inner, QueryImpl.compose, Derivations.expand, Derivations.pair, Derivations.privateWord,
    SecretEncoding.reindexQueries]

open Classical in
private theorem public_split (pp : PublicParam) (b : HashInput) (l : ResidualCache pp) :
    (inner pp (.inl (.inr (.inl b)))).run l = (do
      let lo ← liftM (ChainWorld.query (.inl (.inr (.inl b))))
      let hi ← liftM (ChainWorld.query (.inl (.inr (.inr b))))
      pure (PairedHashWord.halves.symm (lo, hi), l)) := by
  simp [inner, QueryImpl.compose, Derivations.expand, Derivations.pair, Derivations.publicWord,
    SecretEncoding.reindexQueries, handler, StateT.run_bind]

open Classical in
private theorem increase (pp : PublicParam) (t : Source.Domain)
    (initial : ResidualCache pp × State K)
    {z} (hit : z ∈ support ((step G pp t).run initial)) :
    (inputs z.2.2).encard ≤ (inputs initial.2).encard + paidFee t := by
  classical
  rcases initial with ⟨l, s⟩
  simp only [step, StateT.run_mk, support_map] at hit
  obtain ⟨w, hw, rfl⟩ := hit
  rcases t with ((n | (b | tick)) | key)
  · simp [inner, QueryImpl.compose, Derivations.expand, SecretEncoding.reindexQueries, handler,
      G.relabelImpl_run_unif, Functor.map_map] at hw
    obtain ⟨_, _, rfl⟩ := hw
    change (inputs s).encard ≤ (inputs s).encard + 0
    simp
  · rw [public_split] at hw
    simp only [simulateQ_bind, simulateQ_pure, simulateQ_spec_query, StateT.run_bind,
      StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at hw
    obtain ⟨low, hl, high, hh, rfl⟩ := hw
    have lo := public_inputs G (.inl b) s hl
    have hi := public_inputs G (.inr b) low.2 hh
    have both := hi.trans (by simpa using Set.insert_subset_insert (a := b) lo)
    exact (Set.encard_le_encard both).trans (Set.encard_insert_le _ _)
  · simp [inner, QueryImpl.compose, Derivations.expand, SecretEncoding.reindexQueries, handler,
      draw_frame G, Functor.map_map] at hw
    obtain ⟨_, _, _, rfl⟩ := hw
    exact le_self_add
  · rw [private_split] at hw
    simp only [StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
      mem_support_bind_iff, mem_support_pure_iff] at hw
    obtain ⟨lo, hlo, hi, hhi, rfl⟩ := hw
    have a := private_frame G pp _ l s hlo
    have b := private_frame G pp _ lo.1.2 lo.2 hhi
    change (inputs hi.2).encard ≤ (inputs s).encard + _
    have equality : inputs hi.2 = inputs s := by
      unfold inputs
      rw [b, a]
    rw [equality]
    exact le_self_add

open Classical in
/-- A source program requests only uniforms, public halves and private starts.

Consequently its canonical lift leaves the deferred schedule exactly as it found it.
-/
theorem deferred_lift {α : Type} (body : OracleComp ChainWorld α) (s : State K)
    (pending : List (StartKey ⊕ K)) :
    (simulateQ G.deferredImpl (liftComp body
      (PairedHashWord.HalfSpec.withLabels StartKey K (BitVec digestBits)))).run (s, pending) =
    (fun z => (z.1, z.2, pending)) <$> (simulateQ G.relabelImpl body).run s := by
  induction body using OracleComp.inductionOn generalizing s with
  | pure v => simp
  | query_bind t k ih =>
    simp only [liftComp_bind, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, map_bind]
    have forward : ∀ (t : ChainWorld.Domain),
        (simulateQ G.deferredImpl (liftComp (liftM (ChainWorld.query t) : OracleComp ChainWorld _)
          (PairedHashWord.HalfSpec.withLabels StartKey K (BitVec digestBits)))).run (s, pending) =
          (fun z => (z.1, z.2, pending)) <$> (G.relabelImpl t).run s := by
      intro t
      have lifted : liftComp (liftM (ChainWorld.query t) : OracleComp ChainWorld _)
          (PairedHashWord.HalfSpec.withLabels StartKey K (BitVec digestBits)) =
          liftM ((PairedHashWord.HalfSpec.withLabels StartKey K (BitVec digestBits)).query
            (.inl t)) := by
        rcases t with (n | b) | x <;> rfl
      rw [lifted, simulateQ_spec_query]
      exact G.deferredImpl_run_inl t (s, pending)
    rw [forward, bind_map_left]
    exact bind_congr fun w => ih w.1 w.2

open Classical in
private theorem budget {α : Type} (pp : PublicParam) (body : OracleComp Source α) (q : Nat)
    (s : ResidualCache pp × State K) (w)
    (hw : w ∈ support ((simulateQ (step G pp) (WeightedCap.capCompOpt paidFee q body)).run s)) :
    (inputs w.2.2).encard ≤ (inputs s.2).encard + q := by
  induction body using OracleComp.inductionOn generalizing s q with
  | pure x =>
    simp only [WeightedCap.capCompOpt_pure, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff] at hw
    subst w
    exact le_self_add
  | query_bind t next ih =>
    rw [WeightedCap.capCompOpt_query_bind] at hw
    split_ifs at hw with affordable
    · rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hw
      obtain ⟨y, hy, tail⟩ := hw
      have fee := increase G pp t s hy
      have last := ih y.1 (q - paidFee t) y.2 tail
      calc
        _ ≤ _ := last
        _ ≤ ((inputs s.2).encard + (paidFee t : ℕ∞)) + ((q - paidFee t : Nat) : ℕ∞) :=
          add_le_add fee le_rfl
        _ = _ := by rw [add_assoc, ← Nat.cast_add, Nat.add_sub_of_le affordable]
    · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hw
      subst w
      exact le_self_add

open Classical in
/-- Count each physical byte input once, including aborted and conflicting deferred executions.

The original tariff runs before either half is requested.
-/
theorem deferred_budget {α : Type} (pp : PublicParam) (body : OracleComp Source α) (q : Nat)
    (l : ResidualCache pp) (s t : State K) (past next : List (StartKey ⊕ K))
    (obs : Option α) (extra : ResidualCache pp)
    (run : ((obs, extra), t, next) ∈ support ((simulateQ G.deferredImpl (liftComp
      (residualProgram pp (WeightedCap.capCompOpt paidFee q body) l)
      (PairedHashWord.HalfSpec.withLabels StartKey K (BitVec digestBits)))).run (s, past))) :
    next = past ∧ (inputs t).encard ≤ (inputs s).encard + q := by
  rw [deferred_lift, support_map] at run
  obtain ⟨⟨a, last⟩, supported, same⟩ := run
  cases same
  rw [source_eq, run_step, support_map] at supported
  obtain ⟨⟨result, residual, last⟩, actual, same⟩ := supported
  cases same
  exact ⟨rfl, budget G pp body q (l, s) _ actual⟩

open Classical in
/-- The pre-fill evaluator of the source graph from empty public and label tables. -/
@[expose] noncomputable def coldRun {α : Type} (pp : PublicParam) (body : OracleComp Source α)
    (l : ResidualCache pp) :=
  (simulateQ G.deferredImpl (liftComp (residualProgram pp body l)
    (PairedHashWord.HalfSpec.withLabels StartKey K (BitVec digestBits)))).run ((∅, ∅), [])

open Classical in
private theorem cold_budget {α : Type} (pp : PublicParam) (body : OracleComp Source α) (q : Nat)
    (l : ResidualCache pp) (obs : Option α) (extra : ResidualCache pp)
    (st : State K) (pending : List (StartKey ⊕ K))
    (run : ((obs, extra), st, pending)
      ∈ support (coldRun G pp (WeightedCap.capCompOpt paidFee q body) l)) :
    pending = [] ∧ (inputs st).encard ≤ q := by
  obtain ⟨pendingEq, paid⟩ := deferred_budget G pp body q l (∅, ∅) st [] pending obs extra run
  have cold : inputs ((∅, ∅) : State K) = ∅ := by ext b; simp [inputs]
  rw [cold, Set.encard_empty, zero_add] at paid
  exact ⟨pendingEq, paid⟩

attribute [local irreducible] GraphPrefix.continuation

open Classical in
/-- After the parameter prefix, the remaining budget bounds the number of raw inputs.

The bound includes client aborts and graph conflicts.
-/
theorem actual_deferred (A : Adversary) (left : Nat) (w : HashOutput)
    (obs : Option Outcome) (extra : ResidualCache (GraphPrefix.parameterOfWord w))
    (st : State TwoLayerGraph.Row) (pending : List (StartKey ⊕ TwoLayerGraph.Row))
    (run : let pp := GraphPrefix.parameterOfWord w
      ((obs, extra), st, pending) ∈ support (coldRun (TwoLayerGraph.graph pp) pp
        (WeightedCap.capCompOpt paidFee left (GraphPrefix.continuation A pp))
        (localState _ _ (toKeyedState pp (GraphPrefix.afterWord w))))) :
    pending = [] ∧ (TwoLayerGraph.physicalInputs st.1).encard ≤ left :=
  cold_budget _ _ _ _ _ _ _ _ _ run

end Footprint
end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient
