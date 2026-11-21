module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealGraphKeys
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerGraph
public import VCVio.OracleComp.QueryTracking.RandomOracle.Relabel
public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed.Residual

/-!
# The signing experiment over private chain starts

Each tick and each private half outside the selected chain starts has its own local random table.

The external ideal game sees the physical public hash halves and the private chain starts.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient

open OracleComp OracleSpec HashSig SecretEncoding.Residual
open RandomOraclePairedValue

abbrev SourceCache := SecretEncoding.SplitCache Backend PrfInput HashOutput
abbrev KeyedCache (pp : PublicParam) :=
  SecretEncoding.SplitCache KeyBackend (StartKey ⊕ OtherPrivate pp) (BitVec digestBits)

/--
Split full public and private reads before assigning a chain label to each selected private half.
-/
@[expose] noncomputable def keyedProgram {α : Type} (pp : PublicParam)
    (body : OracleComp Source α) :=
  simulateQ (SecretEncoding.reindexQueries KeyBackend (privateKeyEquiv pp).symm)
    (simulateQ (Derivations.expand Tick PairedHashWord.halves) body)

abbrev ChainWorld := PairedHashWord.HalfSpec.withDerivations StartKey (BitVec digestBits)
abbrev ChainCache := SecretEncoding.SplitCache PairedHashWord.HalfSpec StartKey (BitVec digestBits)
abbrev ResidualCache (pp : PublicParam) := Local Tick (OtherPrivate pp) (BitVec digestBits)

open Classical in
/-- Run the original caller while retaining the auxiliary and residual caches. -/
@[expose] noncomputable def residualProgram {α : Type} (pp : PublicParam)
    (body : OracleComp Source α) (start : ResidualCache pp) :
    OracleComp ChainWorld (α × ResidualCache pp) :=
  (simulateQ (handler (pub := PairedHashWord.HalfSpec) (aux := Tick)
    (X := StartKey) (Z := OtherPrivate pp) (R :=
      BitVec digestBits)) (keyedProgram pp body)).run start

open Classical in
/-- The distribution of the observation and all four final tables agrees with the full-word game. -/
theorem residualProgram_joint {α : Type} (pp : PublicParam) (body : OracleComp Source α)
    (initial : SourceCache) :
    (fun w => ((w.1, localState _ _ (toKeyedState pp w.2)),
      baseState _ _ (toKeyedState pp w.2))) <$>
      (simulateQ (SecretEncoding.idealImpl Backend PrfInput HashOutput) body).run initial =ᵈ
    (simulateQ (SecretEncoding.idealImpl PairedHashWord.HalfSpec StartKey (BitVec digestBits))
      (residualProgram pp body (localState _ _ (toKeyedState pp initial)))).run
        (baseState _ _ (toKeyedState pp initial)) := by
  classical
  unfold residualProgram
  rw [SecretEncoding.Residual.run]
  have transported := (program_keyed_joint pp body initial).map
    (fun z => ((z.1, localState _ _ z.2.2), baseState _ _ z.2.2))
  simpa only [Functor.map_map, keyedProgram] using transported

open Classical in
/-- Every output of the chain-start game comes from an actual full-word signing run.

Its observation, both external tables, and both residual tables are retained.
-/
theorem residualProgram_source {α : Type} (pp : PublicParam) (body : OracleComp Source α)
    (initial : SourceCache)
    (obs : α) (t : ResidualCache pp) (b : ChainCache)
    (supported : ((obs, t), b) ∈ support ((simulateQ
      (SecretEncoding.idealImpl PairedHashWord.HalfSpec
      StartKey (BitVec digestBits)) (residualProgram pp body (localState _ _
        (toKeyedState pp initial)))).run
        (baseState _ _ (toKeyedState pp initial)))) :
    ∃ full : SourceCache, (obs, full) ∈ support
      ((simulateQ (SecretEncoding.idealImpl Backend PrfInput HashOutput) body).run initial) ∧
      t = localState _ _ (toKeyedState pp full) ∧ b = baseState _ _ (toKeyedState pp full) := by
  classical
  unfold residualProgram at supported
  rw [SecretEncoding.Residual.run] at supported
  rw [support_map] at supported
  obtain ⟨⟨out, keyed⟩, keyedRun, same⟩ := supported
  have obsEq : out = obs := congrArg (fun w => w.1.1) same
  subst out
  have h := support_eq_of_evalDistEq (program_keyed_joint pp body initial)
  simp only [support_map] at h
  let joined := Derivations.joinState Tick PairedHashWord.halves
    (SecretEncoding.reindexState KeyBackend (privateKeyEquiv pp) keyed)
  obtain ⟨⟨result, full⟩, actual, eq⟩ := (Set.ext_iff.mp h (obs, joined, keyed)).2
    ⟨(obs, keyed), keyedRun, rfl⟩
  have resultEq : result = obs := congrArg Prod.fst eq
  have keyedEq : toKeyedState pp full = keyed := congrArg (fun w => w.2.2) eq
  subst result keyed
  exact ⟨full, actual, (congrArg (fun w => w.1.2) same).symm, (congrArg Prod.snd same).symm⟩

variable {K : Type} (G : CanonicalGraph PairedHashWord.HalfSpec StartKey K (BitVec digestBits))

/-- Reconstruct both full-word source tables from all four halves retained by the simulation. -/
noncomputable def recoverFull (pp : PublicParam) (extra : ResidualCache pp) (base : ChainCache) :
    SourceCache :=
  let keyed : KeyedCache pp := (QueryCache.addEquiv _ _ (base.1, extra.1),
    .ofFn (fun k : StartKey ⊕ OtherPrivate pp =>
      Sum.elim (fun x : StartKey => (base.2 x : Option (BitVec digestBits))) (fun z =>
        extra.2 z) k))
  RandomOraclePairedValue.Derivations.joinState Tick PairedHashWord.halves
    (SecretEncoding.reindexState KeyBackend (privateKeyEquiv pp) keyed)

/-- Restoring the projections of an actual full-word table keeps every entry. -/
theorem recoverFull_source (pp : PublicParam) (s : SourceCache) :
    recoverFull pp (localState _ _ (toKeyedState pp s)) (baseState _ _ (toKeyedState pp s))
      = s := by
  have reassemble (c : KeyedCache pp) :
      (QueryCache.addEquiv _ _ (c.1.fst, c.1.snd),
        QueryCache.ofFn (fun k : StartKey ⊕ OtherPrivate pp =>
          Sum.elim (fun x : StartKey => (c.2 (.inl x) : Option (BitVec digestBits)))
            (fun z => c.2 (.inr z)) k)) = c := by
    apply Prod.ext
    · exact (QueryCache.addEquiv _ _).apply_symm_apply _
    · apply QueryCache.ext
      rintro (k | z) <;> rfl
  unfold recoverFull baseState localState
  dsimp only [QueryCache.ofFn_apply]
  rw [reassemble (toKeyedState pp s)]
  unfold toKeyedState
  let e := PairedHashWord.halves
  let aux := Tick
  exact (congrArg (RandomOraclePairedValue.Derivations.joinState aux e)
    (SecretEncoding.reindexState_symm KeyBackend (privateKeyEquiv pp).symm
      (RandomOraclePairedValue.Derivations.splitState aux e s))).trans
        (RandomOraclePairedValue.Derivations.join_split aux e s)

open Classical in
/-- Start the graph and the ideal game with the same warm tables.

Every supported conflict-free graph run has the same result and merged tables in the ideal game.
-/
theorem graphEndpoint {α : Type} (body : OracleComp ChainWorld α)
    (s t : RelabelState PairedHashWord.HalfSpec StartKey K (BitVec digestBits)) (a : α)
    (complete : G.LabelsComplete s)
    (actual : (a, t) ∈ support ((simulateQ G.eagerImpl
      (liftComp body (PairedHashWord.HalfSpec.withLabels StartKey K (BitVec digestBits)))).run s))
    (consistent : ¬G.Conflict t) :
    (a, G.toSplitCache t) ∈ support ((simulateQ
      (SecretEncoding.idealImpl PairedHashWord.HalfSpec StartKey (BitVec digestBits)) body).run
      (G.toSplitCache s)) := by
  classical
  rw [G.simulateQ_eagerImpl_liftComp] at actual
  let event (z : α × ChainCache) := z = (a, G.toSplitCache t)
  have bound := G.prEvent_relabelImpl_and_not_conflict_le_of_labelsComplete body complete event
  have pos : 0 < Pr{let z ← (simulateQ G.relabelImpl body).run s}[
      event (z.1, G.toSplitCache z.2) ∧ ¬G.Conflict z.2] :=
    (prEvent_pos_iff _ _).2 ⟨(a, t), actual, rfl, consistent⟩
  obtain ⟨endpoint, supported, same⟩ := (prEvent_pos_iff _ _).1 (lt_of_lt_of_le pos bound)
  change endpoint = (a, G.toSplitCache t) at same
  exact same ▸ supported

open Classical in
/-- The adaptive signing game supplies the full-word source state of the conflict-free graph run.

It also supplies the merged public table and every indexed private start.
-/
theorem residualProgram_eager_source {α : Type} (pp : PublicParam) (body : OracleComp Source α)
    (initial : SourceCache)
    (s t : RelabelState PairedHashWord.HalfSpec StartKey K (BitVec digestBits))
    (obs : α) (extra : ResidualCache pp)
    (initialTables : baseState _ _ (toKeyedState pp initial) = G.toSplitCache s)
    (complete : G.LabelsComplete s)
    (actual : ((obs, extra), t) ∈ support ((simulateQ G.eagerImpl (liftComp
      (residualProgram pp body (localState _ _ (toKeyedState pp initial)))
      (PairedHashWord.HalfSpec.withLabels StartKey K (BitVec digestBits)))).run s))
    (consistent : ¬G.Conflict t) :
    ∃ full : SourceCache,
      (obs, full) ∈ support ((simulateQ (SecretEncoding.idealImpl Backend PrfInput HashOutput)
        body).run initial) ∧
      extra = localState _ _ (toKeyedState pp full) ∧
      G.toSplitCache t = baseState _ _ (toKeyedState pp full) := by
  classical
  have reached := graphEndpoint G _ s t _ complete actual consistent
  rw [← initialTables] at reached
  exact residualProgram_source pp body initial obs extra _ reached

open Classical in
/-- Bound any event of the original observation and both full source tables in the graph game.

The extra event is exactly the canonical graph conflict.
-/
theorem prEvent_source_le_residualGraph {α : Type} (pp : PublicParam) (body : OracleComp Source α)
    (initial : SourceCache)
    (s : RelabelState PairedHashWord.HalfSpec StartKey K (BitVec digestBits))
    (initialTables : baseState _ _ (toKeyedState pp initial) = G.toSplitCache s)
    (complete : G.LabelsComplete s)
    (P : α × SourceCache → Prop) :
    Pr{let z ← (simulateQ
      (SecretEncoding.idealImpl Backend PrfInput HashOutput) body).run initial}[P z] ≤
    Pr{let z ← (simulateQ G.eagerImpl (liftComp
      (residualProgram pp body (localState _ _ (toKeyedState pp initial)))
      (PairedHashWord.HalfSpec.withLabels StartKey K (BitVec digestBits)))).run s}[
      P (z.1.1, recoverFull pp z.1.2 (G.toSplitCache z.2)) ∨ G.Conflict z.2] := by
  classical
  let Q (z : (α × ResidualCache pp) × ChainCache) :=
    P (z.1.1, recoverFull pp z.1.2 z.2)
  have coupled := (residualProgram_joint pp body initial).prEvent_eq Q
  rw [initialTables] at coupled
  have bound := G.prEvent_idealImpl_le_relabelImpl_of_labelsComplete
    (residualProgram pp body (localState _ _ (toKeyedState pp initial))) complete Q
  rw [G.simulateQ_eagerImpl_liftComp]
  apply le_trans _ bound
  rw [← coupled]
  simp [prEvent_norm, Q, recoverFull_source]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient
