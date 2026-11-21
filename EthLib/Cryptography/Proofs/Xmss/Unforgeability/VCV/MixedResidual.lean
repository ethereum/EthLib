module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealGraphCalls
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.NormalizedTariff
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealGraphBound

/-!
# Local private draws in a mixed graph schedule

The leanXMSS parameter and randomizer derivations keep their private cache after key generation.

The mixed schedule uses the uniform sampling port only when a local entry is absent.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open Constants HashSig TwoLayerGraph OracleComp OracleSpec SecretEncoding.Residual
open RandomOraclePairedValue
open CanonicalGraph.PairedQueries
open ChainGraph (Public Word)
open scoped Classical

abbrev MixedWorld := Mixed HashInput HashOutput Start Row Word
abbrev MixedLocal (pp : PublicParam) := StateT (ResidualCache pp) (OracleComp MixedWorld)

/-- Both interpretations of an independent local draw use the same underlying sampler. -/
theorem expand_coin {α : Type} (p : ProbComp α) :
    simulateQ (expand PairedHashWord.halves) (liftM p : OracleComp MixedWorld α) =
      liftComp (liftM p : OracleComp ChainWorld α) (Public.withLabels Start Row Word) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp [liftComp]
  | query_bind t k ih =>
    simp only [liftM_bind, simulateQ_bind, liftComp, ih]
    rfl

/-- A tick affects only the local auxiliary table. -/
@[expose] noncomputable def mixedTick (pp : PublicParam) : MixedLocal pp Unit :=
  StateT.mk fun s => (fun z => (z.1, (z.2, s.2))) <$>
    (liftM ((Tick.randomOracle ()).run s.1) : OracleComp MixedWorld _)

/-- The original tick and the mixed local tick retain exactly the same reply and tables. -/
theorem expand_tick (pp : PublicParam) (s : ResidualCache pp) :
    simulateQ (expand PairedHashWord.halves) ((mixedTick pp).run s) =
      liftComp (residualProgram pp sourceTick s) (Public.withLabels Start Row Word) := by
  simp only [mixedTick, StateT.run_mk, simulateQ_map, expand_coin]
  simp [sourceTick, residualProgram, keyedProgram, Derivations.expand,
    SecretEncoding.reindexQueries,
    handler, liftComp]

/-- Query the two residual halves of the same physical PRF input, in source order. -/
@[expose] noncomputable def mixedLocalWord (pp : PublicParam) (key : PrfInput)
    (lo : (Sum.inl key : PrfInput ⊕ PrfInput) ∉ Set.range (taggedStart pp))
    (hi : (Sum.inr key : PrfInput ⊕ PrfInput) ∉ Set.range (taggedStart pp)) :
      MixedLocal pp HashOutput :=
  StateT.mk fun s => do
    let table := (OtherPrivate pp →ₒ Word).randomOracle
    let a ← (liftM ((table ⟨.inl key, lo⟩).run s.2) : OracleComp MixedWorld _)
    let b ← (liftM ((table ⟨.inr key, hi⟩).run a.2) : OracleComp MixedWorld _)
    return (PairedHashWord.halves.symm (a.1, b.1), (s.1, b.2))

/-- Expansion of an off-chain derivation is exact for arbitrary warm or cold local entries. -/
theorem expand_localWord (pp : PublicParam) (key : PrfInput)
    (lo : (Sum.inl key : PrfInput ⊕ PrfInput) ∉ Set.range (taggedStart pp))
    (hi : (Sum.inr key : PrfInput ⊕ PrfInput) ∉ Set.range (taggedStart pp)) (s : ResidualCache pp) :
    simulateQ (expand PairedHashWord.halves) ((mixedLocalWord pp key lo hi).run s) =
      liftComp (residualProgram pp (liftM (Source.query (.inr key))) s)
        (Public.withLabels Start Row Word) := by
  rw [residual_other pp key lo hi s]
  simp only [mixedLocalWord, StateT.run_mk, simulateQ_bind, simulateQ_pure, expand_coin, liftComp]

/-- Neither tagged half of the parameter word names a chain start at any public parameter. -/
theorem parameter_local (pp : PublicParam) :
    (Sum.inl parameterLabel : PrfInput ⊕ PrfInput) ∉ Set.range (taggedStart pp) ∧
      (Sum.inr parameterLabel : PrfInput ⊕ PrfInput) ∉ Set.range (taggedStart pp) := by
  have label (k : StartKey) : (taggedStart pp k).elim id id = startLabel pp k := by
    unfold taggedStart
    split <;> rfl
  constructor <;> rintro ⟨k,
    eq⟩ <;> exact start_ne_parameter pp k ((label k).symm.trans (congrArg (Sum.elim id id) eq))

/-- An already populated pair returns the original full word and makes no request. -/
theorem mixedLocalWord_hit (pp : PublicParam) (key : PrfInput)
    (lo : (Sum.inl key : PrfInput ⊕ PrfInput) ∉ Set.range (taggedStart pp))
    (hi : (Sum.inr key : PrfInput ⊕ PrfInput) ∉ Set.range (taggedStart pp))
    (s : ResidualCache pp) (w : HashOutput)
    (hl : s.2 ⟨.inl key, lo⟩ = some (PairedHashWord.halves w).1)
    (hh : s.2 ⟨.inr key, hi⟩ = some (PairedHashWord.halves w).2) :
    ((mixedLocalWord pp key lo hi).run s) = pure (w, s) := by
  simp [mixedLocalWord, hl, hh]

/-- Every extension of the conditioned local table replays the chosen parameter.

The auxiliary table may have arbitrary contents. -/
theorem mixedParameter_hit (w : HashOutput) (s : ResidualCache (parameterOfWord w))
    (prior : (localState _ _ (toKeyedState (parameterOfWord w) (afterWord w))).2 ≤ s.2) :
    let pp := parameterOfWord w
    ((mixedLocalWord pp parameterLabel (parameter_local pp).1 (parameter_local pp).2).run s) =
      pure (w, s) := by
  intro pp
  apply mixedLocalWord_hit
  · apply prior
    change (toKeyedState pp (afterWord w)).2 (.inr _) = _
    rw [toKeyedState_other]
    simp [splitCache, afterWord]
  · apply prior
    change (toKeyedState pp (afterWord w)).2 (.inr _) = _
    rw [toKeyedState_other]
    simp [splitCache, afterWord]

/-- The byte-oriented scheme callback for either layer's physical randomizer query. -/
@[expose] noncomputable def mixedRandomizer (pp : PublicParam) (l : Layer)
    (e : UInt32) (msg : ByteArray) :
    MixedLocal pp (Vector UInt8 32) :=
  ofOutput <$> mixedLocalWord pp (pp, addrRnd l e, msg)
    (randomizer_residual pp l e msg).1 (randomizer_residual pp l e msg).2

theorem expand_randomizer (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (s : ResidualCache pp) :
    simulateQ (expand PairedHashWord.halves) ((mixedRandomizer pp l e msg).run s) =
      liftComp (residualProgram pp (sourcePrf pp (addrRnd l e) msg) s)
        (Public.withLabels Start Row Word) := by
  simp only [mixedRandomizer, StateT.run_map, simulateQ_map, expand_localWord, sourcePrf]
  simp [residualProgram, keyedProgram, liftComp]

private theorem coin_support {α : Type} (p : ProbComp α) {u : α}
    (h : u ∈ support (liftM p : OracleComp MixedWorld α)) : u ∈ support p := by
  induction p using OracleComp.inductionOn with
  | pure a => simpa only [liftM_pure, mem_support_pure_iff] using h
  | query_bind n k ih =>
    rw [liftM_bind, mem_support_bind_iff] at h
    obtain ⟨v, _, next⟩ := h
    rw [mem_support_bind_iff]
    exact ⟨v, by simp, ih v next⟩

/-- Local private sampling only extends the table, including on two cold misses. -/
theorem mixedLocalWord_extends (pp : PublicParam) (key : PrfInput)
    (lo : (Sum.inl key : PrfInput ⊕ PrfInput) ∉ Set.range (taggedStart pp))
    (hi : (Sum.inr key : PrfInput ⊕ PrfInput) ∉ Set.range (taggedStart pp))
    (s : ResidualCache pp) {z}
    (run : z ∈ support ((mixedLocalWord pp key lo hi).run s)) : s.2 ≤ z.2.2 := by
  simp only [mixedLocalWord, StateT.run_mk, mem_support_bind_iff, mem_support_pure_iff] at run
  obtain ⟨a, ha, b, hb, rfl⟩ := run
  have first := coin_support
    (((OtherPrivate pp →ₒ Word).randomOracle ⟨.inl key, lo⟩).run s.2) ha
  have second := coin_support
    (((OtherPrivate pp →ₒ Word).randomOracle ⟨.inr key, hi⟩).run a.2) hb
  exact (QueryImpl.withCaching_cache_le uniformSampleImpl _ _ _ first).trans
    (QueryImpl.withCaching_cache_le uniformSampleImpl _ _ _ second)

/-- A tick cannot modify the private parameter or randomizer entries. -/
theorem mixedTick_private (pp : PublicParam) (s : ResidualCache pp) {z}
    (run : z ∈ support ((mixedTick pp).run s)) : z.2.2 = s.2 := by
  simp only [mixedTick, StateT.run_mk, support_map] at run
  obtain ⟨_, _, rfl⟩ := run
  rfl

/-- Sampling from the private local tables consumes no physical hash fee. -/
theorem mixedCoin_free {α : Type} (p : ProbComp α) :
    (liftM p : OracleComp MixedWorld α).AllQueriesSatisfy
      (fun t => mixedCost (H := Word) (F := HashOutput) (fun _ => 0) t = 0) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftM_bind]
    apply allQueriesSatisfy_bind _ ih
    change AllQueriesSatisfy (liftM (MixedWorld.query (.inl (.inl t))) : OracleComp MixedWorld _) _
    exact (allQueriesSatisfy_query_iff _ _).2 rfl

/-- The tick's cache read and any miss are free in the selected graph tariff. -/
theorem mixedTick_free (pp : PublicParam) (s : ResidualCache pp) :
    ((mixedTick pp).run s).AllQueriesSatisfy
      (fun t => mixedCost (H := Word) (F := HashOutput) (fun _ => 0) t = 0) := by
  simp only [mixedTick, StateT.run_mk, ← bind_pure_comp]
  exact allQueriesSatisfy_bind (mixedCoin_free _) fun _ => allQueriesSatisfy_pure _ _

/-- Both halves remain free even when the local derivation cache is cold. -/
theorem mixedLocalWord_free (pp : PublicParam) (key : PrfInput)
    (lo : (Sum.inl key : PrfInput ⊕ PrfInput) ∉ Set.range (taggedStart pp))
    (hi : (Sum.inr key : PrfInput ⊕ PrfInput) ∉ Set.range (taggedStart pp)) (s : ResidualCache pp) :
    ((mixedLocalWord pp key lo hi).run s).AllQueriesSatisfy
      (fun t => mixedCost (H := Word) (F := HashOutput) (fun _ => 0) t = 0) := by
  exact allQueriesSatisfy_bind (mixedCoin_free _) fun _ =>
    allQueriesSatisfy_bind (mixedCoin_free _) fun _ => allQueriesSatisfy_pure _ _

/-- A physical randomizer query may draw twice but charges no public input. -/
theorem mixedRandomizer_free (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (s : ResidualCache pp) : ((mixedRandomizer pp l e msg).run s).AllQueriesSatisfy
      (fun t => mixedCost (H := Word) (F := HashOutput) (fun _ => 0) t = 0) := by
  rw [mixedRandomizer, StateT.run_map, ← bind_pure_comp]
  exact allQueriesSatisfy_bind (mixedLocalWord_free ..) fun _ => allQueriesSatisfy_pure _ _

/-- Every randomizer lookup preserves the conditioned parameter in its returned private state. -/
theorem mixedRandomizer_extends (pp : PublicParam) (l : Layer) (e : UInt32)
    (msg : ByteArray) (s : ResidualCache pp) {z}
    (run : z ∈ support ((mixedRandomizer pp l e msg).run s)) : s.2 ≤ z.2.2 := by
  rw [mixedRandomizer, StateT.run_map, support_map] at run
  obtain ⟨_, seen, rfl⟩ := run
  exact mixedLocalWord_extends pp _ _ _ s seen

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
