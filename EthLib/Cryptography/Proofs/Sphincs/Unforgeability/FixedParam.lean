module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.SkipGame
import VCVio.EvalDist.ProbabilityBounds

/-!
# Proofs: the game with the public parameter fixed, and its canonical graph

Key generation first derives the public parameter `P`, as two halves.

`P` is half 0, and half 1 is never read.

So the game draws the two halves, then runs the rest of the experiment.

The canonical graph is the one of the keys with parameter `P`.

From the state that holds the two halves, VCVio's canonical relabelling applies to that graph.

There, every honest tweakable hash at a point of the graph reads the label of its node.

A forgery in the game is then at most a forgery in the relabelled game, or a conflict.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability

open EthLib.Cryptography.Sphincs.Constants
open EthLib.Cryptography.HashSig (ofOutput)
open OracleSpec OracleComp

/-! ## The experiment after the public parameter -/

/-- The derivation of the public parameter `P`. -/
def paramInput : DerivationInput :=
  ⟨(Vector.replicate PUBLIC_PARAM_LEN 0, addrParam, .empty), isDerivationAddress_addrParam⟩

/-- `H` in the game where the scheme skips the halves it throws away. -/
noncomputable def skipH (x : ByteArray) : OracleComp HalvedWorld (Vector UInt8 32) :=
  simulateQ skipHalves (liftH DerivationInput x)

/-- The derivations in that game, each asked half by half. -/
noncomputable def skipPrf : SeedPrf (OracleComp HalvedWorld) :=
  mapPrf (simulateQ skipHalves) derivationPrf

/-- In that game, a derivation asks its two halves and joins them. -/
theorem skipHalves_inr (x : DerivationInput) :
    skipHalves (.inr x) = (do
      let u ← HalvedWorld.query (.inr (x, 0))
      let v ← HalvedWorld.query (.inr (x, 1))
      return hashHalves.symm (u, v)) := by
  simp [QueryImpl.apply_compose, ghostHalves, skipGhost]

/-- A digest read as a public parameter: both are 16 bytes. -/
def paramOf (u : Digest) : PublicParam :=
  u

/-- The public parameter of the derivation joined from two halves is the first half. -/
theorem halfOf_zero_outputOf_hashHalves_symm (u v : Digest) :
    (halfOf 0 (outputOf (hashHalves.symm (u, v))) : PublicParam) = paramOf u :=
  halfOf_zero_hashHalves_symm u v

/-- In that game, the public parameter is the first of two drawn halves. -/
theorem publicParamOf_skipPrf : publicParamOf skipPrf = (do
    let u ← HalvedWorld.query (.inr (paramInput, 0))
    let _ ← HalvedWorld.query (.inr (paramInput, 1))
    return paramOf u) := by
  simp only [publicParamOf, skipPrf, mapPrf, derivationPrf, isDerivationAddress_addrParam,
    ↓reduceDIte, simulateQ_map, simulateQ_spec_query, skipHalves_inr, map_bind, bind_assoc,
    map_pure, pure_bind, halfOf_zero_outputOf_hashHalves_symm]
  rfl

/-- The experiment after the public parameter `P`: the top tree's root, the adversary, the check. -/
noncomputable def restExperiment (adversary : Adversary) (P : PublicParam) :
    OracleComp HalvedWorld
      (SignatureAlg.UnforgeableTranscript Message PublicKey Unit (Option Signature)) := do
  let root ← treeRoot skipH P skipPrf .top 0
  let pk : PublicKey := { root, publicParam := P }
  let ((msg, σ), log) ← skipScheme.runWithSigningOracle pk ()
    ((halvedAdversary adversary).main pk)
  let verified ← skipScheme.verify pk msg σ
  return ⟨pk, (), log, msg, σ, verified⟩

/-- The experiment of the scheme that skips the thrown-away halves.

It derives `P`, then runs the rest. -/
theorem skipExperiment_eq (adversary : Adversary) :
    SignatureAlg.unforgeableTranscriptExperiment
        (⟨(halvedAdversary adversary).main⟩ : SignatureAlg.UnforgeableAdversary skipScheme) =
      publicParamOf skipPrf >>= restExperiment adversary := by
  rw [SignatureAlg.unforgeableTranscriptExperiment_def, skipScheme, SignatureAlg.map_keygen]
  dsimp only [hiddenSeedScheme]
  rw [simulateQ_bind, publicKeyOf_map_monad (simulateQ skipHalves)
    (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f)]
  simp only [publicKeyOf, simulateQ_pure, bind_assoc, pure_bind]
  rfl

/-! ## The state that holds the public parameter -/

/-- Cells of the graph are compared cell by cell: a derivation half, or a node.

Instance search does not find this one by itself. -/
instance : DecidableEq Cell :=
  instDecidableEqSum

/-- The relabelled state with the two halves of `P` drawn and nothing else. -/
noncomputable def paramState (u v : Digest) :
    RelabelState (List UInt8 × Fin 2 →ₒ Digest) (DerivationInput × Fin 2) Node Digest :=
  (∅, ((∅ : (Cell →ₒ Digest).QueryCache).cacheQuery
    (.inl (paramInput, 0)) u).cacheQuery (.inl (paramInput, 1)) v)

/-- No label is drawn in that state. -/
theorem paramState_inr (u v : Digest) (k : Node) : (paramState u v).2 (.inr k) = none := by
  simp only [paramState]
  rw [QueryCache.cacheQuery_of_ne _ _ (by simp), QueryCache.cacheQuery_of_ne _ _ (by simp)]
  rfl

/-- In that state, every drawn label belongs to a node whose children are drawn. -/
theorem labelsComplete_paramState (P : PublicParam) (u v : Digest) :
    (graph P).LabelsComplete (paramState u v) := fun k hk => by
  rw [paramState_inr] at hk
  exact absurd hk (by simp)

/-- That state stands for the empty public cache and the table of the two halves. -/
theorem toSplitCache_paramState (P : PublicParam) (u v : Digest) :
    (graph P).toSplitCache (paramState u v) =
      (∅, ((∅ : ((DerivationInput × Fin 2) →ₒ Digest).QueryCache).cacheQuery (paramInput, 0)
        u).cacheQuery (paramInput, 1) v) := by
  refine Prod.ext (QueryCache.ext fun t => ?_) ?_
  · change (graph P).merge (paramState u v) t = none
    by_cases ht : ∃ k vs, (graph P).childVals (paramState u v) k = some vs ∧ (graph P).pt k vs = t
    · obtain ⟨k, vs, hk, rfl⟩ := ht
      rw [(graph P).merge_apply_pt hk, paramState_inr, Option.map_none]
    · rw [(graph P).merge_apply_of_not_exists ht]
      rfl
  · change RelabelState.table (paramState u v) = _
    rw [paramState, RelabelState.table_cacheQuery_inl, RelabelState.table_cacheQuery_inl,
      RelabelState.table_empty]

/-! ## The relabelled game with the public parameter fixed -/

/-- Events after a common draw compare as they compare for each drawn value. -/
theorem prEvent_bind_le_bind {α : Type} (mx : ProbComp α) (f g : α → ProbComp Prop)
    (h : ∀ a, prEvent (f a) ≤ prEvent (g a)) : prEvent (mx >>= f) ≤ prEvent (mx >>= g) := by
  have := prEvent_bind_mono_of_forall_le mx f g id id fun a => by simpa [prEvent_norm] using h a
  simpa [prEvent_norm] using this

/-- The game where the scheme skips the thrown-away halves draws the two halves of `P` first.

An event of the output has the chance it has after those draws, from the table that holds them. -/
theorem prEvent_skip_eq (adversary : Adversary) (E : SignatureAlg.UnforgeableTranscript Message
    PublicKey Unit (Option Signature) → Prop) :
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl (List UInt8 × Fin 2 →ₒ Digest)
        (DerivationInput × Fin 2) Digest) (SignatureAlg.unforgeableTranscriptExperiment
          (⟨(halvedAdversary adversary).main⟩ : SignatureAlg.UnforgeableAdversary skipScheme))).run
          (∅, ∅)}[E z.1] =
      Pr{let u ← $ᵗ Digest
         let v ← $ᵗ Digest
         let z ← (simulateQ (SecretEncoding.idealImpl (List UInt8 × Fin 2 →ₒ Digest)
           (DerivationInput × Fin 2) Digest) (restExperiment adversary (paramOf u))).run
           (∅, ((∅ : ((DerivationInput × Fin 2) →ₒ Digest).QueryCache).cacheQuery (paramInput, 0)
             u).cacheQuery (paramInput, 1) v)}[E z.1] := by
  rw [skipExperiment_eq, publicParamOf_skipPrf]
  have h1 : ((∅ : ((DerivationInput × Fin 2) →ₒ Digest).QueryCache) (paramInput, 0)) = none := rfl
  have h2 : ∀ u, (((∅ : ((DerivationInput × Fin 2) →ₒ Digest).QueryCache).cacheQuery
      (paramInput, 0) u) (paramInput, 1)) = none := fun _ =>
    (QueryCache.cacheQuery_of_ne _ _ (by simp)).trans rfl
  simp only [bind_assoc, pure_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    idealImpl_run_derive_none' h1,
    idealImpl_run_derive_none' (h2 _), bind_map_left]
  simp only [prEvent_norm]

/-- **The relabelled game with the public parameter fixed.**

The forging advantage is at most a forgery or a conflict in the relabelled game.

That game draws the two halves of `P`, then relabels the graph of `P` from the state holding them.

The two seed hops add `qH / 2^256` each. -/
theorem forgeAdvantage_le_relabel (adversary : Adversary) {qH qS : Nat}
    (hadversary : adversary.RomQueryBound qH qS) :
    forgeAdvantage adversary ≤
      Pr{let u ← $ᵗ Digest
         let v ← $ᵗ Digest
         let z ← (simulateQ (graph (paramOf u)).relabelImpl
           (restExperiment adversary (paramOf u))).run
           (paramState u v)}[z.1.strongWins = true ∨ (graph (paramOf u)).Conflict z.2] +
        qH * ((2 : ENNReal) ^ 256)⁻¹ + qH * ((2 : ENNReal) ^ 256)⁻¹ := by
  refine (forgeAdvantage_le_halved adversary hadversary).trans ?_
  gcongr ?_ + _ + _
  rw [prEvent_halved_eq_skip, prEvent_skip_eq adversary fun t => t.strongWins = true]
  refine prEvent_bind_le_bind _ _ _ fun u => prEvent_bind_le_bind _ _ _ fun v => ?_
  have h := (graph (paramOf u)).prEvent_idealImpl_le_relabelImpl_of_labelsComplete
    (restExperiment adversary (paramOf u)) (labelsComplete_paramState _ u v)
    fun z => z.1.strongWins = true
  rwa [toSplitCache_paramState] at h

end EthLib.Cryptography.Sphincs.Unforgeability
