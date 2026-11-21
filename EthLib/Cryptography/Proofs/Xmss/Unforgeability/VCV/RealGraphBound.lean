module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealGraphPrefix
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealGraphSource

/-!
# The capped forgery game in the graph of the actual public parameter

Key generation spends two calls before its first top-tree query.

The original cap runs before every full-word expansion in the remaining game.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open OracleComp OracleSpec Constants HashSig SecretEncoding.Residual
open scoped ENNReal

local notation "G" w => TwoLayerGraph.graph (parameterOfWord w)

/-- A PRF pair address has a different encoded type from the parameter address. -/
private theorem start_ne_parameter (pp : PublicParam) (k : StartKey) :
    startLabel pp k ≠ parameterLabel := by
  intro same
  have address := congrArg (fun a : PrfInput => a.2.1) same
  change addrPrf k.1 k.2.1 (ChainGraph.pairIndex k.2.2) = addrParam at address
  unfold addrPrf addrParam at address
  exact (by decide : AddressType.prf.code ≠ AddressType.param.code) (encodeAddress_inj.mp address).1

private theorem empty_start (pp : PublicParam) (w : HashOutput) (k : StartKey) :
    (toKeyedState pp (afterWord w)).2 (.inl k) = none := by
  change (RandomOraclePairedValue.splitCache PairedHashWord.halves (afterWord w).2)
    (privateKeyEquiv pp (.inl k)) = none
  rw [privateKeyEquiv_start]
  have emptyEntry : (afterWord w).2 (startLabel pp k) = none :=
      by simp [afterWord, start_ne_parameter]
  by_cases even : k.2.2.val % 2 = 0
  · rw [show taggedStart pp k = Sum.inl (startLabel pp k) from ite_eq_left even]
    exact congrArg (Option.map (fun x => (PairedHashWord.halves x).1)) emptyEntry
  · rw [show taggedStart pp k = Sum.inr (startLabel pp k) from ite_eq_right even]
    exact congrArg (Option.map (fun x => (PairedHashWord.halves x).2)) emptyEntry

/-- Both graph tables begin empty; the prefix tick and both parameter rows stay in local storage. -/
theorem starts_empty (w : HashOutput) :
    baseState _ _ (toKeyedState (parameterOfWord w) (afterWord w)) = (G w).toSplitCache (∅, ∅) := by
  rw [(G w).toSplitCache_empty]
  apply Prod.ext
  · apply QueryCache.ext
    rintro (b | b)
    · change ((afterWord w).1 (.inl b)).map (fun x => (PairedHashWord.halves x).1) = none
      simp [afterWord]
    · change ((afterWord w).1 (.inl b)).map (fun x => (PairedHashWord.halves x).2) = none
      simp [afterWord]
  · exact QueryCache.ext (empty_start (parameterOfWord w) w)

open Classical in
/-- The full graph interpreter from any warm residual and graph tables. -/
@[expose] noncomputable def evaluate {K α : Type} (pp : PublicParam)
    (graph : CanonicalGraph PairedHashWord.HalfSpec StartKey K (BitVec digestBits))
    (body : OracleComp Source α) (extra : ResidualCache pp)
    (st : RelabelState PairedHashWord.HalfSpec StartKey K (BitVec digestBits)) :=
  (simulateQ graph.eagerImpl (liftComp (residualProgram pp body extra)
    (PairedHashWord.HalfSpec.withLabels StartKey K (BitVec digestBits)))).run st

open Classical in
/-- Evaluate the transformed, capped source from empty ordinary and label tables. -/
@[expose] noncomputable def runGraph {K α : Type} (pp : PublicParam)
    (graph : CanonicalGraph PairedHashWord.HalfSpec StartKey K (BitVec digestBits))
    (body : OracleComp Source α) (initial : SourceCache) :=
  evaluate pp graph body (localState _ _ (toKeyedState pp initial)) (∅, ∅)

open Classical in
/-- The candidate, raw replies, cutoff result and complete graph state of a conditional branch. -/
@[expose] noncomputable def graphRun (A : Adversary) (left : Nat) (w : HashOutput) :=
  let pp := parameterOfWord w
  let body := WeightedCap.capCompOpt paidFee left (continuation A pp)
  runGraph pp (G w) body (afterWord w)

attribute [local irreducible] continuation

open Classical in
/-- A common bound on the sampled-parameter graph branches bounds the real keyed forge advantage. -/
theorem forge_le_graph (A : Adversary) (left : Nat) (bound : ℝ≥0∞)
    (bounded : HasHashQueryBound A (left + 2))
    (each : ∀ w : HashOutput, Pr{let z ← graphRun A left w}[
      accepted z.1.1 ∨ (G w).Conflict z.2] ≤ bound) :
    forgeAdvantage A ≤ bound + (left + 2 - 1 : Nat) * (2 ^ 256 : ℝ≥0∞)⁻¹ +
      (left + 2 - 1 : Nat) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  apply (forge_le_paid A _ (by omega) bounded).trans
  refine add_le_add (add_le_add ?_ le_rfl) le_rfl
  apply cold_probability_le
  intro w
  let pp := parameterOfWord w
  let body := WeightedCap.capCompOpt paidFee left (continuation A pp)
  exact (prEvent_source_le_residualGraph (G w) pp body (afterWord w) (∅, ∅)
    (starts_empty w) (G w).labelsComplete_empty (fun z => accepted z.1)).trans (each w)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
