module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedFree
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SelectedCalls
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedClient

/-!
# Reusing the sampled parameter at every signing request

Both halves of the parameter word already occupy the local derivation table.

Private draws can extend that table without changing either half.

The client therefore always enters the signer for its actual sampled parameter.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography Constants HashSig OracleComp OracleSpec TwoLayerGraph Honest
open SecretEncoding.Residual
open CanonicalGraph.PairedQueries

@[expose] noncomputable def mixedParameter (pp : PublicParam) : MixedLocal pp PublicParam :=
  parameterOfWord <$> mixedLocalWord pp parameterLabel (parameter_local pp).1 (parameter_local pp).2

/-- A signing request reads the true cached parameter from the private, uncharged port. -/
theorem selected_parameter (pp : PublicParam) :
    SameMixed pp (simulateQ (selectedImpl pp) (simulateQ (mark IsTrial) (publicParamOf sourcePrf)))
      (mixedParameter pp) := by
  let query : OracleComp Source HashOutput := liftM (Source.query (.inr parameterLabel))
  have read : publicParamOf sourcePrf = parameterOfWord <$> query := by
    simp only [publicParamOf, sourcePrf, bind_pure_comp]
    rfl
  have base : SameMixed pp (liftM (inGraph pp query))
      (mixedLocalWord pp parameterLabel (parameter_local pp).1 (parameter_local pp).2) := by
    apply mixed_free pp _ _ (fun r => mixedLocalWord_free pp parameterLabel _ _ r)
    intro r
    exact congrArg (simulateQ (graph pp).eagerImpl) (expand_localWord pp parameterLabel _ _ r).symm
  have marked : simulateQ (selectedImpl pp) (simulateQ (mark IsTrial) query) =
      (liftM (inGraph pp query) : Selected pp _) := by
    simp only [query, simulateQ_spec_query, mark, selected_original]
  rw [read, simulateQ_map, simulateQ_map, marked, mixedParameter]
  simp only [← bind_pure_comp]
  exact base.bind fun x => SameMixed.pure _

@[expose] def Warm (w : HashOutput) (s : ResidualCache (parameterOfWord w)) :=
  (localState _ _ (toKeyedState (parameterOfWord w) (afterWord w))).2 ≤ s.2

/-- The original selected parameter word is a hit and leaves both caches untouched. -/
theorem parameter_warm (w : HashOutput) (s : ResidualCache (parameterOfWord w)) (warm : Warm w s) :
    (mixedParameter (parameterOfWord w)).run s = pure (parameterOfWord w, s) := by
  simp only [mixedParameter, StateT.run_map, mixedParameter_hit w s warm, map_pure]

/-- Phase tagging cannot charge the private source tick. -/
theorem marked_tick (pp : PublicParam) :
    SameMixed pp (simulateQ (selectedImpl pp) (simulateQ (mark IsTrial) sourceTick))
      (mixedTick pp) := by
  have eq : simulateQ (selectedImpl pp) (simulateQ (mark IsTrial) sourceTick) =
      (liftM (inGraph pp sourceTick) : Selected pp _) := by
    simp only [sourceTick, simulateQ_spec_query, mark, selected_original]
  rw [eq]
  exact selected_mixed_tick pp

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
