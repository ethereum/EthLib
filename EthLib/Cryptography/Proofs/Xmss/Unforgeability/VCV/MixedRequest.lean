module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedParameter
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.SigningSource

/-!
# One request at its genuinely sampled parameter

The tick and private parameter read happen before the source signer is invoked.

Its failure is logged as a raw error and the optional client receives no signature.

The mixed signer already knows the parameter from the same warm private row.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants TwoLayerGraph Honest OracleComp OracleSpec

@[expose] noncomputable def mixedRequest (pp : PublicParam) (r : SignRequest)
    (sign : MixedLocal pp (Except XmssError Signature)) :
      MixedLocal pp (Option Signature × RawLog) := do
  let _ ← mixedTick pp
  let _ ← mixedParameter pp
  let ans ← sign
  return (ans.toOption, [(r, ans)])

attribute [local irreducible] signDerived simulateQ mixedParameter mixedTick hashOf mark
attribute [local irreducible] selectedImpl graphPrf

/-- Discharge the native signer's parameter check using the actually reached residual state. -/
theorem request_at (w : HashOutput) (req : SignRequest)
    (sign : MixedLocal (parameterOfWord w) (Except XmssError Signature))
    (correct : let pp := parameterOfWord w
      SameMixed pp (simulateQ (selectedImpl pp) (simulateQ (mark IsTrial)
        (signDerived (hashOf sourcePass) sourcePrf pp req.leafIndex req.message))) sign)
    (q : Nat) (s : ResidualCache (parameterOfWord w)) (conditioned : Warm w s) :
    let pp := parameterOfWord w
    MixedAt pp q s (simulateQ (selectedImpl pp) (markedSigner (.inr req)).run)
      (mixedRequest pp req sign) := by
  let pp := parameterOfWord w
  change MixedAt pp q s _ _
  unfold markedSigner signerOf failSignerOf mixedRequest
  simp only [WriterT.run_mk, simulateQ_bind, simulateQ_pure, map_bind, map_pure]
  apply mixed_bind_at q s (marked_tick pp q s)
  intro seed next tickRun left
  have privateEq := mixedTick_private pp s tickRun
  have eqPrivate : next.2 = s.2 := privateEq
  have warm : Warm w next := by
    unfold Warm
    rw [eqPrivate]
    exact conditioned
  apply mixed_bind_at left next (selected_parameter pp left next)
  intro drawn state drawRun remain
  rw [parameter_warm w next warm, mem_support_pure_iff] at drawRun
  have eqDraw : drawn = pp := congrArg Prod.fst drawRun
  have eqState : state = next := congrArg Prod.snd drawRun
  subst drawn state
  exact (correct.bind (f := fun ans => pure (ans.toOption, [(req,ans)]))
    (g := fun ans => pure (ans.toOption, [(req,ans)])) (fun ans => SameMixed.pure _)) remain next

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
