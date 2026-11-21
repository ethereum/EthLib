module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedGameLaw
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedSignature

/-!
# The keyed forgery experiment with hidden internal graph reads

The original adversary can adapt each request to its previous signing replies and hash answers.

Only an accepted forgery contributes on a completed path.

A cutoff keeps every graph conflict that already occurred before refusal.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open HashSig TwoLayerGraph Honest OracleComp OracleSpec SecretEncoding.Residual
open scoped ENNReal

/-- The full adaptive client, both signing layers and the verifier share one physical cutoff. -/
theorem mixed_game (A : Adversary) (w : HashOutput) (left : Nat) :
    let pp := parameterOfWord w
    MixedAt pp left (localState _ _ (toKeyedState pp (afterWord w)))
      (simulateQ (selectedImpl pp) (markedContinuation A pp)) (mixedGame pp A) :=
  mixed_game_at A w left (fun req => actual_mixed_signature _ req.leafIndex req.message)

/-- The deferred game and two seed guesses bound keyed forgery. -/
theorem forge_le_deferred_mixed (A : Adversary) (left : Nat) (bound : ℝ≥0∞)
    (bounded : HasHashQueryBound A (left + 2))
    (each : ∀ w : HashOutput, let pp := parameterOfWord w
      let r := localState _ _ (toKeyedState pp (afterWord w))
      Pr{let z ← (graph pp).deferredFillDraw (pure ()) (guardedGraph left
        ((mixedGame pp A).run r))}[
        accepted (z.1.1.map Prod.fst) ∨ (graph pp).Conflict z.2.1] ≤ bound) :
    forgeAdvantage A ≤ bound + (left + 2 - 1 : Nat) * (2 ^ 256 : ℝ≥0∞)⁻¹ +
      (left + 2 - 1 : Nat) * (2 ^ 256 : ℝ≥0∞)⁻¹ :=
  forge_le_mixed_at A left bound bounded (fun w => mixedGame (parameterOfWord w) A)
    (fun w => mixed_game A w left) each

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
