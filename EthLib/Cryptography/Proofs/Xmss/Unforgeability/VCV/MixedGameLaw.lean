module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedGameProgram
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedCacheGrowth
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedStructureCalls
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.GuardedRoot
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedEndpoint
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedClient
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.SigningSource

/-!
# The adaptive pre-cap mixed source at the sampled public parameter

Each optional reply, private table update and public query is returned to the original adversary.

The concrete verifier then runs against the public key and the raw candidate on that same path.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants OracleComp OracleSpec TwoLayerGraph Honest
open SecretEncoding.Residual

private theorem request_grows (pp : PublicParam) (r : SignRequest) :
    ExtendsPrivate (mixedRequest pp r (mixedSignature emitStructure pp r.leafIndex r.message)) := by
  unfold mixedRequest
  apply ExtendsPrivate.bind (fun s z h => le_of_eq (mixedTick_private pp s h).symm)
  intro _
  have param : ExtendsPrivate (mixedParameter pp) := by
    unfold mixedParameter
    rw [← bind_pure_comp]
    exact (ExtendsPrivate.bind (fun s z h => mixedLocalWord_extends pp _ _ _ s h) (fun _ =>
      ExtendsPrivate.pure _))
  apply ExtendsPrivate.bind param
  intro _
  exact (mixed_signature_grows emitStructure pp r.leafIndex r.message).bind (fun _ =>
    ExtendsPrivate.pure _)

/-- Signing, private coins and public hashes preserve the sampled parameter row. -/
private theorem oracle_warm (w : HashOutput) (q : (World + SigningSpec).Domain)
    (s : ResidualCache (parameterOfWord w)) (warm : Warm w s) :
    ∀ result ∈ support (((mixedOracle (parameterOfWord w) q).run).run s), Warm w result.2 := by
  intro z hz
  apply LE.le.trans warm
  cases q with
  | inr r => exact request_grows _ _ _ _ hz
  | inl world =>
    have fuller : ExtendsPrivate ((fun a => (a,
      ([] : RawLog))) <$> mixedWorldPass (parameterOfWord w) world) := by
      rw [← bind_pure_comp]
      exact (ExtendsPrivate.lift _).bind (fun _ => ExtendsPrivate.pure _)
    exact fuller s z hz

attribute [local irreducible] selectedImpl simulateQ mark mixedSignature Xmss.verifyWith Xmss.node


/-- The comparison accepts a concrete same-state proof of the native signing routine. -/
theorem mixed_game_at (A : Adversary) (w : HashOutput) (left : Nat)
    (sign : ∀ r : SignRequest, let pp := parameterOfWord w
      SameMixed pp (simulateQ (selectedImpl pp) (simulateQ (mark IsTrial)
        (signDerived (hashOf sourcePass) sourcePrf pp r.leafIndex r.message)))
        (mixedSignature emitStructure pp r.leafIndex r.message)) :
    let pp := parameterOfWord w
    let initial := localState _ _ (toKeyedState pp (afterWord w))
    MixedAt pp left initial (simulateQ (selectedImpl pp) (markedContinuation A pp))
      (mixedGame pp A) := by
  let pp := parameterOfWord w
  let initial := localState _ _ (toKeyedState pp (afterWord w))
  have root : SameMixed pp (simulateQ (selectedImpl pp) (simulateQ (mark (fun _ => False))
      (Xmss.node (hashOf sourcePass) pp sourcePrf .top LAYER_HEIGHT 0))) (liftM (emitStructure
        (topRoot pp))) :=
    SameMixed.of_eager (guarded_root pp) (structural_call pp (root_structural pp .top _ _))
  have query (q : (World + SigningSpec).Domain) (n : Nat) (s : ResidualCache pp) (warm : Warm w s) :
      MixedAt pp n s (simulateQ (selectedImpl pp) (markedSigner q).run) (mixedOracle pp q).run := by
    cases q with
    | inr r => exact request_at w r _ (sign r) n s warm
    | inl t =>
      change MixedAt pp n s (simulateQ (selectedImpl pp) (simulateQ (mark (fun _ => True))
        ((fun a => (a, ([] : RawLog))) <$> sourcePass t))) ((fun a => (a,
          ([] : RawLog))) <$> mixedWorldPass pp t)
      rw [simulateQ_map, simulateQ_map]
      exact map_at (mixed_world_pass pp t n s) _
  simp only [topRoot, simulateQ_bind] at root
  unfold markedContinuation mixedGame
  simp only [simulateQ_bind, simulateQ_pure]
  apply mixed_bind_at left initial (root left initial)
  intro pkRoot localState rootRun n
  have saved : localState = initial := by
    simp only [StateT.run_monadLift, monadLift_self, mem_support_bind_iff,
      mem_support_pure_iff] at rootRun
    obtain ⟨_, _, eq⟩ := rootRun
    exact congrArg Prod.snd eq
  subst localState
  have client := client_at pp (mixedOracle pp) (Warm w) query (oracle_warm w)
    (A.main ⟨pkRoot,pp⟩) n initial le_rfl
  apply mixed_bind_at n initial client
  rintro ⟨candidate, log⟩ state _ rem
  exact ((mixed_verifier pp ⟨pkRoot,pp⟩ candidate).bind
    (fun a => SameMixed.pure (⟨⟨pkRoot,pp⟩,candidate,log,a⟩ : Outcome))) rem state

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
