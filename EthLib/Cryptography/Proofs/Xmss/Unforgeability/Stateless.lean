module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Permutation
public import EthLib.Cryptography.Proofs.Xmss.Sign

/-!
# Proofs: leanXMSS with a signer that keeps no state

Source: the leanXMSS specification draft, section "Security".

The note's signer keeps only the seed, and the one here keeps the key of key generation.

A stateless signer signs every request with the key that key generation gave.

A tree that the signer of the game keeps is the tree that the seed gives.

So the stateless signer returns the same signatures as the signer that keeps its trees.

So both signers forge with the same probability in the random-permutation model.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants (LOG_LIFETIME)
open EthLib.Cryptography.Hash.Keccak (State keccak256LanesWith)
open EthLib.Cryptography.LazyPermutation (PermSpec PermComp forward permImpl
  simulateQ_permImpl_simulateQ_liftTarget)
open EthLib.Cryptography.HashSig (pureHash)

/-- leanXMSS over the random permutation, with a signer that never updates its key.

Each request is signed with the key of key generation. -/
noncomputable def schemeRpmStateless :
    SufCma.Scheme (PermSpec State) SignRequest Message PublicKey SecretKey Signature :=
  { schemeRpm with
    sign := fun sk request => (fun result => (result.1.toOption, sk)) <$>
      signWith (keccak256LanesWith forward) sk request.leafIndex request.message }

/-- After key generation, the stateless game logs one signer's answers.

It is the game of a stateless scheme: requests answered by the signer with the fixed key, logged. -/
theorem gameAfterKeys_schemeRpmStateless
    (adversary : SufCma.Adversary (PermSpec State) SignRequest Message PublicKey Signature)
    (pk : PublicKey) (sk : SecretKey) :
    SufCma.gameAfterKeys schemeRpmStateless adversary pk sk =
      (simulateQ (QueryImpl.ofLift (unifSpec + PermSpec State)
        (WriterT (QueryLog (SufCma.SigningSpec SignRequest Signature))
          (OracleComp (unifSpec + PermSpec State))) +
          QueryImpl.withLogging fun (request : SignRequest) =>
            (fun (result : Except XmssError Signature × SecretKey) => result.1.toOption) <$>
              signWith (keccak256LanesWith forward) sk request.leafIndex request.message)
        (adversary.main pk)).run >>= SufCma.checkForgery schemeRpmStateless pk :=
  SufCma.gameAfterKeys_of_sign_eq schemeRpmStateless adversary pk sk _ fun _ => by
    simp only [schemeRpmStateless, Functor.map_map]

/-! ## A fixed permutation -/

section Fixed

variable (π : Equiv.Perm State)

/-- Key generation over the permutation, answered through `π`, is key generation over `π`. -/
theorem simulateQ_liftTarget_keyGenWith (seed : Seed) :
    simulateQ ((permImpl π).liftTarget (PermComp State))
        (keyGenWith (keccak256LanesWith forward) seed) =
      pure (keyGenWith (keccak256LanesWith (pureHash π)) seed).run := by
  rw [keyGenWith_map_monad (fun x => simulateQ ((permImpl π).liftTarget (PermComp State)) x)
    (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f),
    funext (HashSig.simulateQ_liftTarget_keccak256LanesWith π)]
  exact (keyGenWith_map_monad (m := Id) (fun x => (pure x.run : OracleComp _ _))
    (fun _ => rfl) (fun _ _ => (pure_bind _ _).symm) _ seed).symm

/-- Signing over the permutation, answered through `π`, is signing over `π`. -/
theorem simulateQ_liftTarget_signWith (sk : SecretKey) (idx : LeafIndex) (msg : Message) :
    simulateQ ((permImpl π).liftTarget (PermComp State))
        (signWith (keccak256LanesWith forward) sk idx msg) =
      pure (signWith (keccak256LanesWith (pureHash π)) sk idx msg).run := by
  rw [signWith_map_monad (fun x => simulateQ ((permImpl π).liftTarget (PermComp State)) x)
    (fun b => simulateQ_pure _ b) (fun x f => simulateQ_bind _ x f),
    funext (HashSig.simulateQ_liftTarget_keccak256LanesWith π)]
  exact (signWith_map_monad (m := Id) (fun x => (pure x.run : OracleComp _ _))
    (fun _ => rfl) (fun _ _ => (pure_bind _ _).symm) _ sk idx msg).symm

/-- Answered through `π`, the stateless game is the game whose signer keeps its trees. -/
theorem game_mapOracles_liftTarget
    (adversary : SufCma.Adversary (PermSpec State) SignRequest Message PublicKey Signature) :
    SufCma.game (schemeRpmStateless.mapOracles ((permImpl π).liftTarget (PermComp State)))
        adversary =
      SufCma.game (schemeRpm.mapOracles ((permImpl π).liftTarget (PermComp State))) adversary := by
  -- Key generation draws a seed, then runs key generation over `π`.
  have hkey : (schemeRpm.mapOracles ((permImpl π).liftTarget (PermComp State))).keyGen =
      simulateQ ((permImpl π).liftTarget (PermComp State)) (liftM sampleSeed) >>= fun seed =>
        pure (keyGenWith (keccak256LanesWith (pureHash π)) seed).run := by
    change simulateQ ((permImpl π).liftTarget (PermComp State)) (liftM sampleSeed >>= fun seed =>
      keyGenWith (keccak256LanesWith forward) seed) = _
    rw [simulateQ_bind]
    exact bind_congr fun seed => simulateQ_liftTarget_keyGenWith π seed
  unfold SufCma.game
  change (schemeRpm.mapOracles ((permImpl π).liftTarget (PermComp State))).keyGen >>= _ =
    (schemeRpm.mapOracles ((permImpl π).liftTarget (PermComp State))).keyGen >>= _
  rw [hkey, bind_assoc, bind_assoc]
  refine bind_congr fun seed => ?_
  rw [pure_bind, pure_bind]
  -- Both signers answer as the signer with the key of key generation.
  set signer : SignRequest → OracleComp (unifSpec + PermSpec State) (Option Signature) :=
    fun request => pure (signWith (keccak256LanesWith (pureHash π))
      (keyGenWith (keccak256LanesWith (pureHash π)) seed).run.2 request.leafIndex
        request.message).run.1.toOption with hsigner
  -- The check of a forgery reads the verification, the messages and the rule of use alone.
  have hcheck :
      SufCma.checkForgery (schemeRpmStateless.mapOracles
        ((permImpl π).liftTarget (PermComp State))) =
      SufCma.checkForgery (schemeRpm.mapOracles ((permImpl π).liftTarget (PermComp State))) :=
    rfl
  rw [SufCma.gameAfterKeys_of_sign_eq _ adversary _ _ signer ?stateless,
    SufCma.gameAfterKeys_of_invariant _ adversary _
      (SecretKey.Reachable (keccak256LanesWith (pureHash π)) seed) signer ?stateful _
      SecretKey.Reachable.keyGen, hcheck]
  case stateless =>
    intro request
    change simulateQ ((permImpl π).liftTarget (PermComp State))
      ((fun result => (result.1.toOption, _)) <$>
        signWith (keccak256LanesWith forward) _ request.leafIndex request.message) = _
    rw [simulateQ_map, simulateQ_liftTarget_signWith, map_pure, hsigner, map_pure]
  case stateful =>
    -- The stateful key stays reachable, and a reachable key signs as key generation's.
    intro sk hsk request
    refine ⟨pure ((signWith (keccak256LanesWith (pureHash π)) sk request.leafIndex
        request.message).run.1.toOption,
      ⟨(signWith (keccak256LanesWith (pureHash π)) sk request.leafIndex request.message).run.2,
        hsk.sign _ _⟩), ?_, ?_⟩
    · change simulateQ ((permImpl π).liftTarget (PermComp State))
        ((fun result => (result.1.toOption, result.2)) <$>
          signWith (keccak256LanesWith forward) sk request.leafIndex request.message) = _
      rw [simulateQ_map, simulateQ_liftTarget_signWith, map_pure, map_pure]
    · rw [hsigner, map_pure]
      dsimp only
      rw [SecretKey.Reachable.keyGen.signWith_fst_eq hsk]

end Fixed

/-- **An adversary forges against the stateless signer exactly as often as against the other.**

The other signer keeps its trees. -/
theorem advantage_schemeRpmStateless
    (adversary : SufCma.Adversary (PermSpec State) SignRequest Message PublicKey Signature) :
    SufCma.advantage schemeRpmStateless (SufCma.randomPermutationModel State) adversary =
      SufCma.advantage schemeRpm (SufCma.randomPermutationModel State) adversary := by
  -- For each permutation `π`, the two games are one computation.
  have hgame : ∀ π : Equiv.Perm State,
      simulateQ (permImpl π) (SufCma.game schemeRpmStateless adversary) =
        simulateQ (permImpl π) (SufCma.game schemeRpm adversary) := fun π => by
    rw [← simulateQ_permImpl_simulateQ_liftTarget π, SufCma.simulateQ_game,
      game_mapOracles_liftTarget, ← SufCma.simulateQ_game, simulateQ_permImpl_simulateQ_liftTarget]
  -- A run in the model is a run against a uniform permutation drawn first.
  rw [SufCma.advantage, SufCma.advantage, SufCma.prEvent_runIn_randomPermutationModel,
    SufCma.prEvent_runIn_randomPermutationModel]
  simp only [hgame]

/-- **leanXMSS with a stateless signer is strongly unforgeable in the random-permutation model.**

The adversary itself makes at most `q` calls of the permutation or its inverse and `2^32` requests.

It forges with probability at most `(q + 531) * 2^-127`.

Key generation, the signer and the final verification are not charged to `q`. -/
theorem stronglyUnforgeable_randomPermutationModel_stateless :
    SufCma.StronglyUnforgeable schemeRpmStateless (SufCma.randomPermutationModel State)
      (2 ^ LOG_LIFETIME) 531 127 := fun q adversary hq hn => by
  rw [advantage_schemeRpmStateless]
  exact stronglyUnforgeable_randomPermutationModel q adversary hq hn

end EthLib.Cryptography.Xmss.Unforgeability
