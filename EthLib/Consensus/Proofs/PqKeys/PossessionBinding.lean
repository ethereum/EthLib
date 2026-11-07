module

public import EthLib.Consensus.Proofs.PqKeys.Possession
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability

/-!
# Proofs: a proof of possession binds the leanXMSS key to the BLS key it names

EIP-8450 relies on this binding in its section "Key copying and squatting".

A copied leanXMSS key needs a new proof of possession for another registrant.

Only the holder of the key can make one.

The game below states it in the random oracle model, as the leanXMSS game does.

It runs in four steps:

- a uniform seed `S_0` gives the key pair `(sk, pk)`;
- the adversary gets `pk`, queries `H`, and requests signatures, never at one leaf index twice;
- it returns a BLS key and a proof;
- it wins when two things hold.
  The check accepts the proof for that BLS key and `pk`.
  No signing request for their possession root returned that proof.

The signing oracle signs any message at any leaf index.

So the adversary is at least as strong as one that sees the proofs and duty signatures of a key.

The theorem bounds the probability of a win by `q / 2^127`.

`q` counts every hash call of the experiment.

The proof turns a possession adversary into a leanXMSS adversary that wins whenever it wins.

That adversary returns the possession root and the decoded proof as its forgery.

The game checks a proof as the specification does: leaf index 0, then leanXMSS verification.

It verifies even when the leaf index is not 0, so it makes the hash calls of the leanXMSS game.

For every hash, its verdict is the verdict of the specification.
-/

@[expose] public section

namespace EthLib.Consensus.PqKeys

open OracleComp OracleSpec ENNReal
open Cryptography Cryptography.Xmss Cryptography.Xmss.Unforgeability
open Cryptography.Bls

/-- An adversary against proofs of possession.

From the public key, it samples coins, queries `H` and requests signatures.

It returns a BLS key and a claimed proof of possession for it. -/
structure PossessionAdversary where
  main : PublicKey →
    OracleComp (XmssSecurity.OracleWorld + SigningSpec) (BLSPubkey × XMSSSignature)

variable (config : Config) (genesisValidatorsRoot : Root)

/-- The leanXMSS forgery that a claimed proof stands for: the possession root and the proof. -/
def possessionForgery (pk : PublicKey) (claim : BLSPubkey × XMSSSignature) : Forgery where
  message := possessionRoot config genesisValidatorsRoot claim.1 (xmssPublicKeyBytes pk)
  signature := signatureOfBytes claim.2

/-- The game against proofs of possession, which returns two verdicts.

The first is that of the leanXMSS game on the forgery that the claim stands for.

The second is whether the proof carries leaf index 0. -/
noncomputable def possessionGamePair (adversary : PossessionAdversary) :
    OracleComp XmssSecurity.OracleWorld (Bool × Bool) := do
  let seed ← liftM sampleSeed
  let (sk, pk) ← liftM (keyGenWith H seed)
  let ((claim, log) : (BLSPubkey × XMSSSignature) × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift XmssSecurity.OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp XmssSecurity.OracleWorld)) + signingOracle sk)
      (adversary.main pk)).run
  let forgery := possessionForgery config genesisValidatorsRoot pk claim
  let verified ← liftM (verifyWith H pk forgery.message forgery.signature)
  return (decide (Valid log ∧ ¬Contains log forgery) && verified,
    decide (xmssSignatureIndex claim.2 = PQ_POSSESSION_XMSS_INDEX))

/-- The game: the adversary wins when the check accepts its proof and the proof is new. -/
noncomputable def possessionGameCore (adversary : PossessionAdversary) :
    OracleComp XmssSecurity.OracleWorld Bool :=
  (fun verdicts => verdicts.1 && verdicts.2) <$>
    possessionGamePair config genesisValidatorsRoot adversary

/-- The game against one random oracle, from an empty cache, counting every hash call. -/
noncomputable def possessionExperiment (adversary : PossessionAdversary) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (possessionGameCore config genesisValidatorsRoot adversary)).run.run' ∅

/-- The probability that the adversary wins. -/
noncomputable def possessionAdvantage (adversary : PossessionAdversary) : ℝ≥0∞ :=
  Pr{let result ← possessionExperiment config genesisValidatorsRoot adversary}[result.1 = true]

/-- Every run of the experiment makes at most `q` hash calls. -/
def HasPossessionHashQueryBound (adversary : PossessionAdversary) (q : Nat) : Prop :=
  ∀ result ∈ support (possessionExperiment config genesisValidatorsRoot adversary), result.2 ≤ q

/-- The leanXMSS adversary that runs a possession adversary and returns the forgery of its claim. -/
def PossessionAdversary.toXmss (adversary : PossessionAdversary) : Adversary where
  main pk := possessionForgery config genesisValidatorsRoot pk <$> adversary.main pk

/-- For every hash, the game's verdict on a claim is the verdict of the specification.

The game spells out the check: leaf index 0, then leanXMSS verification on the possession root. -/
theorem possessionVerdict_eq (f : ByteArray → Vector UInt8 32) (pk : PublicKey)
    (claim : BLSPubkey × XMSSSignature) :
    (decide (xmssSignatureIndex claim.2 = PQ_POSSESSION_XMSS_INDEX) &&
        (verifyWith (pureHash f) pk
          (possessionForgery config genesisValidatorsRoot pk claim).message
          (possessionForgery config genesisValidatorsRoot pk claim).signature).run) =
      (isValidPqPossessionProofWith (pureHash f) config genesisValidatorsRoot claim.1
        (xmssPublicKeyBytes pk) claim.2).run := by
  rw [isValidPqPossessionProofWith_eq, publicKeyOfBytes_xmssPublicKeyBytes]
  by_cases index : xmssSignatureIndex claim.2 = PQ_POSSESSION_XMSS_INDEX <;>
    simp [index, possessionForgery]

/-- The leanXMSS game of the reduction is the first verdict of the possession game. -/
theorem gameCore_toXmss (adversary : PossessionAdversary) :
    gameCore (adversary.toXmss config genesisValidatorsRoot) =
      Prod.fst <$> possessionGamePair config genesisValidatorsRoot adversary := by
  simp [gameCore, possessionGamePair, PossessionAdversary.toXmss, simulateQ_map, map_bind,
    bind_map_left]

/-- The possession game run against one random oracle, with both verdicts and the hash calls. -/
noncomputable def possessionPairExperiment (adversary : PossessionAdversary) :
    ProbComp ((Bool × Bool) × Nat) :=
  (simulateQ countedOracle (possessionGamePair config genesisValidatorsRoot adversary)).run.run' ∅

/-- Running a mapped game maps the result of its experiment, and keeps its count of hash calls. -/
theorem run_simulateQ_map {α β : Type} (f : α → β)
    (game : OracleComp XmssSecurity.OracleWorld α) :
    ((simulateQ countedOracle (f <$> game)).run.run' ∅ : ProbComp (β × Nat)) =
      (fun result : α × Nat => (f result.1, result.2)) <$>
        ((simulateQ countedOracle game).run.run' ∅ : ProbComp (α × Nat)) := by
  rw [simulateQ_map, WriterT.run_map, StateT.run'_map']
  rfl

/-- The experiment of the reduction reads the first verdict of the possession game. -/
theorem experiment_toXmss (adversary : PossessionAdversary) :
    experiment (adversary.toXmss config genesisValidatorsRoot) =
      (fun result => (result.1.1, result.2)) <$>
        possessionPairExperiment config genesisValidatorsRoot adversary := by
  rw [experiment, gameCore_toXmss, run_simulateQ_map]
  rfl

/-- The possession experiment reads both verdicts of the possession game. -/
theorem possessionExperiment_eq (adversary : PossessionAdversary) :
    possessionExperiment config genesisValidatorsRoot adversary =
      (fun result => (result.1.1 && result.1.2, result.2)) <$>
        possessionPairExperiment config genesisValidatorsRoot adversary := by
  rw [possessionExperiment, possessionGameCore, run_simulateQ_map]
  rfl

/-- Both experiments make the same hash calls, so a budget of one is a budget of the other. -/
theorem hashQueryBound_toXmss (adversary : PossessionAdversary) (q : Nat) :
    HasPossessionHashQueryBound config genesisValidatorsRoot adversary q ↔
      HasHashQueryBound (adversary.toXmss config genesisValidatorsRoot) q := by
  unfold HasPossessionHashQueryBound HasHashQueryBound
  rw [possessionExperiment_eq, experiment_toXmss]
  simp only [support_map, Set.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]

/-- Every win of the possession game is a win of the reduction in the leanXMSS game. -/
theorem possessionAdvantage_le (adversary : PossessionAdversary) :
    possessionAdvantage config genesisValidatorsRoot adversary ≤
      forgeAdvantage (adversary.toXmss config genesisValidatorsRoot) := by
  unfold possessionAdvantage forgeAdvantage
  rw [possessionExperiment_eq, experiment_toXmss, prEvent_map, prEvent_map]
  exact prEvent_mono _ _ _ fun result won => by simp_all

/-- A proof of possession binds the leanXMSS key to the BLS key it names.

Take an adversary whose experiment makes at most `q >= 1` hash calls.

It returns a BLS key and a proof that the check accepts for it and the honest leanXMSS key.

No signing request for their possession root returned that proof.

It does so with probability at most `q / 2^127`.

The bound is that of the leanXMSS game, and `q` counts every hash call of the experiment. -/
theorem possession_binding (q : Nat) (atLeastOne : 1 ≤ q) (adversary : PossessionAdversary)
    (budget : HasPossessionHashQueryBound config genesisValidatorsRoot adversary q) :
    possessionAdvantage config genesisValidatorsRoot adversary ≤
      q / ((2 ^ 127 : Nat) : ℝ≥0∞) :=
  (possessionAdvantage_le config genesisValidatorsRoot adversary).trans
    (unforgeable q atLeastOne _ ((hashQueryBound_toXmss config genesisValidatorsRoot adversary q).mp
      budget))

end EthLib.Consensus.PqKeys
