module

public import EthLib.Cryptography.Proofs.Kzg.BlobBindingAdvantage
public import EthLib.Cryptography.Proofs.Kzg.PeerDasGames

set_option autoImplicit false

/-!
# Proofs: the blob binding bound under bilinear strong Diffie–Hellman

A reduction that recovers the setup secret `τ` solves BSDH at once.

So the secret-recovery term of the blob binding bound becomes a BSDH advantage.

BSDH is Definition 1 of ePrint 2025/1683.

<https://eprint.iacr.org/2025/1683>
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr TargetGroup)
open OracleComp ENNReal
open scoped EthLib.Cryptography.Bls.Fr

/-- The BSDH answer of a recovered secret `t`: the scalar `t - 1` and the generator.

For `t = τ`, the generator represents `1 / (τ - (t - 1)) = 1`.

A failed recovery gives the answer of `t = 0`. -/
def secretBsdhSolution {GT : Type} [CommMonoid GT] (M : TargetGroup GT) (candidate : Option Fr) :
    Fr × GT :=
  (candidate.getD 0 - 1, M.generator)

/-- The answer of the recovered secret solves the problem. -/
theorem isBsdhSolutionSub_secretBsdhSolution {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    (τ : Fr) : IsBsdhSolutionSub M τ (secretBsdhSolution M (some τ)) := by
  refine ⟨by simp [secretBsdhSolution], ?_⟩
  simp [secretBsdhSolution, TargetGroup.Represents]

/-- The reduction runs the recovery of the secret once, then answers with its result. -/
noncomputable def secretBsdhReduction {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    (adversary : SetupPowers → ProbComp (Option Fr)) : SetupPowers → ProbComp (Fr × GT) :=
  fun pw => secretBsdhSolution M <$> adversary pw

/-- **Recovery of the setup secret is at most as likely as a BSDH solution.**

Both games sample `τ` uniformly in `Fr` and give the adversary its setup powers. -/
theorem setupSecretAdvantage_le_bsdhAdvantage {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    (adversary : SetupPowers → ProbComp (Option Fr)) :
    setupSecretAdvantage adversary ≤ bsdhAdvantage M (secretBsdhReduction M adversary) :=
  prEvent_le_of_reduction ($ᵗ Fr) setupPowers adversary (fun _ => secretBsdhSolution M)
    (fun τ candidate => candidate = some τ) (fun τ sol => IsBsdhSolutionSub M τ sol)
    fun τ _ h => h ▸ isBsdhSolutionSub_secretBsdhSolution M τ

namespace BlobBinding

/-- **Blob-batch binding reduces to fresh challenge roots or a BSDH solution.**

The root bound is that of the bound with secret recovery, which holds under the same hypotheses.

The adversary is algebraic, an assumption that stands for the algebraic group model.

The challenge hash is a random oracle, and the target group is a model.

The BSDH reduction runs the secret recovery once, so the adversary also runs once.

The running time of the root search in the recovery is not formalized. -/
theorem blobBindingAdvantage_le_bsdh {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    (n qBlob qBatch : Nat) (adversary : SetupPowers → OracleComp Spec (List BlobOpening))
    (halgebraic : AlgebraicAdversary n adversary)
    (hblob : ∀ pw, IsQueryBoundP (adversary pw) (fun q => isBlobQuery q = true) qBlob)
    (hbatch : ∀ pw, IsQueryBoundP (adversary pw) (fun q => isBatchQuery q = true) qBatch) :
    blobBindingAdvantage n adversary ≤
      (qBlob + n : Nat) * blobRootWeight + (qBatch + 1 : Nat) * batchRootWeight n +
        bsdhAdvantage M (secretBsdhReduction M (setupSecretReduction n adversary)) :=
  (blobBindingAdvantage_le n qBlob qBatch adversary halgebraic hblob hbatch).trans
    (add_le_add_right (setupSecretAdvantage_le_bsdhAdvantage M _) _)

end BlobBinding

end EthLib.Cryptography.Kzg
