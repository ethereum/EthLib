module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.IdealStatement
public import EthLib.Cryptography.Proofs.EvalDistEq
public import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
public import VCVio.OracleComp.QueryTracking.Unpredictability

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

export EthLib.Cryptography.HashSig (hashOutputBits_eq splitHashOutput)

end XmssSecurity

namespace XmssSecurity.Rom

noncomputable local instance : UniformAnswerMeasure HashSpec :=
  UniformAnswerMeasure.ofFiniteNonempty _

theorem card_hashOutput : Fintype.card HashOutput = 2 ^ hashOutputBits := by
  simp

export EthLib.Cryptography.HashSig (joinDigest highDigest hashOutputEquivDigestPair
  independentDigestHalves evalDist_split_uniformHashOutput_eq_independent
  evalDist_truncate_uniformHashOutput)

def digestFiberEquiv (target : Digest) :
    Digest ≃ {output : HashOutput // truncateHash output = target} where
  toFun high := ⟨joinDigest high target, by
    change BitVec.extractLsb' 0 digestBits (high ++ target) = target
    exact BitVec.extractLsb'_append_eq_right⟩
  invFun output := highDigest output.val
  left_inv high := by
    change BitVec.extractLsb' digestBits digestBits (high ++ target) = high
    exact BitVec.extractLsb'_append_eq_left
  right_inv output := by
    apply Subtype.ext
    calc
      joinDigest (highDigest output.val) target =
          joinDigest (highDigest output.val) (truncateHash output.val) := by
        rw [output.property]
      _ = (splitHashOutput output.val).cast hashOutputBits_eq.symm := by
        exact congrArg (BitVec.cast hashOutputBits_eq.symm)
          (BitVec.extractLsb'_append_extractLsb' (x := splitHashOutput output.val))
      _ = output.val := by simp [splitHashOutput]

/-- Sample a 256-bit oracle answer whose low XMSS digest is fixed.

Its high half remains uniform. -/
noncomputable def sampleHashOutputWithDigest (target : Digest) :
    ProbComp HashOutput :=
  (fun high => hashOutputEquivDigestPair.symm (high, target)) <$>
    ($ᵗ Digest)

@[simp]
noncomputable def sampledHashOutputWithDigest :
    ProbComp (Digest × HashOutput) := do
  let low ← $ᵗ Digest
  let output ← sampleHashOutputWithDigest low
  return (low, output)

/-- Take a programmed answer together with its chosen low digest.

It has the same joint distribution as a uniform answer together with its truncation. -/
theorem evalDist_sampledHashOutputWithDigest_eq_uniform :
    sampledHashOutputWithDigest =ᵈ ((fun output : HashOutput => (truncateHash output, output)) <$>
        ($ᵗ HashOutput)) := by
  calc
    (sampledHashOutputWithDigest) =ᵈ
        ($ᵗ Digest >>= fun high =>
          $ᵗ Digest >>= fun low =>
            pure (low, hashOutputEquivDigestPair.symm (high, low))) := by
      unfold sampledHashOutputWithDigest sampleHashOutputWithDigest
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
    _ =ᵈ ((fun halves : Digest × Digest =>
          (halves.2, hashOutputEquivDigestPair.symm halves)) <$>
        independentDigestHalves) := by
      simp [independentDigestHalves, map_eq_bind_pure_comp, bind_assoc]
    _ =ᵈ ((fun halves : Digest × Digest =>
          (halves.2, hashOutputEquivDigestPair.symm halves)) <$>
        (hashOutputEquivDigestPair <$> ($ᵗ HashOutput))) :=
      evalDist_split_uniformHashOutput_eq_independent.symm.map _
    _ =ᵈ ((fun output : HashOutput => (truncateHash output, output)) <$>
        ($ᵗ HashOutput)) := by
      have hfunction :
          (fun halves : Digest × Digest =>
            (halves.2, hashOutputEquivDigestPair.symm halves)) ∘
              hashOutputEquivDigestPair =
            (fun output : HashOutput => (truncateHash output, output)) := by
        funext output
        apply Prod.ext
        · rfl
        · exact hashOutputEquivDigestPair.symm_apply_apply output
      rw [Functor.map_map]
      exact .of_eq (congrArg (· <$> ($ᵗ HashOutput)) hfunction)

/-- Take a programmed low digest and its independent high half.

Inside any continuation, one ordinary random-oracle output may replace them. -/
theorem evalDist_sampledHashOutputWithDigest_bind_eq_uniform_bind
    (continuation : Digest × HashOutput → ProbComp α) :
    (sampledHashOutputWithDigest >>= continuation) =ᵈ
      ($ᵗ HashOutput >>= fun output =>
        continuation (truncateHash output, output)) := by
  calc
    (sampledHashOutputWithDigest >>= continuation) =ᵈ
        (((fun output : HashOutput => (truncateHash output, output)) <$>
          ($ᵗ HashOutput)) >>= continuation) :=
      evalDist_sampledHashOutputWithDigest_eq_uniform.bind_left _

    _ =ᵈ ($ᵗ HashOutput >>= fun output =>
          continuation (truncateHash output, output)) := by
      simp [map_eq_bind_pure_comp, bind_assoc]

def matchingOutputs (target : Digest) : Finset HashOutput :=
  Finset.univ.filter (truncateHash · = target)

theorem card_matchingOutputs (target : Digest) :
    (matchingOutputs target).card = 2 ^ digestBits := by
  rw [show matchingOutputs target = Finset.univ.filter (truncateHash · = target) from rfl]
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr (digestFiberEquiv target)).symm.trans (by simp)

end XmssSecurity.Rom
