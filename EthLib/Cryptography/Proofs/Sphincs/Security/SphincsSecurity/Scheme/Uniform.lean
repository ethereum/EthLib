module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Lemmas
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Uniform bits of a hash output

Any window of bits of a uniform 32-byte hash output is uniform.

In particular, the low 128 bits of a uniform output are a uniform digest.
-/

@[expose] public section

namespace SphincsSecurity

variable [Params]
open OracleComp OracleSpec ENNReal

omit [Params] in
/-- Two hash outputs with the same low `width` bits and the same bits above them are equal. -/
theorem hashOutput_eq_of_extract {width : Nat} (hwidth : width ≤ hashOutputBits) {x y : HashOutput}
    (hlow : x.extractLsb' 0 width = y.extractLsb' 0 width)
    (hhigh : x.extractLsb' width (hashOutputBits - width)
      = y.extractLsb' width (hashOutputBits - width)) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hlt : i < width
  · have := congrArg (fun b : BitVec width => b.getLsbD i) hlow
    simpa [BitVec.getLsbD_extractLsb', hlt] using this
  · have hshift : i - width < hashOutputBits - width := by omega
    have := congrArg (fun b : BitVec (hashOutputBits - width) => b.getLsbD (i - width)) hhigh
    simp only [BitVec.getLsbD_extractLsb', hshift, decide_true, Bool.true_and] at this
    rwa [show width + (i - width) = i by omega] at this

/-- A hash output split into its low `width` bits and the bits above them. -/
def splitHashOutput (width : Nat) (output : HashOutput) :
    BitVec width × BitVec (hashOutputBits - width) :=
  (output.extractLsb' 0 width,
    output.extractLsb' width (hashOutputBits - width))

omit [Params] in
theorem splitHashOutput_injective {width : Nat} (hwidth : width ≤ hashOutputBits) :
    Function.Injective (splitHashOutput width) := by
  intro left right heq
  apply hashOutput_eq_of_extract hwidth
  · exact congrArg Prod.fst heq
  · exact congrArg Prod.snd heq

omit [Params] in
theorem splitHashOutput_bijective {width : Nat} (hwidth : width ≤ hashOutputBits) :
    Function.Bijective (splitHashOutput width) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨splitHashOutput_injective hwidth, ?_⟩
  rw [Fintype.card_prod, Fintype.card_bitVec, Fintype.card_bitVec, Fintype.card_bitVec, ← pow_add]
  congr
  omega

noncomputable def splitHashOutputEquiv (width : Nat) (hwidth : width ≤ hashOutputBits) :
    HashOutput ≃ BitVec width × BitVec (hashOutputBits - width) :=
  Equiv.ofBijective (splitHashOutput width) (splitHashOutput_bijective hwidth)

omit [Params] in
/-- The first coordinate of a uniform pair is uniform. -/
theorem map_fst_uniformSample_prod {α β : Type} [SampleableType α] [SampleableType β] :
    (Prod.fst <$> ($ᵗ (α × β) : ProbComp (α × β))) =ᵈ ($ᵗ α : ProbComp α) := by
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  calc ($ᵗ α >>= fun a => $ᵗ β >>= fun _ => (pure a : ProbComp α))
        =ᵈ ($ᵗ α >>= fun a => (pure a : ProbComp α)) :=
          EvalDistEq.bind_right _ fun a => OracleComp.EvalDistEq.bind_const _ _
    _ =ᵈ ($ᵗ α : ProbComp α) := by rw [bind_pure]

omit [Params] in
/-- The low `width` bits of a uniform hash output are uniform. -/
theorem evalDist_hashOutput_extract_uniform {width : Nat} (hwidth : width ≤ hashOutputBits) :
    ((fun output : HashOutput => output.extractLsb' 0 width) <$>
        ($ᵗ HashOutput : ProbComp HashOutput)) =ᵈ ($ᵗ BitVec width : ProbComp (BitVec width)) := by
  calc ((fun output : HashOutput => output.extractLsb' 0 width) <$>
        ($ᵗ HashOutput : ProbComp HashOutput))
        =ᵈ Prod.fst <$> (splitHashOutput width <$> ($ᵗ HashOutput : ProbComp HashOutput)) := by
          simp [Functor.map_map, splitHashOutput]
    _ =ᵈ Prod.fst <$> ($ᵗ (BitVec width × BitVec (hashOutputBits - width)) :
          ProbComp (BitVec width × BitVec (hashOutputBits - width))) :=
          (SampleableType.map_uniformSample_evalDistEq_of_bijective
            (splitHashOutput_bijective hwidth)).map _
    _ =ᵈ ($ᵗ BitVec width : ProbComp (BitVec width)) := map_fst_uniformSample_prod

/-- The three parts of a hash output around the `width` bits at `offset`. -/
def splitHashOutputAt (offset width : Nat) (output : HashOutput) :
    BitVec width × (BitVec offset × BitVec (hashOutputBits - (offset + width))) :=
  (output.extractLsb' offset width,
    (output.extractLsb' 0 offset,
      output.extractLsb' (offset + width) (hashOutputBits - (offset + width))))

omit [Params] in
theorem splitHashOutputAt_bijective {offset width : Nat}
    (hwidth : offset + width ≤ hashOutputBits) :
    Function.Bijective (splitHashOutputAt offset width) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨?_, ?_⟩
  · intro x y heq
    have hmid := congrArg Prod.fst heq
    have hlow := congrArg (fun t => t.2.1) heq
    have hhigh := congrArg (fun t => t.2.2) heq
    simp only [splitHashOutputAt] at hmid hlow hhigh
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases hlt : i < offset
    · have := congrArg (fun b : BitVec offset => b.getLsbD i) hlow
      simpa [BitVec.getLsbD_extractLsb', hlt] using this
    · by_cases hlt' : i < offset + width
      · have hshift : i - offset < width := by omega
        have := congrArg (fun b : BitVec width => b.getLsbD (i - offset)) hmid
        simp only [BitVec.getLsbD_extractLsb', hshift, decide_true, Bool.true_and] at this
        rwa [show offset + (i - offset) = i by omega] at this
      · have hshift : i - (offset + width) < hashOutputBits - (offset + width) := by omega
        have := congrArg (fun b : BitVec (hashOutputBits - (offset + width)) =>
          b.getLsbD (i - (offset + width))) hhigh
        simp only [BitVec.getLsbD_extractLsb', hshift, decide_true, Bool.true_and] at this
        rwa [show offset + width + (i - (offset + width)) = i by omega] at this
  · rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_bitVec, Fintype.card_bitVec,
      Fintype.card_bitVec, Fintype.card_bitVec,
      ← pow_add, ← pow_add]
    congr
    omega

omit [Params] in
/-- The `width` bits at any offset of a uniform hash output are uniform. -/
theorem evalDist_hashOutput_extractAt_uniform {offset width : Nat}
    (hwidth : offset + width ≤ hashOutputBits) :
    ((fun output : HashOutput => output.extractLsb' offset width) <$>
        ($ᵗ HashOutput : ProbComp HashOutput)) =ᵈ ($ᵗ BitVec width : ProbComp (BitVec width)) := by
  calc ((fun output : HashOutput => output.extractLsb' offset width) <$>
        ($ᵗ HashOutput : ProbComp HashOutput))
        =ᵈ Prod.fst <$>
          (splitHashOutputAt offset width <$> ($ᵗ HashOutput : ProbComp HashOutput)) := by
          simp [Functor.map_map, splitHashOutputAt]
    _ =ᵈ Prod.fst <$>
        ($ᵗ (BitVec width × (BitVec offset × BitVec (hashOutputBits - (offset + width)))) :
          ProbComp (BitVec width × (BitVec offset × BitVec (hashOutputBits - (offset + width))))) :=
          (SampleableType.map_uniformSample_evalDistEq_of_bijective
            (splitHashOutputAt_bijective hwidth)).map _
    _ =ᵈ ($ᵗ BitVec width : ProbComp (BitVec width)) := map_fst_uniformSample_prod

omit [Params] in
/-- The low 128 bits of a uniform hash output are a uniform digest. -/
theorem evalDist_truncateHash_uniform :
    (truncateHash <$> ($ᵗ HashOutput : ProbComp HashOutput)) =ᵈ ($ᵗ Digest : ProbComp Digest) :=
  evalDist_hashOutput_extract_uniform (width := digestBits) (by decide)

omit [Params] in
/-- The low 128 bits of a uniform output lie in a set with probability its share of digests. -/
theorem probEvent_uniform_truncateHash_mem (targets : Finset Digest) :
    Pr{let output ← ($ᵗ HashOutput : ProbComp HashOutput)}[truncateHash output ∈ targets] =
      (targets.card : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) := by
  rw [← prEvent_map ($ᵗ HashOutput : ProbComp HashOutput) truncateHash (· ∈ targets),
    evalDist_truncateHash_uniform.prEvent_eq]
  rw [SampleableType.prEvent_uniformSample]
  rw [Finset.filter_univ_mem]

end SphincsSecurity
