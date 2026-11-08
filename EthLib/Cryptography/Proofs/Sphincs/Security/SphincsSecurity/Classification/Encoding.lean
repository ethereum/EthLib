module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Code
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Uniform

/-!
# Neighbors of a target-sum codeword

The code reads a 128-bit digest as 64 two-bit digits, with no padding bits.

A unit neighbor of a valid word is one step lower on one chain and no lower on any other chain.

A word has at most `64 * 63 = 4032` unit neighbors.

Two valid words are equal, unit neighbors, or apart by at least two backward steps.
-/

@[expose] public section

namespace SphincsSecurity.Security.EncodingCode

variable [Params]

open TargetSum OracleComp OracleSpec ENNReal
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

/-- A valid word one step below a valid reference word on one chain and no lower elsewhere. -/
def UnitNeighborAt (reference candidate : Encoding) (lowered : ChainIndex) : Prop :=
  Valid reference ∧ Valid candidate ∧ (candidate lowered).val + 1 = (reference lowered).val ∧
    ∀ index, index ≠ lowered → (reference index).val ≤ (candidate index).val

omit [Params] in
theorem UnitNeighborAt.ne {reference candidate : Encoding} {lowered : ChainIndex}
    (h : UnitNeighborAt reference candidate lowered) : candidate ≠ reference := by
  intro he
  have hd := h.2.2.1
  rw [he] at hd
  omega

noncomputable def unitNeighbors (reference : Encoding) (lowered : ChainIndex) : Finset Encoding :=
  Finset.univ.filter (fun candidate => UnitNeighborAt reference candidate lowered)

omit [Params] in
theorem mem_unitNeighbors {reference candidate : Encoding} {lowered : ChainIndex} :
    candidate ∈ unitNeighbors reference lowered ↔ UnitNeighborAt reference candidate lowered := by
  simp only [unitNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def allUnitNeighbors (reference : Encoding) : Finset Encoding :=
  Finset.univ.biUnion (unitNeighbors reference)

omit [Params] in
theorem mem_allUnitNeighbors {reference candidate : Encoding} :
    candidate ∈ allUnitNeighbors reference ↔
      ∃ lowered, UnitNeighborAt reference candidate lowered := by
  simp only [allUnitNeighbors, Finset.mem_biUnion, Finset.mem_univ, true_and, mem_unitNeighbors]

/-- A bound on the unit neighbors of a word that are lower on one given chain. -/
def unitNeighborBound : Nat := numChains - 1

/-- A bound on all the unit neighbors of a word. -/
def neighborBound : Nat := numChains * (numChains - 1)

omit [Params] in
private theorem two_terms_le_sum (f : ChainIndex → Nat) {left right : ChainIndex}
    (hne : left ≠ right) :
    f left + f right ≤ ∑ index, f index := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := f)
      (Finset.subset_univ ({left, right} : Finset ChainIndex))
    (fun _ _ _ => Nat.zero_le _)
  simpa only [Finset.sum_pair hne] using h

omit [Params] in
private theorem single_of_sum_one (f : ChainIndex → Nat) (hsum : (∑ index, f index) = 1) :
    ∃ index, f index = 1 ∧ ∀ other, other ≠ index → f other = 0 := by
  have hnonzero : ∃ index, f index ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hz : (∑ index, f index) = 0 := Finset.sum_eq_zero fun index _ => hnone index
    omega
  obtain ⟨index, hi⟩ := hnonzero
  have hle : f index ≤ ∑ other, f other := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ index)
  have hone : f index = 1 := by omega
  refine ⟨index, hone, fun other hne => ?_⟩
  have hpair := two_terms_le_sum f hne
  omega

omit [Params] in
/--
A unit neighbor is one step higher on exactly one other chain, and equal on the rest.

The reason is that both words have the same digit sum.
-/
private theorem UnitNeighborAt.raised {reference candidate : Encoding} {lowered : ChainIndex}
    (h : UnitNeighborAt reference candidate lowered) :
    ∃ raised, raised ≠ lowered ∧ (reference raised).val + 1 = (candidate raised).val ∧
      ∀ index, index ≠ lowered → index ≠ raised → candidate index = reference index := by
  obtain ⟨hreference, hcandidate, hlow, hup⟩ := h
  have hpoint : ∀ index : ChainIndex,
      ((reference index).val - (candidate index).val) + (candidate index).val =
        ((candidate index).val - (reference index).val) + (reference index).val :=
            fun index => by omega
  have hsum := congrArg (fun f : ChainIndex → Nat => ∑ index, f index) (funext hpoint)
  simp only [Finset.sum_add_distrib] at hsum
  have hback : ∑ index, ((reference index).val - (candidate index).val) = 1 := by
    rw [Finset.sum_eq_single lowered]
    · omega
    · intro index _ hne
      have := hup index hne
      omega
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
  change _ + TargetSum.sum candidate = _ + TargetSum.sum reference at hsum
  have hsums : TargetSum.sum candidate = TargetSum.sum reference := hcandidate.trans hreference.symm
  have hforward : ∑ index, ((candidate index).val - (reference index).val) = 1 := by omega
  obtain ⟨raised, hraise, hothers⟩ := single_of_sum_one _ hforward
  refine ⟨raised, fun he => ?_, by omega, fun index hl hr => ?_⟩
  · subst raised
    omega
  · have hdown := hothers index hr
    have hle := hup index hl
    apply Fin.ext
    omega

omit [Params] in
theorem unitNeighbors_card_le (reference : Encoding) (lowered : ChainIndex) :
    (unitNeighbors reference lowered).card ≤ unitNeighborBound := by
  let chooseRaised : {candidate // UnitNeighborAt reference candidate lowered} →
      {raised : ChainIndex // raised ≠ lowered} :=
    fun candidate => ⟨candidate.property.raised.choose, candidate.property.raised.choose_spec.1⟩
  have hinj : Function.Injective chooseRaised := by
    intro left right he
    apply Subtype.ext
    have he' : left.property.raised.choose = right.property.raised.choose := congrArg Subtype.val he
    obtain ⟨_, hup, hrest⟩ := left.property.raised.choose_spec
    obtain ⟨_, hup', hrest'⟩ := right.property.raised.choose_spec
    rw [he'] at hup hrest
    funext index
    by_cases hl : index = lowered
    · subst index
      apply Fin.ext
      have := left.property.2.2.1
      have := right.property.2.2.1
      omega
    · by_cases hr : index = right.property.raised.choose
      · subst index
        apply Fin.ext
        omega
      · exact (hrest index hl hr).trans (hrest' index hl hr).symm
  have hcard := Fintype.card_le_of_injective chooseRaised hinj
  rw [Fintype.card_subtype, Fintype.card_subtype] at hcard
  have hr : (Finset.univ.filter fun raised : ChainIndex => raised ≠ lowered) =
      Finset.univ.erase lowered := by
    ext raised
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
  rw [hr, Finset.card_erase_of_mem (Finset.mem_univ lowered), Finset.card_univ,
      Fintype.card_fin] at hcard
  rw [unitNeighborBound]
  simpa only [unitNeighbors] using hcard

omit [Params] in
theorem allUnitNeighbors_card_le (reference : Encoding) : (allUnitNeighbors reference).card ≤
    neighborBound := by
  calc
    _ ≤ ∑ lowered : ChainIndex, (unitNeighbors reference lowered).card := Finset.card_biUnion_le
    _ ≤ ∑ _lowered : ChainIndex, unitNeighborBound :=
      Finset.sum_le_sum fun lowered _ => unitNeighbors_card_le reference lowered
    _ = neighborBound := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, neighborBound,
        unitNeighborBound]

/-! ### Values of the bounds -/

omit [Params] in
theorem unitNeighborBound_eq : unitNeighborBound = 63 := by
  rw [unitNeighborBound]
  rfl

omit [Params] in
theorem neighborBound_eq : neighborBound = 4032 := by
  rw [neighborBound]
  rfl

/-- The number of steps by which a candidate word lies below a reference word, over all chains. -/
def backwardWeight (reference candidate : Encoding) : Nat :=
  ∑ index : ChainIndex, ((reference index).val - (candidate index).val)

omit [Params] in
theorem unitNeighbor_of_backwardWeight_one {reference candidate : Encoding}
    (hreference : Valid reference) (hcandidate : Valid candidate)
        (hweight : backwardWeight reference candidate = 1) :
    ∃ lowered, UnitNeighborAt reference candidate lowered := by
  obtain ⟨lowered, hlower, hothers⟩ := single_of_sum_one
      (fun index => (reference index).val - (candidate index).val) hweight
  refine ⟨lowered, hreference, hcandidate, ?_, fun index hne => ?_⟩
  · omega
  · have hdown := hothers index hne
    omega

omit [Params] in
theorem eq_of_backwardWeight_zero {reference candidate : Encoding}
    (hreference : Valid reference) (hcandidate : Valid candidate)
        (hweight : backwardWeight reference candidate = 0) :
    reference = candidate := by
  apply Completeness.encoding_antichain hreference hcandidate
  intro index
  have hle : (reference index).val - (candidate index).val ≤
      backwardWeight reference candidate := by
    unfold backwardWeight
    exact Finset.single_le_sum
      (f := fun index : ChainIndex => (reference index).val - (candidate index).val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
  omega

omit [Params] in
theorem backwardWeight_two_witness {reference candidate : Encoding}
    (hweight : 2 ≤ backwardWeight reference candidate) :
    (∃ index, (candidate index).val + 2 ≤ (reference index).val) ∨
      ∃ left right, left ≠ right ∧ (candidate left).val < (reference left).val ∧
          (candidate right).val < (reference right).val := by
  by_cases hlarge : ∃ index, (candidate index).val + 2 ≤ (reference index).val
  · exact Or.inl hlarge
  have hnonzero : ∃ index, (candidate index).val < (reference index).val := by
    by_contra hnone
    push Not at hnone
    have hz : backwardWeight reference candidate = 0 := by
      apply Finset.sum_eq_zero
      intro index _
      exact Nat.sub_eq_zero_of_le (hnone index)
    omega
  obtain ⟨left, hl⟩ := hnonzero
  by_cases hother : ∃ right, left ≠ right ∧ (candidate right).val < (reference right).val
  · obtain ⟨right, hne, hr⟩ := hother
    exact Or.inr ⟨left, right, hne, hl, hr⟩
  · have hzero : ∀ index, index ≠ left → (reference index).val - (candidate index).val = 0 := by
      intro index hne
      have hn : ¬(candidate index).val < (reference index).val :=
        fun hi => hother ⟨index, hne.symm, hi⟩
      omega
    have hsum :
        backwardWeight reference candidate = (reference left).val - (candidate left).val := by
      apply Finset.sum_eq_single left
      · intro index _ hne
        exact hzero index hne
      · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
    have hn := not_exists.mp hlarge left
    omega

omit [Params] in
/--
Two valid words are equal or unit neighbors, or the candidate is at least two steps lower.

The two steps lie on one chain or on two different chains.
-/
theorem valid_encoding_classification {reference candidate : Encoding}
    (hreference : Valid reference) (hcandidate : Valid candidate) :
    reference = candidate ∨ (∃ lowered, UnitNeighborAt reference candidate lowered) ∨
      (∃ index, (candidate index).val + 2 ≤ (reference index).val) ∨
      ∃ left right, left ≠ right ∧ (candidate left).val < (reference left).val ∧
          (candidate right).val < (reference right).val := by
  by_cases hzero : backwardWeight reference candidate = 0
  · exact Or.inl (eq_of_backwardWeight_zero hreference hcandidate hzero)
  by_cases hone : backwardWeight reference candidate = 1
  · exact Or.inr (Or.inl (unitNeighbor_of_backwardWeight_one hreference hcandidate hone))
  exact Or.inr (Or.inr (backwardWeight_two_witness (by omega)))

omit [Params] in
/-- The encoding of a digest is injective, since its 64 two-bit digits hold all 128 bits. -/
theorem digestEncoding_injective : Function.Injective digestEncoding := by
  intro left right hencoding
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  have hbound : bit < 128 := hbit
  let index : ChainIndex :=
    ⟨Completeness.digitSlot (bit / 2), by unfold Completeness.digitSlot; change _ < 64; omega⟩
  have hdigit :
      left.extractLsb' (digitOffset index) 2 = right.extractLsb' (digitOffset index) 2 := by
    apply BitVec.eq_of_toNat_eq
    exact congrArg Fin.val (congrFun hencoding index)
  have hbits := congrArg (fun digit : BitVec 2 => digit.getLsbD (bit % 2)) hdigit
  have hmod : bit % 2 < 2 := by omega
  have hoffset : digitOffset index + bit % 2 = bit := by
    change 8 * (Completeness.digitSlot (bit / 2) / 4) + 6 -
        winternitzBits * (Completeness.digitSlot (bit / 2) % 4) + bit % 2 = bit
    unfold Completeness.digitSlot winternitzBits
    omega
  simpa only [BitVec.getLsbD_extractLsb', hmod, decide_true, Bool.true_and,
    hoffset] using hbits

omit [Params] in
theorem decode_valid {digest : Digest} {word : Encoding}
    (hdecode : decodeDigest digest = some word) : Valid word := by
  unfold decodeDigest at hdecode
  split at hdecode
  · rename_i hvalid
    exact Option.some.inj hdecode ▸ hvalid
  · simp at hdecode

omit [Params] in
/-- At most one digest decodes to a given word, since the encoding has no padding bits. -/
theorem decode_some_injective {left right : Digest} {word : Encoding}
    (hleft : decodeDigest left = some word) (hright : decodeDigest right = some word) :
    left = right := by
  unfold decodeDigest at hleft hright
  split at hleft <;> split at hright
  · exact digestEncoding_injective ((Option.some.inj hleft).trans (Option.some.inj hright).symm)
  all_goals simp at hleft hright

/-- The digests that decode to a word of a given finite set. -/
noncomputable def decodingDigests (words : Finset Encoding) : Finset Digest :=
  Finset.univ.filter fun digest => ∃ word ∈ words, decodeDigest digest = some word

omit [Params] in
theorem mem_decodingDigests {words : Finset Encoding} {digest : Digest} :
    digest ∈ decodingDigests words ↔ ∃ word ∈ words, decodeDigest digest = some word := by
  simp only [decodingDigests, Finset.mem_filter, Finset.mem_univ, true_and]

omit [Params] in
theorem decodingDigests_card_le (words : Finset Encoding) :
    (decodingDigests words).card ≤ words.card := by
  apply Finset.card_le_card_of_injOn (fun digest => (decodeDigest digest).getD
      (fun _ => ⟨0, by decide⟩))
  · intro digest hd
    obtain ⟨word, hw, hdecode⟩ := mem_decodingDigests.mp hd
    simpa only [hdecode, Option.getD_some, Finset.mem_coe] using hw
  · intro left hl right hr he
    obtain ⟨leftWord, _, hleft⟩ := mem_decodingDigests.mp hl
    obtain ⟨rightWord, _, hright⟩ := mem_decodingDigests.mp hr
    simp only [hleft, hright, Option.getD_some] at he
    exact decode_some_injective hleft (by rw [he]; exact hright)

end SphincsSecurity.Security.EncodingCode
