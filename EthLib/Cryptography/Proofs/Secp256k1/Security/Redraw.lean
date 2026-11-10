module

public import EthLib.Cryptography.Proofs.Secp256k1.Security.Game
public import EthLib.Cryptography.Proofs.LazyPermutation

/-!
# Proofs: inverse answers of `Π` redrawn with a known discrete logarithm

A new inverse query of `Π` gets a uniform value `α` of `A`.

If `α` encodes a nonzero multiple of the base point, draw a nonzero scalar `a` instead.

Answer the encoding of `a g`.

Then `a` is a discrete logarithm of a point with encoding `α`.

The test of whether `α` encodes a nonzero multiple of the base point is an argument.

A search over all scalars defines what the test must decide.

Part (a) of Definition 2 of the source asks that this test be efficient.

The answer keeps its law when the encoding is exactly 2-to-1 on the nonzero multiples of `g`.

That holds when the base point is nonzero, and `2` is nonzero.

It also needs that opposite points, and only they, share an encoding.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

The redraw is lines 25 to 28 of their Figure 7, in Game G2 of the proof of their Theorem 2.

Their proof says the change keeps the law because the encoding is semi-injective.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.Security

open OracleComp OracleSpec ENNReal LazyPermutation

variable {F G A M : Type}

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [FinEnum F] [FinEnum A]

/-- Whether `α` encodes a nonzero multiple of the base point.

When the base point generates the group, these are the encodings of the nonzero points.

It defines what the redraw's test must decide.

It searches all scalars, so it is not efficient. -/
def encodesPoint (scheme : Scheme F G A M) (α : A) : Bool :=
  (FinEnum.toList F).any fun a => decide (a ≠ 0 ∧ scheme.encode (a • scheme.g) = α)

/-- A new inverse answer, redrawn with its discrete logarithm when the test passes.

Draw `α` uniformly from `A`.

If the test says it encodes a nonzero multiple of the base point, draw a uniform nonzero scalar `a`.

Then answer the encoding of `a g`, with `a`; otherwise answer `α`, with nothing.

The argument `d` is only the default value of the draw from `A`. -/
def redrawInverse (scheme : Scheme F G A M) (inImage : A → Bool) (d : A) :
    ProbComp (A × Option F) := do
  let α ← uniformOutside [] d
  if inImage α then
    let a ← (uniformOutside [0] 1 : ProbComp F)
    pure (scheme.encode (a • scheme.g), some a)
  else pure (α, none)

/-- A redrawn answer with a scalar `a` is the encoding of `a g`, and `a` is nonzero. -/
theorem of_mem_support_redrawInverse_some {scheme : Scheme F G A M} {inImage : A → Bool}
    {d α : A} {a : F} (h : (α, some a) ∈ support (redrawInverse scheme inImage d)) :
    a ≠ 0 ∧ scheme.encode (a • scheme.g) = α := by
  simp only [redrawInverse, bind_pure_comp, support_bind, support_ite, support_map,
    support_pure, Set.mem_iUnion, exists_prop] at h
  obtain ⟨i, -, hi⟩ := h
  split_ifs at hi
  · obtain ⟨b, hb, hba⟩ := hi
    simp only [Prod.mk.injEq, Option.some.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    rw [uniformOutside] at hb
    have := (List.mem_filter.1 (mem_of_mem_support_uniformFrom
      (List.ne_nil_of_mem (a := 1) (by simp [FinEnum.mem_toList])) 1 hb)).2
    exact ⟨by simpa using this, rfl⟩
  · simp at hi

/-- The test passes exactly when its value encodes a nonzero multiple of the base point. -/
theorem encodesPoint_iff {scheme : Scheme F G A M} {α : A} :
    encodesPoint scheme α = true ↔ ∃ a : F, a ≠ 0 ∧ scheme.encode (a • scheme.g) = α := by
  simp [encodesPoint, FinEnum.mem_toList]

/-- A redrawn answer without a scalar encodes no nonzero multiple of the base point. -/
theorem of_mem_support_redrawInverse_none {scheme : Scheme F G A M} {inImage : A → Bool}
    (hImage : ∀ α, inImage α = encodesPoint scheme α)
    {d α : A} (h : (α, none) ∈ support (redrawInverse scheme inImage d)) :
    ∀ a : F, a ≠ 0 → scheme.encode (a • scheme.g) ≠ α := by
  simp only [redrawInverse, bind_pure_comp, support_bind, support_ite, support_map,
    support_pure, Set.mem_iUnion, exists_prop] at h
  obtain ⟨i, -, hi⟩ := h
  split_ifs at hi with hp
  · simp at hi
  · simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hi
    obtain ⟨rfl, -⟩ := hi
    exact fun a ha he => hp (by rw [hImage]; exact encodesPoint_iff.2 ⟨a, ha, he⟩)

/-- The nonzero scalars `b` with `b g` encoded as `a g` are `a` and `-a`, two scalars. -/
theorem card_filter_encode_eq {scheme : Scheme F G A M} (hg : scheme.g ≠ 0) (h2 : (2 : F) ≠ 0)
    (hsemi : scheme.SemiInjective) (hneg : scheme.EncodeNeg) {a : F} (ha : a ≠ 0) :
    (Finset.univ.filter fun b : F =>
      b ≠ 0 ∧ scheme.encode (b • scheme.g) = scheme.encode (a • scheme.g)).card = 2 := by
  have hna : a ≠ -a := fun h => ha (by
    have : (2 : F) * a = 0 := by rw [two_mul]; nth_rewrite 2 [h]; exact add_neg_cancel a
    exact (mul_eq_zero.1 this).resolve_left h2)
  rw [← Finset.card_pair hna]
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hb, he⟩
    rcases hsemi _ _ (smul_ne_zero ha hg) (smul_ne_zero hb hg) he.symm with h | h
    · exact Or.inl (smul_left_injective F hg h)
    · exact Or.inr (smul_left_injective F hg (h.trans (neg_smul a scheme.g).symm))
  · rintro (rfl | rfl)
    · exact ⟨ha, rfl⟩
    · exact ⟨neg_ne_zero.2 ha, by rw [neg_smul, hneg]⟩

/-- The nonzero scalars are twice as many as the encodings of the nonzero multiples of `g`. -/
theorem card_filter_encodesPoint_mul_two {scheme : Scheme F G A M} (hg : scheme.g ≠ 0)
    (h2 : (2 : F) ≠ 0) (hsemi : scheme.SemiInjective) (hneg : scheme.EncodeNeg) :
    (Finset.univ.filter fun α => encodesPoint scheme α).card * 2 =
      (Finset.univ.filter fun b : F => b ≠ 0).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun b : F => scheme.encode (b • scheme.g))
    (t := Finset.univ.filter fun α => encodesPoint scheme α) fun b hb => by
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      exact encodesPoint_iff.2 ⟨b, hb, rfl⟩]
  rw [Finset.sum_congr rfl fun α hα => ?_, Finset.sum_const, smul_eq_mul]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα
  obtain ⟨a, ha, rfl⟩ := encodesPoint_iff.1 hα
  rw [Finset.filter_filter]
  exact card_filter_encode_eq hg h2 hsemi hneg ha

/-- **The redrawn answer is uniform on `A`.**

The base point must be nonzero, and `2` must be nonzero in the scalars.

The encoding must be semi-injective, and opposite points must share their encoding.

The test must agree with the search over all scalars.

`2 ≠ 0` serves only the count; the source does not need it. -/
theorem redrawInverse_fst_evalDistEq {scheme : Scheme F G A M} {inImage : A → Bool}
    (hImage : ∀ α, inImage α = encodesPoint scheme α)
    (hg : scheme.g ≠ 0) (h2 : (2 : F) ≠ 0)
    (hsemi : scheme.SemiInjective) (hneg : scheme.EncodeNeg) (d : A) :
    Prod.fst <$> redrawInverse scheme inImage d =ᵈ uniformOutside [] d := by
  obtain rfl : inImage = encodesPoint scheme := funext hImage
  refine evalDistEq_of_forall_prEvent_eq_output fun α₀ => ?_
  have hnil : ((FinEnum.toList A).filter fun b => b ∉ []) = FinEnum.toList A := by simp
  have hu : ∀ α, Pr{let y ← uniformOutside [] d}[y = α] = ((FinEnum.toList A).length : ℝ≥0∞)⁻¹ :=
    fun α => by
      rw [uniformOutside, hnil,
        prEvent_uniformFrom_eq_of_mem FinEnum.nodup_toList d (FinEnum.mem_toList α)]
  rw [hu, redrawInverse, prEvent_map, prEvent_bind_eq_sum_fintype]
  simp only [hu]
  rw [← Finset.mul_sum]
  conv_rhs => rw [← mul_one ((FinEnum.toList A).length : ℝ≥0∞)⁻¹]
  congr 1
  have hp : Pr{let a ← (uniformOutside [0] 1 : ProbComp F)}[scheme.encode (a • scheme.g) = α₀] =
      ((Finset.univ.filter fun b : F => b ≠ 0 ∧ scheme.encode (b • scheme.g) = α₀).card : ℝ≥0∞) /
        (Finset.univ.filter fun b : F => b ≠ 0).card := by
    have hu : (FinEnum.toList F).toFinset = Finset.univ :=
      Finset.eq_univ_of_forall fun b => List.mem_toFinset.2 (FinEnum.mem_toList b)
    rw [uniformOutside, prEvent_uniformFrom_eq_countP ?hne, List.countP_filter,
      ← List.countP_eq_length_filter, ← hu, FinEnum.nodup_toList.card_eq_countP,
      FinEnum.nodup_toList.card_eq_countP]
    · simp only [List.mem_singleton, Bool.decide_and, Bool.and_comm]
    · exact List.ne_nil_of_mem (a := 1) (by simp [FinEnum.mem_toList])
  simp only [bind_pure_comp, apply_ite (fun m : ProbComp (A × Option F) => Pr{let x ← m}[x.1 = α₀]),
    prEvent_map, prEvent_pure, hp]
  by_cases hα₀ : encodesPoint scheme α₀ = true
  · obtain ⟨a₀, ha₀, rfl⟩ := encodesPoint_iff.1 hα₀
    rw [card_filter_encode_eq hg h2 hsemi hneg ha₀, Finset.sum_ite,
      Finset.sum_eq_zero (s := Finset.univ.filter fun α => ¬encodesPoint scheme α = true)
        fun α hα => by
          split_ifs with h
          · subst h
            exact absurd hα₀ (Finset.mem_filter.1 hα).2
          · rfl,
      add_zero, Finset.sum_const, nsmul_eq_mul,
      ← card_filter_encodesPoint_mul_two hg h2 hsemi hneg, ← mul_div_assoc,
      ← Nat.cast_mul]
    refine ENNReal.div_self (Nat.cast_ne_zero.2 (mul_ne_zero ?_ two_ne_zero))
      (ENNReal.natCast_ne_top _)
    exact Finset.card_ne_zero.2 ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, hα₀⟩⟩
  · have h0 : (Finset.univ.filter fun b : F => b ≠ 0 ∧ scheme.encode (b • scheme.g) = α₀) = ∅ :=
      Finset.filter_false_of_mem fun b _ hb => hα₀ (encodesPoint_iff.2 ⟨b, hb⟩)
    rw [h0, Finset.card_empty, Nat.cast_zero, ENNReal.zero_div]
    rw [Finset.sum_congr rfl fun α _ => (show (if encodesPoint scheme α = true then (0 : ℝ≥0∞)
      else if α = α₀ then 1 else 0) = if α₀ = α then 1 else 0 by
        split_ifs <;> first | rfl | (subst_vars; contradiction)),
      Finset.sum_ite_eq]
    simp

end EthLib.Cryptography.Secp256k1.Security
