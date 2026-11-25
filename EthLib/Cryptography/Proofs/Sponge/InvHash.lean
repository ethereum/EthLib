module

public import EthLib.Cryptography.Proofs.Sponge.InvFwd

/-!
# Proofs: the hash step keeps the invariant of the combined game

The full view walks the sponge along the padded message.

When the pairs it should hold form a partial function that covers the walk, the walk follows them.

So without a collision, the walk ends in the value of the padded path, whose digest is the hash.
-/

@[expose] public section

namespace EthLib.Cryptography.Sponge.Indiff

open OracleComp OracleSpec LazyPermutation Indifferentiability

variable {Dg E C Msg : Type} {P : Padding Msg (Dg × E)} {iv : SpongeState Dg E C}

/-! ## Prefixes -/

/-- A prefix of a padding hashed after `m` is a prefix of the padding of `m`, or hashed before. -/
theorem hPath_cons_iff {L : List Msg} {m : Msg} {β : List (Dg × E)} :
    HPath P (m :: L) β ↔ (β ≠ [] ∧ β <+: P.pad m) ∨ HPath P L β := by
  simp [HPath]

/-! ## The walk of the full view -/

/-- The state after `i` blocks of `bs` from `s`, with the values of paths read from `vf`. -/
def walkState (vf : List (Dg × E) → SpongeState Dg E C) (pre : List (Dg × E))
    (s : SpongeState Dg E C) (bs : List (Dg × E)) (i : ℕ) : SpongeState Dg E C :=
  if i = 0 then s else vf (pre ++ bs.take i)

/-- One block further along the walk. -/
theorem walkState_cons (vf : List (Dg × E) → SpongeState Dg E C) (pre : List (Dg × E))
    (s y : SpongeState Dg E C) (B : Dg × E) (bs : List (Dg × E)) (i : ℕ)
    (hy : y = vf (pre ++ [B])) :
    walkState vf (pre ++ [B]) y bs i = walkState vf pre s (B :: bs) (i + 1) := by
  rcases i with _ | i <;> simp [walkState, hy, List.take_succ_cons]

section Walk

variable [XorOp Dg] [XorOp E] [DecidableEq Dg] [DecidableEq E] [DecidableEq C]

/-- **The walk follows the target pairs**, when they form a partial function covering it.

It ends in the value of the whole path, keeps the old pairs, and adds every step and no other. -/
theorem detWalk_spec (used : List (Dg × E) → Bool) (vf : List (Dg × E) → SpongeState Dg E C)
    (G : SpongeState Dg E C × SpongeState Dg E C → Prop)
    (hfun : ∀ x y y', G (x, y) → G (x, y') → y = y') (A₀ : PermCache (SpongeState Dg E C)) :
    ∀ (bs pre : List (Dg × E)) (s : SpongeState Dg E C) (A : PermCache (SpongeState Dg E C))
      (us : List (SpongeState Dg E C)),
      -- The target holds the recorded pairs, which include those of `A₀`.
      (∀ e ∈ A, G e) → (∀ e ∈ A₀, e ∈ A) →
      -- The target holds every step of the walk.
      (∀ i (h : i < bs.length),
        G (absorb (walkState vf pre s bs i) bs[i], vf (pre ++ bs.take (i + 1)))) →
      -- The step into a used path is recorded in `A₀`.
      (∀ i (h : i < bs.length), used (pre ++ bs.take (i + 1)) = true →
        (absorb (walkState vf pre s bs i) bs[i], vf (pre ++ bs.take (i + 1))) ∈ A₀) →
      (detWalk used vf pre s A bs us).1 = (if bs = [] then s else vf (pre ++ bs)) ∧
      (∀ e ∈ (detWalk used vf pre s A bs us).2, G e) ∧
      (∀ e ∈ A, e ∈ (detWalk used vf pre s A bs us).2) ∧
      (∀ i (h : i < bs.length), (absorb (walkState vf pre s bs i) bs[i],
        vf (pre ++ bs.take (i + 1))) ∈ (detWalk used vf pre s A bs us).2) := by
  intro bs
  induction bs with
  | nil =>
    intro pre s A us hA _ _ _
    exact ⟨by simp [detWalk], fun e he => hA e he, fun e he => he, fun i h => absurd h (by simp)⟩
  | cons B bs ih =>
    intro pre s A us hA hA₀ hpath hused
    have h0 := hpath 0 (by simp)
    simp only [walkState, ↓reduceIte, List.getElem_cons_zero, List.take_succ_cons,
      List.take_zero] at h0
    -- The hypotheses for the rest of the walk.
    have hpath' : ∀ y, y = vf (pre ++ [B]) → ∀ i (h : i < bs.length),
        G (absorb (walkState vf (pre ++ [B]) y bs i) bs[i],
          vf (pre ++ [B] ++ bs.take (i + 1))) := by
      intro y hy i hi
      have := hpath (i + 1) (by simp; omega)
      rw [walkState_cons vf pre s y B bs i hy]
      simpa [List.take_succ_cons] using this
    have hused' : ∀ y, y = vf (pre ++ [B]) → ∀ i (h : i < bs.length),
        used (pre ++ [B] ++ bs.take (i + 1)) = true →
        (absorb (walkState vf (pre ++ [B]) y bs i) bs[i],
          vf (pre ++ [B] ++ bs.take (i + 1))) ∈ A₀ := by
      intro y hy i hi hu
      have := hused (i + 1) (by simp; omega) (by simpa [List.take_succ_cons] using hu)
      rw [walkState_cons vf pre s y B bs i hy]
      simpa [List.take_succ_cons] using this
    -- The lookup at the first state returns the target pair.
    have hlook : ∀ y, A.lookup (absorb s B) = some y → y = vf (pre ++ [B]) := fun y hy =>
      hfun _ _ _ (hA _ (mem_of_lookup_eq_some hy)) h0
    -- The first step is recorded after the walk.
    have hfirst : ∀ (A' : PermCache (SpongeState Dg E C)), (absorb s B, vf (pre ++ [B])) ∈ A' →
        ∀ (us' : List (SpongeState Dg E C)), (∀ e ∈ A', G e) →
        (∀ e ∈ A₀, e ∈ A') → (∀ e ∈ A, e ∈ A') →
        (detWalk used vf (pre ++ [B]) (vf (pre ++ [B])) A' bs us').1 =
            (if B :: bs = [] then s else vf (pre ++ B :: bs)) ∧
          (∀ e ∈ (detWalk used vf (pre ++ [B]) (vf (pre ++ [B])) A' bs us').2, G e) ∧
          (∀ e ∈ A, e ∈ (detWalk used vf (pre ++ [B]) (vf (pre ++ [B])) A' bs us').2) ∧
          (∀ i (h : i < (B :: bs).length), (absorb (walkState vf pre s (B :: bs) i) (B :: bs)[i],
            vf (pre ++ (B :: bs).take (i + 1))) ∈
              (detWalk used vf (pre ++ [B]) (vf (pre ++ [B])) A' bs us').2) := by
      intro A' hmem us' hA' hA₀' hAA'
      obtain ⟨h1, h2, h3, h4⟩ := ih (pre ++ [B]) (vf (pre ++ [B])) A' us' hA' hA₀'
        (hpath' _ rfl) (hused' _ rfl)
      refine ⟨?_, h2, fun e he => h3 e (hAA' e he), fun i hi => ?_⟩
      · rw [h1]
        rcases bs with _ | ⟨b, bs⟩ <;> simp
      · rcases i with _ | i
        · simp only [walkState, ↓reduceIte, List.getElem_cons_zero, List.take_succ_cons,
            List.take_zero]
          exact h3 _ hmem
        · have := h4 i (by simp at hi; omega)
          rw [walkState_cons vf pre s _ B bs i rfl] at this
          simpa [List.take_succ_cons] using this
    simp only [detWalk]
    split
    · next y hy =>
      obtain rfl := hlook y hy
      exact hfirst A (mem_of_lookup_eq_some hy) us.tail hA hA₀ fun _ h => h
    · next hy =>
      have hnu : used (pre ++ [B]) = false := by
        by_contra hu
        have hmem := hA₀ _ (by
          have := hused 0 (by simp) (by simpa using hu)
          simpa [walkState] using this)
        have := lookup_eq_some_of_mem hmem fun e he hex => hfun _ _ _
          (by rw [← hex]; exact hA e he) h0
        rw [hy] at this
        exact absurd this (by simp)
      simp only [hnu, Bool.false_eq_true, ↓reduceIte]
      exact hfirst _ List.mem_cons_self us.tail
        (fun e he => by
          rcases List.mem_cons.mp he with rfl | he
          · exact h0
          · exact hA e he)
        (fun e he => List.mem_cons_of_mem _ (hA₀ e he))
        (fun e he => List.mem_cons_of_mem _ he)

variable [DecidableEq Msg] [SampleableType Dg] [SampleableType E] [SampleableType C]
  [Zero Dg] [Zero E] [LawfulXor Dg] [LawfulXor E]

/-- **The hash step keeps the invariant.** -/
theorem combInv_combHash {cs : CState Dg E C Msg} {c : ACache Msg Dg E C} (hI : CombInv P iv cs c)
    (m : Msg) {z : ((Dg × Dg) × CState Dg E C Msg) × ACache Msg Dg E C}
    (hz : z ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl
      ((combHash P iv m).run cs)).run c)) : CombInv P iv z.1.2 z.2 := by
  obtain ⟨hS, hcond⟩ := hI
  obtain ⟨w, c₁, d, hw, hd, hz1⟩ := combHash_support P iv m cs c hz
  obtain ⟨hcc₁, hcached, -, us, hdet⟩ := allWalk_support P _ [] iv cs.all (P.pad m) c hw
  obtain ⟨hc₁c', hd', -⟩ := randomOracle_run_support (hs := ASpec Msg Dg E C) (.inl m) c₁ hd
  simp only [List.nil_append] at hcached hdet
  set c' := z.2 with hc'
  have hcc' : c ≤ c' := le_trans hcc₁ hc₁c'
  rw [hz1]
  set cs' := (hashOut cs m w d).2 with hcs'
  have hhashed : cs'.hashed = m :: cs.hashed := rfl
  set pm := P.pad m with hpm
  have hpm0 : pm ≠ [] := P.pad_ne_nil m
  -- The nonempty prefixes of the padding are its first `i + 1` blocks.
  have hpre : ∀ β, β ≠ [] ∧ β <+: pm ↔ ∃ i < pm.length, β = pm.take (i + 1) := by
    intro β
    constructor
    · rintro ⟨hne, hp⟩
      have hlen := hp.length_le
      have hpos : 0 < β.length := List.length_pos_iff.mpr hne
      refine ⟨β.length - 1, by omega, ?_⟩
      rw [Nat.sub_add_cancel hpos]
      exact List.prefix_iff_eq_take.mp hp
    · rintro ⟨i, hi, rfl⟩
      exact ⟨by simpa [List.take_eq_nil_iff] using List.ne_nil_of_length_pos (by omega),
        List.take_prefix _ _⟩
  -- The values of the paths along the padded message.
  set vf : List (Dg × E) → SpongeState Dg E C := fun β => (cachedPathValue P c' β).getD iv with hvf
  have hvfc : ∀ i < pm.length,
      cachedPathValue P c' (pm.take (i + 1)) = some (vf (pm.take (i + 1))) := by
    intro i hi
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hcached i hi)
    have h' := cachedPathValue_mono P hc₁c' hv
    rw [h']
    simp [hvf, h']
  have hw_eq : w = detWalk (usedPath P cs.sim.chains cs.hashed) vf [] iv cs.all pm us :=
    hdet vf fun i hi => by
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hcached i hi)
      rw [hv]
      have := hvfc i hi
      rw [cachedPathValue_mono P hc₁c' hv] at this
      exact this
  have hsv : ∀ i ≤ pm.length, svC P iv c' (pm.take i) = some (walkState vf [] iv pm i) := by
    intro i hi
    rcases i with _ | i
    · simp [svC, walkState]
    · rw [svC_of_ne_nil (by simp [List.take_eq_nil_iff, hpm0]), hvfc i (by omega)]
      simp [walkState]
  -- The facts of every run.
  have hS' : CombStruct P iv cs' c' := by
    refine ⟨hS.root, fun p hp => svC_mono hcc' (hS.chainVal p hp), hS.chainEdge,
      fun β hβ => ?_⟩
    rcases hPath_cons_iff.mp (hhashed ▸ hβ) with h | h
    · obtain ⟨i, hi, rfl⟩ := (hpre _).mp h
      rw [hvfc i hi]
      simp
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hS.hCached β h)
      rw [cachedPathValue_mono P hcc' hv]
      simp
  refine ⟨hS', fun hbad hEC' => ?_⟩
  have hHid : ∀ β, Hidden P cs.vis β → Hidden P cs'.vis β := fun β hβ =>
    ⟨hPath_cons_iff.mpr (Or.inr hβ.1), hβ.2⟩
  have hEC : ¬ HiddenCollision P iv cs.vis c := by
    rintro ⟨β, v, hβ, hv, h⟩
    refine hEC' ⟨β, v, hHid β hβ, cachedPathValue_mono P hcc' hv, ?_⟩
    rcases h with h | ⟨γ, w', hγ, hne, hw', hwv⟩
    · exact Or.inl h
    · exact Or.inr ⟨γ, w', hHid γ hγ, hne, cachedPathValue_mono P hcc' hw', hwv⟩
  have hC := hcond hbad hEC
  have hV' : VisCons cs'.sim := hC.vis
  -- The target pairs.
  set G := GEdge P iv cs' c' with hG
  have hGmono : ∀ e, GEdge P iv cs c e → G e := by
    rintro e (h | h)
    · exact Or.inl h
    · exact Or.inr (hiddenEdge_mono hcc' hHid h)
  have hfun : ∀ x y y', G (x, y) → G (x, y') → y = y' := fun x y y' h h' =>
    (Prod.mk.inj (gEdge_fst_inj hS' hV' hEC' h h' rfl)).2
  -- The step into a rooted prefix is a pair of the simulator.
  have hvisEdge : ∀ i (hi : i < pm.length), pm.take (i + 1) ∈ vPaths cs.sim →
      (absorb (walkState vf [] iv pm i) pm[i], vf (pm.take (i + 1))) ∈ cs.sim.edges := by
    intro i hi hvis
    obtain ⟨v₀, hv₀⟩ := exists_chain_of_mem_vPaths hvis
    obtain ⟨q, hq, B, h1, h2⟩ := hS.chainEdge _ hv₀ (by simp [List.take_eq_nil_iff, hpm0])
    rw [List.take_succ_eq_append_getElem hi] at h1
    obtain ⟨h3, h4⟩ := List.append_inj' h1 rfl
    obtain rfl : pm[i] = B := List.singleton_inj.mp h4
    have hq1 := svC_mono hcc' (hS.chainVal q hq)
    rw [← h3, hsv i (by omega)] at hq1
    have hv1 := svC_mono hcc' (hS.chainVal _ hv₀)
    rw [svC_of_ne_nil (by simp [List.take_eq_nil_iff, hpm0]), hvfc i hi] at hv1
    rw [Option.some.inj hq1, Option.some.inj hv1]
    exact h2
  -- The step into each prefix is a target pair.
  have hpath : ∀ i (hi : i < pm.length),
      G (absorb (walkState vf [] iv pm i) pm[i], vf ([] ++ pm.take (i + 1))) := by
    intro i hi
    rw [List.nil_append]
    by_cases hvis : pm.take (i + 1) ∈ vPaths cs.sim
    · exact Or.inl (hvisEdge i hi hvis)
    · refine Or.inr ⟨pm.take i, pm[i], _, _,
        ⟨?_, by rw [← List.take_succ_eq_append_getElem hi]; exact hvis⟩, hsv i (by omega), ?_, rfl⟩
      · rw [← List.take_succ_eq_append_getElem hi]
        exact hPath_cons_iff.mpr (Or.inl ((hpre _).mpr ⟨i, hi, rfl⟩))
      · rw [← List.take_succ_eq_append_getElem hi]
        exact hvfc i hi
  -- The step into a used prefix is already in the full view.
  have hused : ∀ i (hi : i < pm.length),
      usedPath P cs.sim.chains cs.hashed ([] ++ pm.take (i + 1)) = true →
      (absorb (walkState vf [] iv pm i) pm[i], vf ([] ++ pm.take (i + 1))) ∈ cs.all := by
    intro i hi hu
    rw [List.nil_append] at hu ⊢
    by_cases hvis : pm.take (i + 1) ∈ vPaths cs.sim
    · exact (hC.allMem _).mpr (Or.inl (hvisEdge i hi hvis))
    · have hH : HPath P cs.hashed (pm.take (i + 1)) :=
        (usedPath_eq_true_iff.mp hu).resolve_left hvis
      have hhid : Hidden P cs.vis (pm.take i ++ [pm[i]]) := by
        rw [← List.take_succ_eq_append_getElem hi]
        exact ⟨hH, hvis⟩
      obtain ⟨v₀, hv₀⟩ := Option.ne_none_iff_exists'.mp (hS.hCached _ hhid.1)
      obtain ⟨s₀, hs₀⟩ := svC_known hS (knownPath_init hS (Or.inr hhid))
      obtain rfl := svC_eq_of_le hcc' hs₀ (hsv i (by omega))
      have := hvfc i hi
      rw [List.take_succ_eq_append_getElem hi] at this
      obtain rfl := cachedPathValue_eq_of_le hcc' hv₀ this
      refine (hC.allMem _).mpr (Or.inr ⟨pm.take i, pm[i], _, _, hhid, hs₀, hv₀, ?_⟩)
      rw [List.take_succ_eq_append_getElem hi]
  obtain ⟨hw1, hwG, hwA, hwN⟩ := detWalk_spec (usedPath P cs.sim.chains cs.hashed) vf G hfun
    cs.all pm [] iv cs.all us (fun e he => hGmono e ((hC.allMem e).mp he)) (fun _ h => h)
    hpath hused
  rw [← hw_eq] at hw1 hwG hwA hwN
  simp only [hpm0, ↓reduceIte, List.nil_append] at hw1
  -- The real answer is the digest of the random oracle.
  have hdig : w.1.1.1 = d := by
    have hlen : 0 < pm.length := List.length_pos_iff.mpr hpm0
    have hv := hvfc (pm.length - 1) (by omega)
    rw [Nat.sub_add_cancel hlen, List.take_length] at hv
    rw [hw1]
    simp only [cachedPathValue, hpm, P.unpad_pad, hd'] at hv
    simp only [Option.bind_some, Option.map_eq_some_iff] at hv
    obtain ⟨t, -, ht⟩ := hv
    rw [← ht]
  refine ⟨hV', fun e => ⟨fun he => hwG e he, fun he => ?_⟩, ?_⟩
  · rcases he with he | ⟨γ, G', t, v, hδ, ht, hv, rfl⟩
    · exact hwA _ ((hC.allMem _).mpr (Or.inl he))
    · rcases hPath_cons_iff.mp hδ.1 with h | h
      · obtain ⟨i, hi, hγ⟩ := (hpre _).mp h
        change i < pm.length at hi
        rw [List.take_succ_eq_append_getElem hi] at hγ
        obtain ⟨rfl, hGG⟩ := List.append_inj' hγ rfl
        obtain rfl : G' = pm[i] := List.singleton_inj.mp hGG
        rw [hsv i (by omega)] at ht
        obtain rfl := Option.some.inj ht
        have := hvfc i hi
        rw [List.take_succ_eq_append_getElem hi, hv] at this
        obtain rfl := Option.some.inj this
        have := hwN i hi
        rw [List.take_succ_eq_append_getElem hi] at this
        exact this
      · have hhid : Hidden P cs.vis (γ ++ [G']) := ⟨h, hδ.2⟩
        obtain ⟨v₀, hv₀⟩ := Option.ne_none_iff_exists'.mp (hS.hCached _ h)
        obtain ⟨s₀, hs₀⟩ := svC_known hS (knownPath_init hS (Or.inr hhid))
        obtain rfl := svC_eq_of_le hcc' hs₀ ht
        obtain rfl := cachedPathValue_eq_of_le hcc' hv₀ hv
        exact hwA _ ((hC.allMem _).mpr (Or.inr ⟨γ, G', _, _, hhid, hs₀, hv₀, rfl⟩))
  · simp [hcs', hashOut, hdig, hC.noDiff]

end Walk

end EthLib.Cryptography.Sponge.Indiff
