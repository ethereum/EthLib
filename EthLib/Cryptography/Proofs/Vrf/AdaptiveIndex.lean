module

public import EthLib.Cryptography.Proofs.Vrf.Unpredictability
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.EvalDistEq
public import VCVio.OracleComp.SimSemantics.StateT.UntilBad
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Proofs: an output is unpredictable at an index the adversary chooses

Here the hash is a random oracle, and the `2^32` secrets are uniform and independent.

The adversary gets the root, queries the hash, and asks for openings at any indices.

It then names an index and guesses its output.

It wins if the guess is right and it never asked for the opening at that index.

It wins with probability at most `2^32 (1 + 2 Q) / 2^256`, where `Q = q_H + (q_O + 1) 2^33`.

Here `q_H` counts its hash queries and `q_O` its requests for an opening.

The proof splits a win by the index the adversary names, which costs the factor `2^32`.

For each index, the game agrees with the game of that fixed index until the adversary opens it.

Secrets derived from a seed are not covered here.

The property is the residual unpredictability of Micali, Rabin and Vadhan, §3.2.

It is part of their definition of a verifiable unpredictable function.

Source: "Verifiable Random Functions", [FOCS 1999](https://doi.org/10.1109/SFFCS.1999.814584).
-/

@[expose] public section

open OracleSpec OracleComp ENNReal

namespace EthLib.Cryptography

/-! ## Two handlers that differ only at one key -/

section LogKeys

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {K : Type} [DecidableEq K]

/-- Answer each query with a handler, and record the key of each query that has one. -/
def logKeys (impl : QueryImpl spec (OracleComp spec')) (key : spec.Domain → Option K) :
    QueryImpl spec (StateT (Finset K) (OracleComp spec')) := fun t =>
  StateT.mk fun S => (fun u => (u, S ∪ (key t).toFinset)) <$> impl t

/-- **Identical until a key is recorded.**

Two handlers answer alike every query whose key is not `k`.

Both are run over a second, stateful handler, such as a random oracle.

An event of the first run, with `k` never recorded, has at most its mass in the second run. -/
theorem prEvent_logKeys_le {τ : Type} (ro : QueryImpl spec' (StateT τ ProbComp))
    {impl₁ impl₂ : QueryImpl spec (OracleComp spec')} {key : spec.Domain → Option K} {k : K}
    (hagree : ∀ t, key t ≠ some k → impl₁ t = impl₂ t)
    {α : Type} (oa : OracleComp spec α) (S : Finset K) (s : τ) (P : α → Prop) :
    Pr{let z ← (simulateQ ro ((simulateQ (logKeys impl₁ key) oa).run S)).run' s}[
        P z.1 ∧ k ∉ z.2]
      ≤ Pr{let z ← (simulateQ ro (simulateQ impl₂ oa)).run' s}[P z] := by
  let aux : (t : spec.Domain) → τ → spec.Range t → τ → Finset K → Finset K :=
    fun t _ _ _ S => S ∪ (key t).toFinset
  have hflat : ∀ impl : QueryImpl spec (OracleComp spec'),
      (ro.mapStateTBase (logKeys impl key)).flattenStateT = (ro ∘ₛ impl).extendStateLeft aux := by
    intro impl
    funext t
    refine StateT.ext fun st => ?_
    simp [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, logKeys, aux,
      QueryImpl.apply_compose, map_eq_bind_pure_comp]
  let bad : Finset K × τ → Prop := fun st => k ∈ st.1
  have hsupp : ∀ (impl : QueryImpl spec (OracleComp spec')) t st z,
      z ∈ support (((ro ∘ₛ impl).extendStateLeft aux t).run st) →
        z.2.1 = st.1 ∪ (key t).toFinset := by
    intro impl t st z hz
    simp only [QueryImpl.extendStateLeft_apply, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨p, -, rfl⟩ := hz
    rfl
  have hagree' : QueryImpl.AgreeUntilBad ((ro ∘ₛ impl₁).extendStateLeft aux)
      ((ro ∘ₛ impl₂).extendStateLeft aux) bad := by
    refine QueryImpl.AgreeUntilBad.of_run_eq_or_bad fun t st _ => ?_
    by_cases hk : key t = some k
    · refine .inr ⟨fun z hz => ?_, fun z hz => ?_⟩ <;>
        simp [bad, hsupp _ t st z hz, hk]
    · left
      simp only [QueryImpl.extendStateLeft_apply, QueryImpl.apply_compose, hagree t hk]
  have hpres : QueryImpl.PreservesInv ((ro ∘ₛ impl₁).extendStateLeft aux) bad :=
    fun t st hst z hz => by
      simp only [bad, hsupp _ t st z hz, Finset.mem_union]
      exact Or.inl hst
  have h := hagree'.prEvent_simulateQ_run_and_not_bad_le hpres oa (S, s) fun z => P z.1
  rw [StateT.run'_eq, simulateQ_mapStateTBase_run_eq_map_flattenStateT, hflat,
    ← QueryImpl.simulateQ_compose, StateT.run'_eq,
    ← extendStateLeft_run_proj_eq (ro ∘ₛ impl₂) aux oa s S]
  simpa [Functor.map_map, Function.comp_def, bad] using h

end LogKeys

end EthLib.Cryptography

namespace EthLib.Cryptography.Vrf

/-! ## The game with an adaptive index -/

/-- An adversary that chooses the index: it returns an index and a guess of its output. -/
abbrev AdaptiveAdversary := Digest → OracleComp AdversarySpec (UInt32 × Digest)

/-- The index of a request for an opening. -/
def openedIndex : AdversarySpec.Domain → Option UInt32
  | .inl _ => none
  | .inr i => some i

/-- The honest holder: sampling and hash queries pass through, and every opening is answered. -/
def honestImpl (secrets : UInt32 → Digest) :
    QueryImpl AdversarySpec (OracleComp (unifSpec + HashSpec))
  | .inl t => (unifSpec + HashSpec).query t
  | .inr i => some <$> openingWith queryHash secrets i

/-- The game of an index the adversary chooses, in the random oracle model.

The adversary gets the root, queries the hash, and asks for openings at any indices.

It returns an index and a guess.

The game returns whether the guess is the output at that index and that index was never opened. -/
def adaptiveGame (secrets : UInt32 → Digest) (adversary : AdaptiveAdversary) :
    OracleComp (unifSpec + HashSpec) Bool := do
  let r ← rootWith queryHash secrets
  let z ← (simulateQ (logKeys (honestImpl secrets) openedIndex) (adversary r)).run ∅
  let output ← queryHash (outputInput (secrets z.1.1))
  return decide (z.1.1 ∉ z.2 ∧ z.1.2 = output)

/-! ## One guess of the index -/

/-- Away from index `c`, the honest holder answers as the holder of the game at `c`. -/
theorem honestImpl_eq_openImpl (secrets : UInt32 → Digest) (c : UInt32)
    (t : AdversarySpec.Domain) (ht : openedIndex t ≠ some c) :
    honestImpl secrets t = openImpl secrets c t := by
  rcases t with t | i
  · rfl
  · have hi : i ≠ c := fun h => ht (by rw [h]; rfl)
    simp [honestImpl, openImpl, hi]

/-- The adversary, followed by the hash query of the output at the index it names. -/
def withOutput (secrets : UInt32 → Digest) (adversary : AdaptiveAdversary) (r : Digest) :
    OracleComp AdversarySpec ((UInt32 × Digest) × Digest) := do
  let x ← adversary r
  let output ← AdversarySpec.query (.inl (.inr (outputInput (secrets x.1))))
  return (x, output)

/-- The game, with the output query folded into the adversary's run. -/
theorem adaptiveGame_eq (secrets : UInt32 → Digest) (adversary : AdaptiveAdversary) :
    adaptiveGame secrets adversary = (do
      let r ← rootWith queryHash secrets
      let z ← (simulateQ (logKeys (honestImpl secrets) openedIndex)
        (withOutput secrets adversary r)).run ∅
      return decide (z.1.1.1 ∉ z.2 ∧ z.1.1.2 = z.1.2)) := by
  simp only [adaptiveGame, withOutput, simulateQ_bind, simulateQ_pure, StateT.run_bind,
    bind_assoc]
  refine bind_congr fun r => bind_congr fun z => ?_
  simp [logKeys, honestImpl, openedIndex, queryHash]

/-- After the root, a win at index `c` is a win of the game at `c` against the same adversary.

That adversary only drops the index it names. -/
theorem prEvent_withOutput_le (secrets : UInt32 → Digest) (c : UInt32)
    (adversary : AdaptiveAdversary) (r : Digest) (cache : HashSpec.QueryCache) :
    Pr{let z ← (simulateQ HashSpec.romImpl ((simulateQ (logKeys (honestImpl secrets) openedIndex)
        (withOutput secrets adversary r)).run ∅)).run' cache}[
        (z.1.1.1 ∉ z.2 ∧ z.1.1.2 = z.1.2) ∧ z.1.1.1 = c]
      ≤ Pr{let z ← (simulateQ HashSpec.romImpl (do
          let guess ← simulateQ (openImpl secrets c) (Prod.snd <$> adversary r)
          let output ← queryHash (outputInput (secrets c))
          return (guess, output))).run' cache}[z.1 = z.2] := by
  calc _ ≤ Pr{let z ← (simulateQ HashSpec.romImpl ((simulateQ (logKeys (honestImpl secrets)
          openedIndex) (withOutput secrets adversary r)).run ∅)).run' cache}[
          (z.1.1.1 = c ∧ z.1.1.2 = z.1.2) ∧ c ∉ z.2] :=
        prEvent_mono _ _ _ fun z hz => by
          obtain ⟨⟨h1, h2⟩, rfl⟩ := hz
          exact ⟨⟨rfl, h2⟩, h1⟩
    _ ≤ Pr{let z ← (simulateQ HashSpec.romImpl (simulateQ (openImpl secrets c)
          (withOutput secrets adversary r))).run' cache}[z.1.1 = c ∧ z.1.2 = z.2] :=
        prEvent_logKeys_le HashSpec.romImpl (impl₂ := openImpl secrets c)
          (honestImpl_eq_openImpl secrets c) (withOutput secrets adversary r) ∅ cache
          (fun x => x.1.1 = c ∧ x.1.2 = x.2)
    _ ≤ _ := by
      simp only [withOutput, simulateQ_bind, simulateQ_map, simulateQ_pure, StateT.run'_eq,
        StateT.run_bind, map_bind, bind_map_left]
      have hq : ∀ x, simulateQ (openImpl secrets c)
          (liftM (AdversarySpec.query (.inl (.inr x))) : OracleComp AdversarySpec Digest) =
          queryHash x := fun x => by simp [openImpl, queryHash]
      have key := prEvent_bind_mono_of_forall_le (m := ProbComp)
        ((simulateQ HashSpec.romImpl (simulateQ (openImpl secrets c) (adversary r))).run cache)
        (fun a => (fun b => (a.1, b.1)) <$>
          (simulateQ HashSpec.romImpl (queryHash (outputInput (secrets a.1.1)))).run a.2)
        (fun a => (fun b => (a.1.2, b.1)) <$>
          (simulateQ HashSpec.romImpl (queryHash (outputInput (secrets c)))).run a.2)
        (fun z => z.1.1 = c ∧ z.1.2 = z.2) (fun z => z.1 = z.2) fun a => by
          rw [prEvent_map, prEvent_map]
          by_cases ha : a.1.1 = c
          · rw [ha]
            exact prEvent_mono _ _ _ fun _ h => h.2
          · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun _ _ h => ha h.1]
            exact zero_le
      simpa [hq, map_eq_bind_pure_comp] using key

/-- The run of the game before its result. -/
def adaptiveRun (secrets : UInt32 → Digest) (adversary : AdaptiveAdversary) :
    ProbComp (((UInt32 × Digest) × Digest) × Finset UInt32) :=
  (simulateQ HashSpec.romImpl (do
    let r ← rootWith queryHash secrets
    (simulateQ (logKeys (honestImpl secrets) openedIndex) (withOutput secrets adversary r)).run ∅
    )).run' ∅

/-- A win at index `c` is a win of the game at `c`, against the adversary without its index. -/
theorem prEvent_adaptiveRun_le (secrets : UInt32 → Digest) (c : UInt32)
    (adversary : AdaptiveAdversary) :
    Pr{let z ← adaptiveRun secrets adversary}[(z.1.1.1 ∉ z.2 ∧ z.1.1.2 = z.1.2) ∧ z.1.1.1 = c]
      ≤ Pr{let z ← (simulateQ HashSpec.romImpl
          (game secrets c (secrets c) fun r => Prod.snd <$> adversary r)).run' ∅}[z.1 = z.2] := by
  have key := prEvent_bind_mono_of_forall_le (m := ProbComp)
    ((simulateQ HashSpec.romImpl (rootWith queryHash secrets)).run ∅)
    (fun p => (simulateQ HashSpec.romImpl ((simulateQ (logKeys (honestImpl secrets) openedIndex)
      (withOutput secrets adversary p.1)).run ∅)).run' p.2)
    (fun p => (simulateQ HashSpec.romImpl (do
      let guess ← simulateQ (openImpl secrets c) (Prod.snd <$> adversary p.1)
      let output ← queryHash (outputInput (secrets c))
      return (guess, output))).run' p.2)
    (fun z => (z.1.1.1 ∉ z.2 ∧ z.1.1.2 = z.1.2) ∧ z.1.1.1 = c) (fun z => z.1 = z.2)
    fun p => prEvent_withOutput_le secrets c adversary p.1 p.2
  convert key using 2
  · simp only [adaptiveRun, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  · simp only [game, Function.update_eq_self, simulateQ_bind, StateT.run'_eq, StateT.run_bind,
      map_bind]

/-- Each fixed index is won with probability at most the bound of the fixed game. -/
theorem prEvent_adaptiveRun_and_eq_le (c : UInt32) (adversary : AdaptiveAdversary)
    {qh qo : ℕ} (hh : ∀ r, IsQueryBoundP (adversary r) IsHashQuery qh)
    (ho : ∀ r, IsQueryBoundP (adversary r) IsOpenQuery qo) :
    Pr{let secrets ← $ᵗ (UInt32 → Digest)
       let z ← adaptiveRun secrets adversary}[(z.1.1.1 ∉ z.2 ∧ z.1.1.2 = z.1.2) ∧ z.1.1.1 = c]
      ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ + ((qh + (qo + 1) * 2 ^ 33 : ℕ) : ℝ≥0∞) * (2 * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
  let B : Adversary := fun r => Prod.snd <$> adversary r
  have hhB : ∀ r, IsQueryBoundP (B r) IsHashQuery qh := fun r => by
    simpa [B, isQueryBoundP_map_iff] using hh r
  have hoB : ∀ r, IsQueryBoundP (B r) IsOpenQuery qo := fun r => by
    simpa [B, isQueryBoundP_map_iff] using ho r
  let G : (UInt32 → Digest) → ProbComp (Digest × Digest) := fun secrets =>
    (simulateQ HashSpec.romImpl (game secrets c (secrets c) B)).run' ∅
  have hG : ∀ others s, G (Function.update others c s) =
      (simulateQ HashSpec.romImpl (game others c s B)).run' ∅ := fun others s => by
    simp only [G, game, Function.update_self, Function.update_idem]
  calc _ ≤ Pr{let secrets ← $ᵗ (UInt32 → Digest); let z ← G secrets}[z.1 = z.2] := by
        simpa [bind_assoc] using prEvent_bind_mono_of_forall_le (m := ProbComp)
          ($ᵗ (UInt32 → Digest)) _ G _ _ fun secrets => prEvent_adaptiveRun_le secrets c adversary
    _ = Pr{let s ← $ᵗ Digest
           let others ← $ᵗ (UInt32 → Digest)
           let z ← G (Function.update others c s)}[z.1 = z.2] := by
        have h := (evalDistEq_uniformSample_bind_update c G).prEvent_eq fun z => z.1 = z.2
        simpa [bind_assoc] using h.symm
    _ = Pr{let others ← $ᵗ (UInt32 → Digest)
           let s ← $ᵗ Digest
           let z ← (simulateQ HashSpec.romImpl (game others c s B)).run' ∅}[z.1 = z.2] := by
        simp only [hG]
        exact prEvent_bind_bind_swap _ _ _
    _ ≤ _ := by
        have key := prEvent_bind_le_of_forall_le_of_support (m := ProbComp)
          ($ᵗ (UInt32 → Digest))
          (fun others => $ᵗ Digest >>= fun s =>
            (simulateQ HashSpec.romImpl (game others c s B)).run' ∅)
          (fun z => z.1 = z.2) fun others _ => by
            simpa [bind_assoc] using prEvent_guess_le others c B hhB hoB
        simpa [bind_assoc] using key

/-! ## Unpredictability at an adaptive index -/

/-- The game returns the win of its run. -/
theorem run'_adaptiveGame (secrets : UInt32 → Digest) (adversary : AdaptiveAdversary) :
    (simulateQ HashSpec.romImpl (adaptiveGame secrets adversary)).run' ∅ =
      (fun z => decide (z.1.1.1 ∉ z.2 ∧ z.1.1.2 = z.1.2)) <$> adaptiveRun secrets adversary := by
  rw [adaptiveGame_eq, adaptiveRun]
  simp [StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind]

/-- **An output is unpredictable at an index the adversary chooses.**

The hash is a lazily sampled random oracle on byte strings, with 32-byte answers.

The `2^32` secrets are uniform and independent.

The adversary makes at most `q_H` hash queries and `q_O` requests for an opening on every path.

It names an index and guesses its output there.

It wins if the guess is right and it never asked for the opening at that index.

It wins with probability at most `2^32 (1 + 2 Q) / 2^256`.

Here `Q = q_H + (q_O + 1) 2^33`.

With `q_H = 2^64` and `q_O = 2^32`, the bound is below `2^-157`. -/
theorem prEvent_adaptiveGame_le (adversary : AdaptiveAdversary) {qh qo : ℕ}
    (hh : ∀ r, IsQueryBoundP (adversary r) IsHashQuery qh)
    (ho : ∀ r, IsQueryBoundP (adversary r) IsOpenQuery qo) :
    Pr{let secrets ← $ᵗ (UInt32 → Digest)
       let win ← (simulateQ HashSpec.romImpl (adaptiveGame secrets adversary)).run' ∅}[win]
      ≤ 2 ^ 32 * ((2 ^ 256 : ℝ≥0∞)⁻¹ +
        ((qh + (qo + 1) * 2 ^ 33 : ℕ) : ℝ≥0∞) * (2 * (2 ^ 256 : ℝ≥0∞)⁻¹)) := by
  have h := prEvent_exists_le_card_mul (m := ProbComp)
    ($ᵗ (UInt32 → Digest) >>= fun secrets => adaptiveRun secrets adversary)
    (fun c z => (z.1.1.1 ∉ z.2 ∧ z.1.1.2 = z.1.2) ∧ z.1.1.1 = c)
    (ε := (2 ^ 256 : ℝ≥0∞)⁻¹ + ((qh + (qo + 1) * 2 ^ 33 : ℕ) : ℝ≥0∞) * (2 * (2 ^ 256 : ℝ≥0∞)⁻¹))
    fun c => by simpa using prEvent_adaptiveRun_and_eq_le c adversary hh ho
  have hcard : (Fintype.card UInt32 : ℝ≥0∞) = 2 ^ 32 := by
    rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt32]
    norm_num
  rw [hcard] at h
  refine le_trans (le_of_eq ?_) ((prEvent_mono _ _ _ fun z (hz : _ ∧ _) =>
    ⟨z.1.1.1, hz, rfl⟩).trans h)
  simp only [run'_adaptiveGame]
  simp

end EthLib.Cryptography.Vrf
