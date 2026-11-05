module

public import EthLib.Cryptography.Proofs.Kzg.HonestCells

/-!
# Proofs: code-binding of PeerDAS, with one batch check of many cells

In the games of Lemmas 3 and 4 of ePrint 2025/1683, the verifier checks each cell alone.

This file states code-binding with one batch check of all opened cells of the commitment.

The batch has one challenge, from a hash.

The hash is a random oracle into `Fr` on the inputs of the core check.

That idealises SHA-256 reduced modulo `r`, the order of `Fr`, whose values are not exactly uniform.

The adversary may query the oracle, then outputs a commitment and openings at distinct cell indices.

The verifier queries the oracle on the inputs of the batch, and gets the challenge `x`.

It accepts when the batch check returns a verdict and `x` is a root of the error polynomial.

Under the pairing law, this is the batch check of cells at the challenge of the hash.

No theorem relates the two at another challenge.

The verifier accepts valid openings with every challenge.

The bound is the sum of the bound of Lemma 4 and `(q + 1) 127 / r`.

Here `q` counts the queries of the adversary.

The added term bounds the event that `x` is a root of a nonzero error polynomial.

Otherwise every opened cell is valid and verifies alone, and Lemma 4 applies.

A client that samples a column checks it in its own batch, with many commitments at one cell index.

So the cells of one commitment reach it through several batches, each with its own challenge.

The game does not model that shape.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (G1 G2 Fr TargetGroup)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr
open Polynomial OracleComp ENNReal MeasureTheory

/-! ## The batch check with a given challenge -/

/-- **The batch check of cells accepts, with the challenge `x` in place of its hash.**

The check returns a verdict, so the input is well formed.

The challenge `x` is a root of the error polynomial of the batch.

Each point has the scalar of its bytes, and the setup is one of the secret `τ`.

Under the pairing law, this is the batch check of cells at the challenge of the hash.

No theorem relates the two at another challenge. -/
def CellBatchInput.AcceptsAt (s : TrustedSetup) (τ : Fr) (y : CellBatchInput) (x : Fr) : Prop :=
  (∃ b, verifyCellKzgProofBatch s y.commitments y.cellIndices y.cells y.proofs = .ok b) ∧
    (y.toCellBatch.errorPoly τ scalarOf scalarOf).eval x = 0

/-- **At the challenge of its hash, the check with a given challenge is the batch check.**

Assume the pairing law and a well-formed setup of the secret `τ`.

The batch check accepts with its own challenge exactly when the batch check of cells accepts. -/
theorem CellBatchInput.acceptsAt_challenge_iff (laws : Bls.PairingLaws) {s : TrustedSetup}
    {τ : Fr} (hs : s.WellFormed τ) (y : CellBatchInput) :
    y.AcceptsAt s τ y.toCellBatch.challenge ↔
      verifyCellKzgProofBatch s y.commitments y.cellIndices y.cells y.proofs = .ok true := by
  have key : ∀ {b : Bool},
      verifyCellKzgProofBatch s y.commitments y.cellIndices y.cells y.proofs = .ok b →
        (b = true ↔ (y.toCellBatch.errorPoly τ scalarOf scalarOf).eval y.toCellBatch.challenge =
          0) := fun {b} hb => by
    obtain ⟨hvc, hvp⟩ := validates_of_verifyCellKzgProofBatch hb
    exact verifyCellKzgProofBatch_ok_iff_root laws hs y
      (fun k hk _ hP => represents_scalarOf (hvc _ (getElem!_mem_of_lt hk)) hP)
      (fun k hk _ hP => represents_scalarOf (hvp _ (getElem!_mem_of_lt hk)) hP) hb
  constructor
  · rintro ⟨⟨b, hb⟩, hr⟩
    rw [hb, (key hb).mpr hr]
  · intro h
    exact ⟨⟨true, h⟩, (key h).mp rfl⟩

/-- **Valid openings are accepted with every challenge.**

Let each entry of a batch be a valid opening at `τ`.

Then the batch check accepts it with every challenge `x`. -/
theorem CellBatchInput.acceptsAt_of_cellOpeningValid {s : TrustedSetup} {τ : Fr}
    {y : CellBatchInput} (h₁ : y.cells.size = y.commitments.size)
    (h₂ : y.proofs.size = y.commitments.size) (h₃ : y.cellIndices.size = y.commitments.size)
    (hv : ∀ k < y.commitments.size,
      CellOpeningValid τ y.commitments[k]! y.cellIndices[k]! y.cells[k]! y.proofs[k]!)
    (x : Fr) : y.AcceptsAt s τ x :=
  ⟨(exists_ok_of_cellOpeningValid h₁ h₂ h₃ hv).1, by
    rw [errorPoly_eq_zero_of_cellOpeningValid h₁ h₃ hv, Polynomial.eval_zero]⟩

/-! ## Reductions with a bad event -/

/-- **The union bound for two reductions and a bad event.**

When the adversary wins, one of the two reductions wins on the same run, or a bad event holds.

So the adversary wins with probability at most the sum for the two reductions and the bad event.
-/
theorem prEvent_le_add_add_of_reductions {S I O A B : Type} (sample : ProbComp S)
    (input : S → I) (adversary : I → ProbComp O) (f : I → O → A) (g : I → O → B)
    (win : S → O → Prop) (p : S → A → Prop) (q : S → B → Prop) (bad : S → O → Prop)
    (h : ∀ s o, win s o → p s (f (input s) o) ∨ q s (g (input s) o) ∨ bad s o) :
    Pr{let s ← sample; let o ← adversary (input s)}[win s o] ≤
      Pr{let s ← sample; let a ← f (input s) <$> adversary (input s)}[p s a] +
        Pr{let s ← sample; let b ← g (input s) <$> adversary (input s)}[q s b] +
          Pr{let s ← sample; let o ← adversary (input s)}[bad s o] := by
  let _ : MeasurableSpace S := ⊤
  have _ : DiscreteMeasurableSpace S := ⟨fun _ => trivial⟩
  rw [prEvent_bind_bind_eq_lintegral_of_discrete, prEvent_bind_bind_eq_lintegral_of_discrete,
    prEvent_bind_bind_eq_lintegral_of_discrete, prEvent_bind_bind_eq_lintegral_of_discrete,
    ← lintegral_add_left Measurable.of_discrete, ← lintegral_add_left Measurable.of_discrete]
  refine lintegral_mono fun s => ?_
  rw [prEvent_map, prEvent_map]
  refine (prEvent_mono _ _ _ (h s)).trans ((prEvent_or_le (adversary (input s)) _ _).trans ?_)
  rw [add_assoc]
  exact add_le_add_right (prEvent_or_le (adversary (input s)) _ _) _

/-- **A bound on the event of every secret bounds the event of the game.** -/
theorem prEvent_bind_le_of_forall {S O : Type} (sample : ProbComp S) (run : S → ProbComp O)
    (bad : S → O → Prop) {ε : ℝ≥0∞} (h : ∀ s, Pr{let o ← run s}[bad s o] ≤ ε) :
    Pr{let s ← sample; let o ← run s}[bad s o] ≤ ε := by
  let _ : MeasurableSpace S := ⊤
  have _ : DiscreteMeasurableSpace S := ⟨fun _ => trivial⟩
  rw [prEvent_bind_bind_eq_lintegral_of_discrete]
  calc ∫⁻ s, Pr{let o ← run s}[bad s o] ∂𝒟[sample]
      ≤ ∫⁻ _, ε ∂𝒟[sample] := lintegral_mono h
    _ = ε * 𝒟[sample] Set.univ := lintegral_const ε
    _ ≤ ε := mul_le_of_le_one_right' (evalDist_apply_univ_le_one sample)

/-! ## The game -/

/-- Entry `k` of the array of a mapped list. -/
theorem getElem!_toArray_map {α β : Type} [Inhabited β] (l : List α) (f : α → β) {k : Nat}
    (hk : k < l.length) : (l.map f).toArray[k]! = f l[k] := by
  rw [getElem!_pos _ k (by simpa using hk)]
  simp

/-- The inputs of the batch check for one commitment and a list of openings. -/
def openingsInput (out : Bytes48 × List CellOpening) : CellBatchInput where
  commitments := (out.2.map fun _ => out.1).toArray
  cellIndices := (out.2.map (·.cellIndex)).toArray
  cells := (out.2.map (·.cell)).toArray
  proofs := (out.2.map (·.proof)).toArray

/-- **The winning condition of code-binding, with one batch check of all openings.**

The adversary outputs a commitment and openings at distinct cell indices.

The batch check accepts them all, with the challenge `x` of the oracle.

No polynomial of degree below 4096 has a codeword that agrees with every opened cell. -/
def BatchCodeBindingWins (s : TrustedSetup) (τ : Fr)
    (p : (Bytes48 × List CellOpening) × Fr) : Prop :=
  (p.1.2.map (·.cellIndex)).Nodup ∧ (openingsInput p.1).AcceptsAt s τ p.2 ∧
    ¬∃ f : Fr[X], f.natDegree < FIELD_ELEMENTS_PER_BLOB ∧
      ∀ o ∈ p.1.2, o.cell = codewordCell f o.cellIndex

/-- The experiment of the batch game: the adversary, then the query of the verifier. -/
def batchCodeExperiment
    (adversary : SetupPowers → OracleComp (CellBatch →ₒ Fr) (Bytes48 × List CellOpening))
    (pw : SetupPowers) : OracleComp (CellBatch →ₒ Fr) ((Bytes48 × List CellOpening) × Fr) := do
  let out ← adversary pw
  let r ← liftM ((CellBatch →ₒ Fr).query (openingsInput out).toCellBatch)
  return (out, r)

/-- The experiment of the batch game, with the oracle answered at random. -/
noncomputable def batchCodeRun
    (adversary : SetupPowers → OracleComp (CellBatch →ₒ Fr) (Bytes48 × List CellOpening))
    (pw : SetupPowers) : ProbComp ((Bytes48 × List CellOpening) × Fr) :=
  (simulateQ OracleSpec.randomOracle (batchCodeExperiment adversary pw)).run' ∅

/-- **The advantage against code-binding, with one batch check of all openings.**

The secret `τ` is uniform in `Fr`, and the adversary receives its powers.

The verifier checks all openings at once, with the setup built from the powers. -/
noncomputable def batchCodeBindingAdvantage
    (adversary : SetupPowers → OracleComp (CellBatch →ₒ Fr) (Bytes48 × List CellOpening)) :
    ℝ≥0∞ :=
  Pr{let τ ← $ᵗ Fr; let p ← batchCodeRun adversary (setupPowers τ)}[
    BatchCodeBindingWins (TrustedSetup.ofPowers (setupPowers τ)) τ p]

/-- The first reduction from batch code-binding, to BSDH.

It runs the experiment, answering the oracle itself, then the search of Lemma 4. -/
noncomputable def batchCodeBsdhReduction {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    (adversary : SetupPowers → OracleComp (CellBatch →ₒ Fr) (Bytes48 × List CellOpening)) :
    SetupPowers → ProbComp (Fr × GT) :=
  fun pw => (fun p => codeBsdhSearch M (TrustedSetup.ofPowers pw) p.1) <$>
    batchCodeRun adversary pw

/-- The second reduction from batch code-binding, to ARSDH.

It runs the experiment, answering the oracle itself, then the search of Lemma 4. -/
noncomputable def batchCodeArsdhReduction
    (adversary : SetupPowers → OracleComp (CellBatch →ₒ Fr) (Bytes48 × List CellOpening)) :
    SetupPowers → ProbComp (Finset Fr × G1 × G1) :=
  fun pw => (fun p => codeArsdhSearch (TrustedSetup.ofPowers pw) p.1) <$>
    batchCodeRun adversary pw

/-! ## Code-binding with one batch check -/

/-- **When the adversary wins batch code-binding, a search wins or the challenge is a root.**

Assume the pairing law and a well-formed setup of the secret `τ`.

If the opened cells are all valid, the adversary also wins code-binding with cells checked alone.

Then one of the two searches of Lemma 4 returns a solution.

Otherwise the error polynomial of the batch is not zero, and the challenge is one of its roots.

The batch then has at most 128 cells, since their indices are distinct and below 128. -/
theorem batchCodeBinding_cases {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    (laws : Bls.PairingLaws) {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ)
    {p : (Bytes48 × List CellOpening) × Fr} (hw : BatchCodeBindingWins s τ p) :
    IsBsdhSolutionSub M τ (codeBsdhSearch M s p.1) ∨
      IsArsdhSolution (FIELD_ELEMENTS_PER_BLOB - 1) τ (codeArsdhSearch s p.1) ∨
      ((openingsInput p.1).cellIndices.size ≤ CELLS_PER_EXT_BLOB ∧
        (openingsInput p.1).toCellBatch.errorPoly τ scalarOf scalarOf ≠ 0 ∧
        ((openingsInput p.1).toCellBatch.errorPoly τ scalarOf scalarOf).eval p.2 = 0) := by
  obtain ⟨⟨com, os⟩, r⟩ := p
  obtain ⟨hnd, ⟨⟨b, hb⟩, hr⟩, hno⟩ := hw
  by_cases hz : (openingsInput (com, os)).toCellBatch.errorPoly τ scalarOf scalarOf = 0
  · -- Every opened cell is valid, so it verifies alone.
    have hwin : CodeBindingWins s (com, os) := by
      refine ⟨hnd, fun o ho => ?_, hno⟩
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ho
      have hv := cellOpeningValid_of_errorPoly_eq_zero hb hz (k := k)
        (by simpa [openingsInput] using hk)
      simp only [openingsInput, getElem!_toArray_map _ _ hk] at hv
      exact (CellOpening.verifies_iff laws hs).mpr hv
    rcases codeBinding_searches M laws hs hwin with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨?_, hz, hr⟩)
    obtain ⟨-, -, -, hci, -⟩ := verifyCellKzgProofBatch_eq_ok hb
    -- The cell indices are distinct and below 128.
    have hsub : (os.map (·.cellIndex)).toFinset ⊆ Finset.range CELLS_PER_EXT_BLOB := by
      intro j hj
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hj)
      have hk' : k < os.length := by simpa using hk
      have := hci k (by simpa [openingsInput] using hk')
      simp only [openingsInput, getElem!_toArray_map _ _ hk'] at this
      simpa using this
    have hcard := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd, Finset.card_range] at hcard
    simpa [openingsInput] using hcard

/-- **Code-binding of PeerDAS with one batch check of all openings.**

Assume the pairing law, and take a model of the target group.

Let the adversary make at most `q` queries to the random oracle.

Its advantage against batch code-binding is at most the sum of three terms.

- The advantage of the first reduction against `(4095, 64)`-BSDH.
- The advantage of the second reduction against `(4095, 64)`-ARSDH.
- `(q + 1) 127 / r`, for a challenge that is a root of a nonzero error polynomial.

Here `r` is the order of `Fr`, and the term `q + 1` counts the query of the verifier. -/
theorem batchCodeBindingAdvantage_le {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    (laws : Bls.PairingLaws)
    (adversary : SetupPowers → OracleComp (CellBatch →ₒ Fr) (Bytes48 × List CellOpening))
    {q : Nat} (hq : ∀ pw, OracleComp.IsTotalQueryBound (adversary pw) q) :
    batchCodeBindingAdvantage adversary ≤
      bsdhAdvantage M (batchCodeBsdhReduction M adversary) +
        arsdhAdvantage (batchCodeArsdhReduction adversary) +
          (q + 1) * ((CELLS_PER_EXT_BLOB - 1 : Nat) / Fr.modulus) := by
  refine (prEvent_le_add_add_of_reductions ($ᵗ Fr) setupPowers (batchCodeRun adversary)
    (fun pw p => codeBsdhSearch M (TrustedSetup.ofPowers pw) p.1)
    (fun pw p => codeArsdhSearch (TrustedSetup.ofPowers pw) p.1)
    (fun τ p => BatchCodeBindingWins (TrustedSetup.ofPowers (setupPowers τ)) τ p)
    (fun τ sol => IsBsdhSolutionSub M τ sol)
    (fun τ sol => IsArsdhSolution (FIELD_ELEMENTS_PER_BLOB - 1) τ sol)
    (fun τ p => (openingsInput p.1).cellIndices.size ≤ CELLS_PER_EXT_BLOB ∧
      (openingsInput p.1).toCellBatch.errorPoly τ scalarOf scalarOf ≠ 0 ∧
      ((openingsInput p.1).toCellBatch.errorPoly τ scalarOf scalarOf).eval p.2 = 0)
    fun τ _ hw => batchCodeBinding_cases M laws (wellFormed_ofPowers τ) hw).trans
      (add_le_add le_rfl (prEvent_bind_le_of_forall _ _ _ fun τ => ?_))
  -- For each secret, the root event is the one of the outer check with the oracle.
  have hq' : OracleComp.IsTotalQueryBound (openingsInput <$> adversary (setupPowers τ)) q := by
    rw [map_eq_bind_pure_comp, ← Nat.add_zero q]
    exact OracleComp.isTotalQueryBound_bind (hq _) fun _ => trivial
  have hexp : cellInputRomExperiment (openingsInput <$> adversary (setupPowers τ)) =
      Prod.map openingsInput id <$> batchCodeExperiment adversary (setupPowers τ) := by
    simp [cellInputRomExperiment, batchCodeExperiment]
  have h := prEvent_cellInput_root_le τ scalarOf scalarOf (n := CELLS_PER_EXT_BLOB) _ hq'
  rw [hexp, simulateQ_map, StateT.run'_map', prEvent_map] at h
  exact h

end EthLib.Cryptography.Kzg
