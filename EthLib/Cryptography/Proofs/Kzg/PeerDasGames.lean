module

public import EthLib.Cryptography.Proofs.Kzg.CodeBinding
public import EthLib.Cryptography.Proofs.Kzg.CellVerifier
public import EthLib.Cryptography.Proofs.Kzg.Binding

/-!
# Proofs: position-binding and code-binding of PeerDAS, as games

Wagner and Zapico prove the security of PeerDAS in the standard model, in ePrint 2025/1683.

<https://eprint.iacr.org/2025/1683>

This file states two lemmas of §3.1 there as games, and proves them.

- Lemma 3, position-binding: an adversary opens one cell index to two cells.
  Then a reduction wins bilinear strong Diffie–Hellman (BSDH) at least as often.
- Lemma 4, code-binding: an adversary opens cells that no blob explains.
  Then two reductions win BSDH and adaptive rational strong Diffie–Hellman (ARSDH).
  The sum of their probabilities bounds the probability of the adversary.

Lemma 3 is Lemma 2 of §3.1 of Wagner and Zapico, ePrint 2024/1362.

<https://eprint.iacr.org/2024/1362>

There, the adversary also receives `[τ^i]_2` for `i ≤ 4095`.

Its reduction reads only `[τ^i]_2` for `i < 64`.

In every game here, the secret `τ` is uniform in `Fr`.

Every adversary receives only `[τ^i]_1` for `i ≤ 4095` and `[τ^i]_2` for `i ≤ 64`.

This is the input of Definitions 1 and 2 of ePrint 2025/1683, with `(d, D) = (4095, 64)`.

The verifier of the games builds the full setup from these points.

It checks each cell alone, with the batch check of cells.

The error polynomial of a batch of one cell is a constant.

A nonzero constant has no root, and the zero constant means that the cell is valid.

So an accepted cell is valid without a random oracle.

Another file states code-binding with one batch check of all opened cells of a commitment.

Each reduction runs the adversary once.

It then runs a search that reads only the setup and the output of the adversary.

The running times of the reductions are not formalized.

That BSDH and ARSDH are hard is a hypothesis of no theorem here.

An adversary is any Lean function, so one that recovers `τ` from its input always wins.

Without a model of cost, hardness cannot be a Lean hypothesis.

The BSDH advantage is relative to a model of the target group.

The real pairing gives such a model.

This verifier accepts the cells and proofs of a blob.

Another file proves it.

Theorem 1 of ePrint 2025/1683 is not proved here.

That theorem is the security of PeerDAS as data-availability sampling.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Base (array_mapM_ok)

open EthLib.Cryptography.Bls (G1 G2 Fr TargetGroup)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr
open Polynomial OracleComp ENNReal MeasureTheory

/-! ## Reductions in general -/

/-- **A reduction that wins whenever the adversary wins wins at least as often.**

A game samples `s`, gives `input s` to the adversary, and reads its output `o`.

The reduction runs the adversary on the same input, then maps its output by `f`. -/
theorem prEvent_le_of_reduction {S I O A : Type} (sample : ProbComp S) (input : S → I)
    (adversary : I → ProbComp O) (f : I → O → A) (win : S → O → Prop) (p : S → A → Prop)
    (h : ∀ s o, win s o → p s (f (input s) o)) :
    Pr{let s ← sample; let o ← adversary (input s)}[win s o] ≤
      Pr{let s ← sample; let a ← f (input s) <$> adversary (input s)}[p s a] := by
  let _ : MeasurableSpace S := ⊤
  have _ : DiscreteMeasurableSpace S := ⟨fun _ => trivial⟩
  rw [prEvent_bind_bind_eq_lintegral_of_discrete, prEvent_bind_bind_eq_lintegral_of_discrete]
  refine lintegral_mono fun s => ?_
  rw [prEvent_map]
  exact prEvent_mono _ _ _ (h s)

/-- **The union bound for two reductions.**

When the adversary wins, one of the two reductions wins on the same run.

So the adversary wins with probability at most the sum for the two reductions. -/
theorem prEvent_le_add_of_reductions {S I O A B : Type} (sample : ProbComp S) (input : S → I)
    (adversary : I → ProbComp O) (f : I → O → A) (g : I → O → B) (win : S → O → Prop)
    (p : S → A → Prop) (q : S → B → Prop)
    (h : ∀ s o, win s o → p s (f (input s) o) ∨ q s (g (input s) o)) :
    Pr{let s ← sample; let o ← adversary (input s)}[win s o] ≤
      Pr{let s ← sample; let a ← f (input s) <$> adversary (input s)}[p s a] +
        Pr{let s ← sample; let b ← g (input s) <$> adversary (input s)}[q s b] := by
  let _ : MeasurableSpace S := ⊤
  have _ : DiscreteMeasurableSpace S := ⟨fun _ => trivial⟩
  rw [prEvent_bind_bind_eq_lintegral_of_discrete, prEvent_bind_bind_eq_lintegral_of_discrete,
    prEvent_bind_bind_eq_lintegral_of_discrete, ← lintegral_add_left Measurable.of_discrete]
  refine lintegral_mono fun s => ?_
  rw [prEvent_map, prEvent_map]
  exact (prEvent_mono _ _ _ (h s)).trans (prEvent_or_le _ _ _)

/-! ## The assumptions -/

/-- **The advantage against `(4095, 64)`-BSDH, Definition 1 of ePrint 2025/1683.**

The secret `τ` is uniform in `Fr`, and the adversary receives its powers.

It wins when it outputs `c ≠ τ` and the element of the target group for `1 / (τ - c)`.

The target group is a model, and the real pairing gives one. -/
noncomputable def bsdhAdvantage {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    (adversary : SetupPowers → ProbComp (Fr × GT)) : ℝ≥0∞ :=
  Pr{let τ ← $ᵗ Fr; let sol ← adversary (setupPowers τ)}[IsBsdhSolutionSub M τ sol]

/-- **The advantage against `(4095, 64)`-ARSDH, Definition 2 of ePrint 2025/1683.**

The secret `τ` is uniform in `Fr`, and the adversary receives its powers.

It outputs a set `S` of 4096 scalars and points that represent `a` and `b`.

It wins when `a ≠ 0` and `a = b V_S(τ)`. -/
noncomputable def arsdhAdvantage (adversary : SetupPowers → ProbComp (Finset Fr × G1 × G1)) :
    ℝ≥0∞ :=
  Pr{let τ ← $ᵗ Fr; let sol ← adversary (setupPowers τ)}[
    IsArsdhSolution (FIELD_ELEMENTS_PER_BLOB - 1) τ sol]

/-! ## One cell, checked alone -/

/-- An opening of one cell: its index, its bytes and the bytes of its proof. -/
structure CellOpening where
  cellIndex : CellIndex
  cell : Cell
  proof : Bytes48

/-- The verifier accepts the opening for the commitment, as a batch of one cell. -/
def CellOpening.Verifies (s : TrustedSetup) (commitment : Bytes48) (o : CellOpening) : Prop :=
  verifyCellKzgProofBatch s #[commitment] #[o.cellIndex] #[o.cell] #[o.proof] = .ok true

/-- A map that fails on an invalid proof validates every proof it reads. -/
private theorem zipIdx_mapM_validates {ε : Type} {g : Bytes48 × Nat → Except ε Bytes48}
    (hg : ∀ p r, g p = .ok r → validateKzgG1 p.1 = true) {ps qs : Array Bytes48}
    (h : ps.zipIdx.mapM g = .ok qs) : ∀ p ∈ ps, validateKzgG1 p = true := by
  obtain ⟨hsz, hk⟩ := array_mapM_ok h
  intro p hp
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hp
  have hi' : i < ps.zipIdx.size := by rw [Array.size_zipIdx]; exact hi
  have := hg _ _ (hk i hi' (by omega))
  rwa [Array.getElem_zipIdx] at this

/-- A batch of cells that returns validates every commitment and every proof.

It is stated on variables, so the kernel never evaluates a cell. -/
theorem validates_of_verifyCellKzgProofBatch {s : TrustedSetup} {bs : Array Bytes48}
    {cellIndices : Array CellIndex} {cells : Array Cell} {ps : Array Bytes48} {b : Bool}
    (h : verifyCellKzgProofBatch s bs cellIndices cells ps = .ok b) :
    (∀ c ∈ bs, validateKzgG1 c = true) ∧ (∀ p ∈ ps, validateKzgG1 p = true) := by
  unfold verifyCellKzgProofBatch at h
  by_cases h₁ : cells.size ≠ bs.size
  · simp [h₁, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  by_cases h₂ : ps.size ≠ bs.size
  · simp [h₁, h₂, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  by_cases h₃ : cellIndices.size ≠ bs.size
  · simp [h₁, h₂, h₃, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  by_cases h₄ : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = true
  · simp [h₁, h₂, h₃, h₄, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  simp only [ne_eq, Decidable.not_not, Bool.not_eq_true] at h₁ h₂ h₃ h₄
  simp only [h₄, Bool.false_eq_true, ↓reduceIte] at h
  simp only [h₁, h₂, h₃, ne_eq, not_true_eq_false, ↓reduceIte, bind, Except.bind] at h
  split at h
  · cases h
  rename_i dd hdd
  split at h
  · cases h
  split at h
  · cases h
  rename_i qs hqs
  constructor
  · intro c hc
    rw [← Array.foldlM_toList] at hdd
    have hall := Base.foldlM_forall_of_ok (P := fun p : Bytes48 × Nat => validateKzgG1 p.1 = true)
      (fun acc p r hr => by
      cases hb : bytesToKzgCommitment p.1 with
      | error e =>
        simp [hb, throw, throwThe, MonadExceptOf.throw] at hr
      | ok c =>
        unfold bytesToKzgCommitment at hb
        split at hb
        · assumption
        · cases hb) _ _ _ hdd
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hc
    have hm : (bs[i], i) ∈ bs.zipIdx.toList := by
      rw [Array.toList_zipIdx]
      exact List.mem_iff_getElem.mpr ⟨i, by simpa using hi, by simp⟩
    exact hall (bs[i], i) hm
  · refine zipIdx_mapM_validates ?_ hqs
    intro p r hr
    cases hb : bytesToKzgProof p.1 with
    | error e =>
      simp [hb, throw, throwThe, MonadExceptOf.throw] at hr
    | ok q =>
      unfold bytesToKzgProof at hb
      split at hb
      · assumption
      · cases hb

/-- A batch of one cell that returns validates its commitment and its proof. -/
theorem validateKzgG1_of_verifyCellKzgProofBatch {s : TrustedSetup} {commitment proof : Bytes48}
    {cellIndex : CellIndex} {cell : Cell} {b : Bool}
    (h : verifyCellKzgProofBatch s #[commitment] #[cellIndex] #[cell] #[proof] = .ok b) :
    validateKzgG1 commitment = true ∧ validateKzgG1 proof = true := by
  obtain ⟨hc, hp⟩ := validates_of_verifyCellKzgProofBatch h
  exact ⟨hc _ (by simp), hp _ (by simp)⟩

/-- A polynomial of degree zero that is not zero has no root. -/
theorem eval_ne_zero_of_natDegree_le_zero {P : Fr[X]} (h0 : P ≠ 0) (hd : P.natDegree ≤ 0)
    (x : Fr) : P.eval x ≠ 0 := by
  rw [eq_C_of_natDegree_le_zero hd, eval_C]
  intro h
  exact h0 ((eq_C_of_natDegree_le_zero hd).trans (by rw [h]; exact C_0))

/-- **An accepted cell is valid.**

Assume a well-formed setup of the secret `τ`.

Let the verifier accept one opening for a commitment.

Then the cell index is below 128, and the cell decodes to values `e`.

The commitment and the proof decode to points that represent scalars `c` and `w`.

Let `I` interpolate `e` on the coset of the cell, and let `h` be its shift.

These satisfy `c - I(τ) = w (τ^64 - h^64)`.

No random oracle is needed: the error polynomial of one cell is a constant.

A nonzero constant has no root, and the zero constant is the valid case. -/
theorem CellOpening.Verifies.valid {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {commitment : Bytes48} {o : CellOpening}
    (h : o.Verifies s commitment) :
    o.cellIndex < CELLS_PER_EXT_BLOB ∧ ∃ e C c P w, cellToCosetEvals o.cell = .ok e ∧
      uncompressG1 commitment = .ok C ∧ G1.Represents C c ∧ uncompressG1 o.proof = .ok P ∧
      G1.Represents P w ∧
      c - (cellInterpolant o.cellIndex e).eval τ =
        w * (τ ^ FIELD_ELEMENTS_PER_CELL - cellShift o.cellIndex ^ FIELD_ELEMENTS_PER_CELL) := by
  obtain ⟨hvc, hvp⟩ := validateKzgG1_of_verifyCellKzgProofBatch h
  obtain ⟨-, -, -, hci, evals, hev, hI⟩ := verifyCellKzgProofBatch_eq_ok h
  obtain ⟨⟨G, hG⟩, ⟨Q, hQ⟩⟩ := verifyCellKzgProofBatchImpl_decodes hI
  have hd : dedupCommitments #[commitment] = (#[commitment], #[0]) := by
    simp [dedupCommitments, dedupStep]
  rw [hd] at hG
  obtain ⟨hGsz, hGk⟩ := array_mapM_ok hG
  obtain ⟨hQsz, hQk⟩ := array_mapM_ok hQ
  obtain ⟨hesz, hek⟩ := array_mapM_ok hev
  have hC := hGk 0 (by simp) (by simp [hGsz])
  have hP := hQk 0 (by simp) (by simp [hQsz])
  have he := hek 0 (by simp) (by simp [hesz])
  rw [← getElem!_pos G 0 (by simp [hGsz])] at hC
  rw [← getElem!_pos Q 0 (by simp [hQsz])] at hP
  rw [← getElem!_pos evals 0 (by simp [hesz])] at he
  simp only [List.getElem_toArray, List.getElem_cons_zero] at hC hP he
  obtain ⟨c, hc⟩ := represents_of_validateKzgG1 hvc hC
  obtain ⟨w, hw⟩ := represents_of_validateKzgG1 hvp hP
  let y : CellBatchInput := ⟨#[commitment], #[o.cellIndex], #[o.cell], #[o.proof]⟩
  have hyC : ∀ k < y.commitments.size, ∀ P, uncompressG1 y.commitments[k]! = .ok P →
      G1.Represents P ((fun _ => c) y.commitments[k]!) := by
    intro k hk P' hP'
    obtain rfl : k = 0 := by simpa [y] using hk
    simp only [y, List.getElem!_toArray, List.getElem!_cons_zero, hC] at hP'
    cases hP'
    exact hc
  have hyP : ∀ k < y.proofs.size, ∀ P, uncompressG1 y.proofs[k]! = .ok P →
      G1.Represents P ((fun _ => w) y.proofs[k]!) := by
    intro k hk P' hP'
    obtain rfl : k = 0 := by simpa [y] using hk
    simp only [y, List.getElem!_toArray, List.getElem!_cons_zero, hP] at hP'
    cases hP'
    exact hw
  have hx : y.toCellBatch.cosetsEvals = evals := decodeCells_of_ok hev
  rcases verifyCellKzgProofBatch_valid_or_root hs y (c := fun _ => c) (w := fun _ => w) hyC
    hyP h with hall | ⟨h0, hroot⟩
  · have hv := hall 0 (by simp [y])
    rw [hx] at hv
    refine ⟨by simpa using hci 0 (by simp), evals[0]!, G[0]!, c, Q[0]!, w, he, hC, hc, hP, hw,
      ?_⟩
    simpa [y] using hv
  · have hdeg : (y.toCellBatch.errorPoly τ (fun _ => c) (fun _ => w)).natDegree ≤ 0 :=
      natDegree_errorPoly_le _ _
    exact absurd hroot (eval_ne_zero_of_natDegree_le_zero h0 hdeg _)

/-- The values of a cell, or no values if it does not decode. -/
def decodeCell (cell : Cell) : CosetEvals :=
  (cellToCosetEvals cell).toOption.getD #[]

/-- A cell that decodes has its values as its decoding.

It is stated on a variable cell, so the kernel never evaluates the decoding. -/
theorem decodeCell_of_ok {cell : Cell} {e : CosetEvals} (he : cellToCosetEvals cell = .ok e) :
    decodeCell cell = e := by
  unfold decodeCell
  rw [he]
  rfl

/-- The point of 48 bytes, or zero if they do not decode. -/
def decodePoint (b : Bytes48) : G1 :=
  match uncompressG1 b with
  | .ok P => P
  | .error _ => G1.zero

/-- Two accepted openings for one commitment have scalars that one equation relates.

Their commitment scalars are equal, since the commitment decodes to one point. -/
theorem CellOpening.Verifies.valid₂ {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {commitment : Bytes48} {C : G1} {c : Fr}
    (hC : uncompressG1 commitment = .ok C) (hc : G1.Represents C c) {o : CellOpening}
    (h : o.Verifies s commitment) :
    o.cellIndex < CELLS_PER_EXT_BLOB ∧ ∃ e w, cellToCosetEvals o.cell = .ok e ∧
      decodeCell o.cell = e ∧ G1.Represents (decodePoint o.proof) w ∧
      c - (cellInterpolant o.cellIndex e).eval τ =
        w * (τ ^ FIELD_ELEMENTS_PER_CELL - cellShift o.cellIndex ^ FIELD_ELEMENTS_PER_CELL) := by
  obtain ⟨hci, e, C', c', P, w, he, hC', hc', hP, hw, hv⟩ := h.valid hs
  rw [hC] at hC'
  cases hC'
  rw [hc.unique hc'] at ⊢
  refine ⟨hci, e, w, he, decodeCell_of_ok he, ?_, hv⟩
  simpa only [decodePoint, hP] using hw

/-! ## Position-binding, Lemma 3 -/

/-- The winning condition of position-binding, Definition 4 of ePrint 2025/1683.

The adversary outputs a commitment and two openings at one cell index, with different cells.

Both openings are accepted for the commitment. -/
def PositionBindingWins (s : TrustedSetup) (out : Bytes48 × CellOpening × CellOpening) : Prop :=
  out.2.1.cellIndex = out.2.2.cellIndex ∧ out.2.1.cell ≠ out.2.2.cell ∧
    out.2.1.Verifies s out.1 ∧ out.2.2.Verifies s out.1

/-- **The advantage against position-binding, Definition 4 of ePrint 2025/1683.**

The secret `τ` is uniform in `Fr`, and the adversary receives its powers.

The verifier checks the openings with the setup built from the powers. -/
noncomputable def positionBindingAdvantage
    (adversary : SetupPowers → ProbComp (Bytes48 × CellOpening × CellOpening)) : ℝ≥0∞ :=
  Pr{let τ ← $ᵗ Fr; let out ← adversary (setupPowers τ)}[
    PositionBindingWins (TrustedSetup.ofPowers (setupPowers τ)) out]

/-- The search of the reduction from position-binding to BSDH.

It runs the search on the two cells and their proofs.

It changes the sign of `c` to the sign of ePrint 2025/1683. -/
noncomputable def positionBsdhSearch {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    (s : TrustedSetup) (out : Bytes48 × CellOpening × CellOpening) : Fr × GT :=
  ((findBsdh M s out.2.1.cellIndex (decodeCell out.2.1.cell) (decodeCell out.2.2.cell)
    (decodePoint out.2.1.proof) (decodePoint out.2.2.proof)).map fun sol => (-sol.1, sol.2)).getD
    (0, 1)

/-- The reduction from position-binding to BSDH: the adversary, then the search. -/
noncomputable def positionBsdhReduction {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    (adversary : SetupPowers → ProbComp (Bytes48 × CellOpening × CellOpening)) :
    SetupPowers → ProbComp (Fr × GT) :=
  fun pw => positionBsdhSearch M (TrustedSetup.ofPowers pw) <$> adversary pw

/-- When the adversary wins position-binding, the search returns a BSDH solution. -/
theorem isBsdhSolutionSub_positionBsdhSearch {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ)
    {out : Bytes48 × CellOpening × CellOpening} (hw : PositionBindingWins s out) :
    IsBsdhSolutionSub M τ (positionBsdhSearch M s out) := by
  obtain ⟨hidx, hne, h, h'⟩ := hw
  obtain ⟨hci, -, C, c, -, -, -, hC, hc, -⟩ := h.valid hs
  obtain ⟨-, e, w, he, hde, hw, hv⟩ := h.valid₂ hs hC hc
  obtain ⟨-, e', w', he', hde', hw', hv'⟩ := h'.valid₂ hs hC hc
  rw [← hidx] at hv'
  have hee : e ≠ e' := fun heq => hne (cellToCosetEvals_inj he (heq ▸ he'))
  obtain ⟨sol, hsol, hsolv⟩ := findBsdh_valid M hs hci (size_bytesToBlsFields he)
    (size_bytesToBlsFields he') hee hw hw' hv hv'
  rw [positionBsdhSearch, hde, hde', hsol, Option.map_some, Option.getD_some]
  exact (isBsdhSolution_iff_sub M τ sol.1 sol.2).mp hsolv

/-- **Position-binding of the PeerDAS commitment (Lemma 3 of ePrint 2025/1683).**

Take a model of the target group.

For every adversary, the advantage is at most that of the reduction against `(4095, 64)`-BSDH.
-/
theorem positionBindingAdvantage_le {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    (adversary : SetupPowers → ProbComp (Bytes48 × CellOpening × CellOpening)) :
    positionBindingAdvantage adversary ≤ bsdhAdvantage M (positionBsdhReduction M adversary) :=
  prEvent_le_of_reduction ($ᵗ Fr) setupPowers adversary
    (fun pw => positionBsdhSearch M (TrustedSetup.ofPowers pw))
    (fun τ out => PositionBindingWins (TrustedSetup.ofPowers (setupPowers τ)) out)
    (fun τ sol => IsBsdhSolutionSub M τ sol)
    fun τ _ hw => isBsdhSolutionSub_positionBsdhSearch M (wellFormed_ofPowers τ) hw

/-! ## Code-binding, Lemma 4 -/

/-- Symbol `j` of the codeword of the polynomial `f`.

It encodes the values of `f` at the points of cell `j`, in their order. -/
noncomputable def codewordCell (f : Fr[X]) (cellIndex : Nat) : Cell :=
  cosetEvalsToCell
    (Array.ofFn fun m : Fin FIELD_ELEMENTS_PER_CELL => f.eval (cellPoint cellIndex m))

/-- The winning condition of code-binding, Definition 5 of ePrint 2025/1683.

The adversary outputs a commitment and openings at distinct cell indices.

Every opening is accepted for the commitment.

No polynomial of degree below 4096 has a codeword that agrees with every opened cell. -/
def CodeBindingWins (s : TrustedSetup) (out : Bytes48 × List CellOpening) : Prop :=
  (out.2.map (·.cellIndex)).Nodup ∧ (∀ o ∈ out.2, o.Verifies s out.1) ∧
    ¬∃ f : Fr[X], f.natDegree < FIELD_ELEMENTS_PER_BLOB ∧
      ∀ o ∈ out.2, o.cell = codewordCell f o.cellIndex

/-- **The advantage against code-binding, Definition 5 of ePrint 2025/1683.**

The secret `τ` is uniform in `Fr`, and the adversary receives its powers.

The verifier checks each opening alone, with the setup built from the powers. -/
noncomputable def codeBindingAdvantage
    (adversary : SetupPowers → ProbComp (Bytes48 × List CellOpening)) : ℝ≥0∞ :=
  Pr{let τ ← $ᵗ Fr; let out ← adversary (setupPowers τ)}[
    CodeBindingWins (TrustedSetup.ofPowers (setupPowers τ)) out]

/-- The first opening at a cell index. -/
def openingAt (os : List CellOpening) (j : Nat) : Option CellOpening :=
  os.find? (·.cellIndex == j)

/-- The values of the first opening at a cell index, or no values. -/
def openedValues (os : List CellOpening) (j : Nat) : CosetEvals :=
  ((openingAt os j).map fun o => decodeCell o.cell).getD #[]

/-- The proof point of the first opening at a cell index, or zero. -/
def openedProof (os : List CellOpening) (j : Nat) : G1 :=
  ((openingAt os j).map fun o => decodePoint o.proof).getD G1.zero

/-- The cell indices of the first 64 openings. -/
def firstCells (os : List CellOpening) : Finset Nat :=
  ((os.take FIELD_ELEMENTS_PER_CELL).map (·.cellIndex)).toFinset

open Classical in
/-- The first opening whose values the interpolation of the first 64 openings misses. -/
noncomputable def outlier (os : List CellOpening) : Option CellOpening :=
  os.find? fun o => !decide (∀ m < FIELD_ELEMENTS_PER_CELL,
    (cellsInterpolant (firstCells os) (openedValues os)).eval (cellPoint o.cellIndex m) =
      (openedValues os o.cellIndex)[m]!)

/-- The search of the first reduction from code-binding, to BSDH.

Let `I` interpolate the first 64 openings, and take the outlier.

It runs the search on the cell of the outlier and on the honest opening of that cell from `I`.

It changes the sign of `c` to the sign of ePrint 2025/1683. -/
noncomputable def codeBsdhSearch {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    (s : TrustedSetup) (out : Bytes48 × List CellOpening) : Fr × GT :=
  (((outlier out.2).bind fun o =>
      findBsdh M s o.cellIndex (openedValues out.2 o.cellIndex)
        (honestEvals (firstCells out.2) (openedValues out.2) o.cellIndex)
        (openedProof out.2 o.cellIndex)
        (honestProof s (firstCells out.2) (openedValues out.2) o.cellIndex)).map
    fun sol => (-sol.1, sol.2)).getD (0, 1)

/-- The search of the second reduction from code-binding, to ARSDH.

It joins the first 64 openings into one opening of their 4096 points. -/
noncomputable def codeArsdhSearch (s : TrustedSetup) (out : Bytes48 × List CellOpening) :
    Finset Fr × G1 × G1 :=
  arsdhCandidate s (firstCells out.2) (openedValues out.2) (decodePoint out.1) (openedProof out.2)

/-- The first reduction from code-binding, to BSDH: the adversary, then the search. -/
noncomputable def codeBsdhReduction {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    (adversary : SetupPowers → ProbComp (Bytes48 × List CellOpening)) :
    SetupPowers → ProbComp (Fr × GT) :=
  fun pw => codeBsdhSearch M (TrustedSetup.ofPowers pw) <$> adversary pw

/-- The second reduction from code-binding, to ARSDH: the adversary, then the search. -/
noncomputable def codeArsdhReduction
    (adversary : SetupPowers → ProbComp (Bytes48 × List CellOpening)) :
    SetupPowers → ProbComp (Finset Fr × G1 × G1) :=
  fun pw => codeArsdhSearch (TrustedSetup.ofPowers pw) <$> adversary pw

/-- At distinct cell indices, the first opening at the index of an opening is that opening. -/
theorem openingAt_cellIndex {os : List CellOpening} (hnd : (os.map (·.cellIndex)).Nodup)
    {o : CellOpening} (ho : o ∈ os) : openingAt os o.cellIndex = some o := by
  induction os with
  | nil => cases ho
  | cons a t ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp ho with rfl | ho'
    · simp [openingAt]
    · have hne : a.cellIndex ≠ o.cellIndex := fun h => hnd.1 (h ▸ List.mem_map_of_mem ho')
      rw [openingAt, List.find?_cons_of_neg (by simpa using hne)]
      exact ih hnd.2 ho'

/-- A cell index among the first 64 openings is the index of an opening. -/
theorem exists_of_mem_firstCells {os : List CellOpening} {j : Nat} (hj : j ∈ firstCells os) :
    ∃ o ∈ os, o.cellIndex = j := by
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
  exact ⟨o, List.mem_of_mem_take ho, rfl⟩

/-- At most 64 cells are among the first 64 openings. -/
theorem card_firstCells_le (os : List CellOpening) :
    (firstCells os).card ≤ FIELD_ELEMENTS_PER_CELL :=
  (List.toFinset_card_le _).trans (by simp)

/-- A cell that decodes to the values of `f` on its coset is symbol `j` of the codeword of `f`. -/
theorem eq_codewordCell {cell : Cell} {e : CosetEvals} (he : cellToCosetEvals cell = .ok e)
    {f : Fr[X]} {j : Nat} (hf : ∀ m < FIELD_ELEMENTS_PER_CELL, f.eval (cellPoint j m) = e[m]!) :
    cell = codewordCell f j := by
  have hsz := size_bytesToBlsFields he
  -- Open the codeword by its equation, so the kernel never compares two encodings.
  rw [codewordCell]
  refine (cosetEvalsToCell_of_cellToCosetEvals he).symm.trans (congrArg cosetEvalsToCell ?_)
  refine Array.ext (by simp [hsz]) fun m hm _ => ?_
  rw [Array.getElem_ofFn, ← getElem!_pos e m hm]
  exact (hf m (hsz ▸ hm)).symm

/-- **When the adversary wins code-binding, one of the two searches returns a solution.**

Assume a well-formed setup of the secret `τ`.

Let `I` interpolate the first 64 openings.

If `I` misses no opening, its codeword agrees with every cell, so the adversary has not won.

Otherwise the deterministic argument applies to the first 64 openings and the outlier.

Then the first search returns a BSDH solution, or the second returns an ARSDH solution. -/
theorem codeBinding_searches {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ)
    {out : Bytes48 × List CellOpening} (hw : CodeBindingWins s out) :
    IsBsdhSolutionSub M τ (codeBsdhSearch M s out) ∨
      IsArsdhSolution (FIELD_ELEMENTS_PER_BLOB - 1) τ (codeArsdhSearch s out) := by
  obtain ⟨com, os⟩ := out
  obtain ⟨hnd, hver, hno⟩ := hw
  have hidx : ∀ o ∈ os, o.cellIndex < CELLS_PER_EXT_BLOB := fun o ho =>
    ((hver o ho).valid hs).1
  have hJ : ∀ j ∈ firstCells os, j < CELLS_PER_EXT_BLOB := fun j hj => by
    obtain ⟨o, ho, rfl⟩ := exists_of_mem_firstCells hj
    exact hidx o ho
  have hdeg := natDegree_cellsInterpolant_lt hJ (card_firstCells_le os) (openedValues os)
  have hev : ∀ o ∈ os, ∃ e, cellToCosetEvals o.cell = .ok e ∧ openedValues os o.cellIndex = e :=
    fun o ho => by
      obtain ⟨-, e, -, -, -, -, he, -⟩ := (hver o ho).valid hs
      refine ⟨e, he, ?_⟩
      simp only [openedValues, openingAt_cellIndex hnd ho, Option.map_some, Option.getD_some,
        decodeCell_of_ok he]
  cases hout : outlier os with
  | none =>
    -- The interpolation of the first 64 openings agrees with every opening.
    exfalso
    refine hno ⟨cellsInterpolant (firstCells os) (openedValues os), hdeg, fun o ho => ?_⟩
    obtain ⟨e, he, hee⟩ := hev o ho
    have hc : ∀ m < FIELD_ELEMENTS_PER_CELL,
        (cellsInterpolant (firstCells os) (openedValues os)).eval (cellPoint o.cellIndex m) =
          (openedValues os o.cellIndex)[m]! := by
      simpa using List.find?_eq_none.mp hout o ho
    refine eq_codewordCell he fun m hm => ?_
    rw [← hee]
    exact hc m hm
  | some o =>
    have ho := List.mem_of_find?_eq_some hout
    have hinc : ¬∀ m < FIELD_ELEMENTS_PER_CELL,
        (cellsInterpolant (firstCells os) (openedValues os)).eval (cellPoint o.cellIndex m) =
          (openedValues os o.cellIndex)[m]! := by
      simpa using List.find?_some hout
    obtain ⟨hci, -, C, c, -, -, -, hC, hc, -⟩ := (hver o ho).valid hs
    -- Fewer than 64 openings are all among the first 64, where the interpolation agrees.
    have hJcard : (firstCells os).card = FIELD_ELEMENTS_PER_CELL := by
      by_contra hne
      have hlen : os.length < FIELD_ELEMENTS_PER_CELL := by
        by_contra hl
        refine hne ?_
        rw [firstCells, List.toFinset_card_of_nodup (by
          rw [List.map_take]
          exact hnd.sublist (List.take_sublist _ _))]
        simp only [List.length_map, List.length_take]
        omega
      have hoJ : o.cellIndex ∈ firstCells os := by
        rw [firstCells, List.take_of_length_le hlen.le]
        exact List.mem_toFinset.mpr (List.mem_map_of_mem ho)
      exact hinc fun m hm => eval_cellsInterpolant hJ _ hoJ hm
    have key : ∀ j ∈ insert o.cellIndex (firstCells os), ∃ w,
        G1.Represents (openedProof os j) w ∧
          c - (cellInterpolant j (openedValues os j)).eval τ =
            w * (τ ^ FIELD_ELEMENTS_PER_CELL - cellShift j ^ FIELD_ELEMENTS_PER_CELL) := by
      intro j hj
      obtain ⟨o', ho', rfl⟩ : ∃ o' ∈ os, o'.cellIndex = j := by
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact ⟨o, ho, rfl⟩
        · exact exists_of_mem_firstCells hj
      obtain ⟨-, e', w', he', hde', hw', hv'⟩ := (hver o' ho').valid₂ hs hC hc
      refine ⟨w', ?_, ?_⟩
      · simpa only [openedProof, openingAt_cellIndex hnd ho', Option.map_some, Option.getD_some]
          using hw'
      · rw [openedValues, openingAt_cellIndex hnd ho', Option.map_some, Option.getD_some, hde']
        exact hv'
    choose! w hw hv using key
    have hdC : G1.Represents (decodePoint com) c := by
      simpa only [decodePoint, hC] using hc
    obtain ⟨e, he, hee⟩ := hev o ho
    have hevsz : (openedValues os o.cellIndex).size = FIELD_ELEMENTS_PER_CELL :=
      hee ▸ size_bytesToBlsFields he
    rcases code_binding M hs hJ hJcard hci (openedValues os) hevsz hdC hw hv with
      h1 | ⟨sol, hsol, hsolv⟩ | h3
    · exact absurd (fun m hm => h1.2 o.cellIndex (Finset.mem_insert_self _ _) m hm) hinc
    · left
      simp only [codeBsdhSearch, hout, Option.bind_some, hsol, Option.map_some, Option.getD_some]
      exact (isBsdhSolution_iff_sub M τ sol.1 sol.2).mp hsolv
    · exact Or.inr h3

/-- **Code-binding of the PeerDAS commitment (Lemma 4 of ePrint 2025/1683).**

Take a model of the target group.

For every adversary, the advantage against code-binding is at most the sum of two advantages.

The first is that of the first reduction against `(4095, 64)`-BSDH.

The second is that of the second reduction against `(4095, 64)`-ARSDH. -/
theorem codeBindingAdvantage_le {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    (adversary : SetupPowers → ProbComp (Bytes48 × List CellOpening)) :
    codeBindingAdvantage adversary ≤
      bsdhAdvantage M (codeBsdhReduction M adversary) +
        arsdhAdvantage (codeArsdhReduction adversary) :=
  prEvent_le_add_of_reductions ($ᵗ Fr) setupPowers adversary
    (fun pw => codeBsdhSearch M (TrustedSetup.ofPowers pw))
    (fun pw => codeArsdhSearch (TrustedSetup.ofPowers pw))
    (fun τ out => CodeBindingWins (TrustedSetup.ofPowers (setupPowers τ)) out)
    (fun τ sol => IsBsdhSolutionSub M τ sol)
    (fun τ sol => IsArsdhSolution (FIELD_ELEMENTS_PER_BLOB - 1) τ sol)
    fun τ _ hw => codeBinding_searches M (wellFormed_ofPowers τ) hw

end EthLib.Cryptography.Kzg
