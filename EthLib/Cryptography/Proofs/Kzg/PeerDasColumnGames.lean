module

public import EthLib.Cryptography.Proofs.Kzg.PeerDasBatchGames

/-!
# Proofs: position-binding and code-binding of PeerDAS, with the batches of columns

A client of PeerDAS receives the cells of a block one column at a time.

It checks each column in one batch: the cells of many commitments at one cell index.

So the cells of one commitment reach it through several batches, each with its own challenge.

This file states Lemmas 3 and 4 of ePrint 2025/1683 with a verifier that checks such columns.

<https://eprint.iacr.org/2025/1683>

The adversary may query the oracle, then outputs a commitment, openings and `m` columns.

The verifier hashes each column to its challenge, one query of the oracle per column.

It accepts a column when the batch check of cells returns a verdict on it.

The challenge of the column must also be a root of its error polynomial.

For a well-formed setup, this is the batch check of cells at the challenge of the hash.

An opening counts when one of the columns holds it, for the commitment, at the index of the column.

The hash is a random oracle into `Fr` on the inputs of the core check.

That idealises SHA-256 reduced modulo `r`, the order of `Fr`, whose values are not exactly uniform.

Let each column have at most `n` cells, and let the adversary make at most `q` queries.

The bound of each lemma then grows by `(q + m) (n - 1) / r`.

That term bounds one event: a column has a nonzero error polynomial with its challenge as a root.

Otherwise every cell of every column is valid, and each opening that a column holds verifies alone.

Then the games of single cells apply.

The verifier accepts the columns of honest blobs with every challenge.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (G1 G2 Fr TargetGroup)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr
open Polynomial OracleComp OracleSpec ENNReal MeasureTheory

/-! ## Several batches with a random oracle -/

/-- The game of several batch challenges, with the hash as an oracle from `X` to `Fr`.

The adversary queries the oracle as it likes, then outputs `a`.

The verifier hashes the input `key y` of each batch `y` of `a` in turn.

It pairs each batch with its challenge. -/
def batchesRomExperiment {X Y α : Type} (key : Y → X) (batches : α → List Y)
    (adversary : OracleComp (X →ₒ Fr) α) : OracleComp (X →ₒ Fr) (α × List (Y × Fr)) := do
  let a ← adversary
  let cs ← (batches a).mapM fun y => (y, ·) <$> liftM ((X →ₒ Fr).query (key y))
  return (a, cs)

/-- The verifier makes one query per batch. -/
theorem isTotalQueryBound_challenges {X Y : Type} (key : Y → X) (l : List Y) :
    IsTotalQueryBound (l.mapM (m := OracleComp (X →ₒ Fr))
      fun y => (y, ·) <$> liftM ((X →ₒ Fr).query (key y))) l.length := by
  induction l with
  | nil => trivial
  | cons y l ih =>
    rw [List.mapM_cons, map_eq_bind_pure_comp, bind_assoc, List.length_cons, Nat.add_comm,
      isTotalQueryBound_query_bind_iff]
    refine ⟨by omega, fun _ => ?_⟩
    simp only [Function.comp_apply, pure_bind]
    rw [Nat.add_sub_cancel_left, ← Nat.add_zero l.length]
    exact isTotalQueryBound_bind ih fun _ => trivial

/-- With the answers of the table `g`, the verifier pairs each batch with `g` of its input. -/
theorem evalWithAnswerFn_challenges {X Y : Type} (key : Y → X) (l : List Y) (g : X → Fr) :
    evalWithAnswerFn (QueryImpl.ofFn g)
        (l.mapM (m := OracleComp (X →ₒ Fr)) fun y => (y, ·) <$> liftM ((X →ₒ Fr).query (key y))) =
      l.map fun y => (y, g (key y)) := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    simp [List.mapM_cons, evalWithAnswerFn_bind, evalWithAnswerFn_map, ih]

/-- With the answers of the table `g`, the verifier queries the input of each batch in turn. -/
theorem tableQueryLog_challenges {X Y : Type} (key : Y → X) (l : List Y) (g : X → Fr) :
    tableQueryLog (l.mapM (m := OracleComp (X →ₒ Fr))
        fun y => (y, ·) <$> liftM ((X →ₒ Fr).query (key y))) g =
      l.map fun y => ⟨key y, g (key y)⟩ := by
  induction l with
  | nil => simp
  | cons y l ih =>
    rw [List.mapM_cons, map_eq_bind_pure_comp, bind_assoc, tableQueryLog_query_bind]
    simp only [Function.comp_apply, pure_bind, List.map_cons, List.cons.injEq, true_and]
    rw [tableQueryLog_bind, ih, tableQueryLog_pure, List.append_nil]

/-- **An adversary of `q` queries makes a root of some batch with chance at most `(q + m) d / r`.**

The hash is a lazily sampled random oracle, and the adversary outputs at most `m` batches.

Each admissible input of a batch has an error polynomial of degree at most `d`.

The event is that some batch has an admissible input and a nonzero error polynomial.

Its challenge must also be a root of that polynomial.

The bound counts the `q` queries of the adversary and the `m` queries of the verifier. -/
theorem prEvent_batchesRomRoot_le {X Y α : Type} [DecidableEq X] (key : Y → X)
    (batches : α → List Y) (errorPoly : X → Fr[X]) (admissible : X → Prop) {d : Nat}
    (hdeg : ∀ x, admissible x → (errorPoly x).natDegree ≤ d) {m : Nat}
    (hlen : ∀ a, (batches a).length ≤ m) (adversary : OracleComp (X →ₒ Fr) α) {q : Nat}
    (hq : IsTotalQueryBound adversary q) :
    Pr{let p ← (simulateQ randomOracle (batchesRomExperiment key batches adversary)).run' ∅}[
        ∃ c ∈ p.2, admissible (key c.1) ∧ errorPoly (key c.1) ≠ 0 ∧
          (errorPoly (key c.1)).eval c.2 = 0] ≤
      (q + m) * (d / Fr.modulus) := by
  have hbound : IsTotalQueryBound (batchesRomExperiment key batches adversary) (q + m) := by
    rw [← Nat.add_zero m]
    exact isTotalQueryBound_bind hq fun a =>
      isTotalQueryBound_bind ((isTotalQueryBound_challenges key _).mono (hlen a)) fun _ => trivial
  have h := prEvent_randomOracle_le_of_bad_queries (batchesRomExperiment key batches adversary)
    (q + m) hbound
    (fun p => ∃ c ∈ p.2, admissible (key c.1) ∧ errorPoly (key c.1) ≠ 0 ∧
      (errorPoly (key c.1)).eval c.2 = 0)
    (fun x g => admissible x ∧ errorPoly x ≠ 0 ∧ (errorPoly x).eval (g x) = 0)
    (d / Fr.modulus) ?_ ?_
  · simpa using h
  · -- A new query is uniform, so it is a root with probability at most `d / r`.
    intro x g
    classical
    simp only [Function.update_self]
    by_cases ha : admissible x
    · calc _ ≤ Pr{let u ← $ᵗ Fr}[errorPoly x ≠ 0 ∧ (errorPoly x).eval u = 0] :=
            prEvent_mono _ _ _ fun _ h => h.2
        _ ≤ _ := by
          rw [SampleableType.prEvent_uniformSample, Bls.Fr.card_eq]
          gcongr
          exact_mod_cast card_roots_filter_le _ (hdeg x ha)
    · simp only [ha, false_and, prEvent_false]
      exact zero_le
  · -- A winning batch is one of the queries of the verifier.
    intro g hev
    simp only [batchesRomExperiment, evalWithAnswerFn_bind, evalWithAnswerFn_challenges,
      evalWithAnswerFn_pure, List.mem_map] at hev
    obtain ⟨_, ⟨y, hy, rfl⟩, hbad⟩ := hev
    refine ⟨⟨key y, g (key y)⟩, ?_, hbad⟩
    rw [batchesRomExperiment, tableQueryLog_bind, tableQueryLog_bind, tableQueryLog_challenges,
      evalWithAnswerFn_challenges]
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem hy))

/-! ## Columns -/

/-- **A batch of one column: the cells of many commitments at one cell index.**

Entry `k` holds a commitment, a cell and a proof, all at the one cell index. -/
structure ColumnBatch where
  commitments : Array Bytes48
  cellIndex : CellIndex
  cells : Array Cell
  proofs : Array Bytes48

/-- The inputs of the batch check of cells for a column: its cell index for every cell. -/
def ColumnBatch.toInput (c : ColumnBatch) : CellBatchInput where
  commitments := c.commitments
  cellIndices := Array.replicate c.cells.size c.cellIndex
  cells := c.cells
  proofs := c.proofs

/-- The batch check of cells on a column. -/
def ColumnBatch.verify (s : TrustedSetup) (c : ColumnBatch) : Except KzgError Bool :=
  verifyCellKzgProofBatch s c.commitments (Array.replicate c.cells.size c.cellIndex) c.cells
    c.proofs

/-- The inputs of the core check of a column, which the hash reads. -/
def ColumnBatch.key (c : ColumnBatch) : CellBatch :=
  c.toInput.toCellBatch

/-- The column holds the opening `o` for the commitment.

The column is at the cell index of the opening.

Some entry of the column has the commitment, the cell and the proof of the opening. -/
def ColumnBatch.Holds (c : ColumnBatch) (commitment : Bytes48) (o : CellOpening) : Prop :=
  c.cellIndex = o.cellIndex ∧ ∃ k < c.cells.size,
    c.commitments[k]! = commitment ∧ c.cells[k]! = o.cell ∧ c.proofs[k]! = o.proof

/-- **Every column has at most `n` cells, and is accepted with its challenge.** -/
def ColumnsAccepted (s : TrustedSetup) (τ : Fr) (n : Nat) (cs : List (ColumnBatch × Fr)) :
    Prop :=
  ∀ c ∈ cs, c.1.cells.size ≤ n ∧ c.1.toInput.AcceptsAt s τ c.2

/-- **The challenge of some column is a root of its error polynomial, which is not zero.**

That column has at most `n` cells. -/
def ColumnRoot (τ : Fr) (n : Nat) (cs : List (ColumnBatch × Fr)) : Prop :=
  ∃ c ∈ cs, c.1.key.cellIndices.size ≤ n ∧ c.1.key.errorPoly τ scalarOf scalarOf ≠ 0 ∧
    (c.1.key.errorPoly τ scalarOf scalarOf).eval c.2 = 0

/-- Entry `k` of an array of copies of `a` is `a`. -/
theorem getElem!_replicate {α : Type} [Inhabited α] {n k : Nat} (a : α) (hk : k < n) :
    (Array.replicate n a)[k]! = a := by
  rw [getElem!_pos _ k (by simpa using hk)]
  simp

/-- **A column with a zero error polynomial holds only openings that verify alone.**

Assume a well-formed setup of the secret `τ`.

Let the batch check of cells return a verdict on the column.

Let the error polynomial of the column be zero, where each point has the scalar of its bytes.

Then every opening that the column holds verifies alone for its commitment. -/
theorem ColumnBatch.verifies_of_holds {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {c : ColumnBatch} {x : Fr} (ha : c.toInput.AcceptsAt s τ x)
    (hz : c.key.errorPoly τ scalarOf scalarOf = 0) {commitment : Bytes48} {o : CellOpening}
    (hh : c.Holds commitment o) : o.Verifies s commitment := by
  obtain ⟨⟨b, hb⟩, -⟩ := ha
  obtain ⟨hi, k, hk, hC, hcell, hproof⟩ := hh
  obtain ⟨h₁, -⟩ := verifyCellKzgProofBatch_eq_ok hb
  have hv := cellOpeningValid_of_errorPoly_eq_zero hb hz (k := k)
    (by simp only [ColumnBatch.toInput] at h₁ ⊢; omega)
  simp only [ColumnBatch.toInput, getElem!_replicate _ hk] at hv
  rw [hC, hcell, hproof, hi] at hv
  exact (CellOpening.verifies_iff hs).mpr hv

/-- **Accepted columns hold only openings that verify alone, or a challenge is a root.**

Assume a well-formed setup of the secret `τ`.

Let every column have at most `n` cells and be accepted with its challenge.

Then every opening that a column holds verifies alone for its commitment.

Otherwise the challenge of some column is a root of its error polynomial, which is not zero. -/
theorem columnsAccepted_cases {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {n : Nat} {cs : List (ColumnBatch × Fr)}
    (h : ColumnsAccepted s τ n cs) :
    (∀ c ∈ cs, ∀ commitment o, c.1.Holds commitment o → o.Verifies s commitment) ∨
      ColumnRoot τ n cs := by
  by_cases hz : ∃ c ∈ cs, c.1.key.errorPoly τ scalarOf scalarOf ≠ 0
  · obtain ⟨c, hc, hne⟩ := hz
    obtain ⟨hn, -, hr⟩ := h c hc
    refine Or.inr ⟨c, hc, ?_, hne, hr⟩
    simpa [ColumnBatch.key, CellBatchInput.toCellBatch, ColumnBatch.toInput] using hn
  · simp only [not_exists, not_and, not_not] at hz
    exact Or.inl fun c hc _ _ hh => ColumnBatch.verifies_of_holds hs (h c hc).2 (hz c hc) hh

/-- **The verifier accepts a column of honest blobs with every challenge.**

Take a well-formed setup of the secret `τ`, and a column at a cell index below 128.

Let each entry of the column come from a blob.

Its commitment is the commitment of its blob.

Its cell and its proof are those of the blob at the cell index of the column.

Then the column is accepted with every challenge `x`. -/
theorem ColumnBatch.acceptsAt_computeCellsAndKzgProofs {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {c : ColumnBatch} (h₁ : c.cells.size = c.commitments.size)
    (h₂ : c.proofs.size = c.commitments.size) (hj : c.cellIndex < CELLS_PER_EXT_BLOB)
    (hblobs : ∀ k < c.commitments.size, ∃ blob cs qs,
      blobToKzgCommitment s blob = .ok c.commitments[k]! ∧
      computeCellsAndKzgProofs s blob = .ok (cs, qs) ∧
      c.cells[k]! = cs[c.cellIndex]! ∧ c.proofs[k]! = qs[c.cellIndex]!)
    (x : Fr) : c.toInput.AcceptsAt s τ x := by
  refine CellBatchInput.acceptsAt_of_cellOpeningValid h₁ h₂ (by simpa [ColumnBatch.toInput])
    (fun k hk => ?_) x
  obtain ⟨blob, cs, qs, hC, hP, hcell, hproof⟩ := hblobs k hk
  simp only [ColumnBatch.toInput, getElem!_replicate _ (h₁ ▸ hk : k < c.cells.size)]
  rw [hcell, hproof]
  exact cellOpeningValid_computeCellsAndKzgProofs hs hC hP hj

/-- **At the challenge of its hash, the check of a column is the batch check of cells.**

Assume a well-formed setup of the secret `τ`.

A column is accepted with the challenge of its hash exactly when the batch check accepts it. -/
theorem ColumnBatch.acceptsAt_challenge_iff {s : TrustedSetup}
    {τ : Fr} (hs : s.WellFormed τ) (c : ColumnBatch) :
    c.toInput.AcceptsAt s τ c.key.challenge ↔ c.verify s = .ok true :=
  CellBatchInput.acceptsAt_challenge_iff hs c.toInput

/-! ## The games -/

/-- **The union bound for one reduction and a bad event.**

When the adversary wins, the reduction wins on the same run, or a bad event holds.

So the adversary wins with probability at most the sum for the reduction and the bad event. -/
theorem prEvent_le_add_of_reduction_or_bad {S I O A : Type} (sample : ProbComp S) (input : S → I)
    (adversary : I → ProbComp O) (f : I → O → A) (win : S → O → Prop) (p : S → A → Prop)
    (bad : S → O → Prop) (h : ∀ s o, win s o → p s (f (input s) o) ∨ bad s o) :
    Pr{let s ← sample; let o ← adversary (input s)}[win s o] ≤
      Pr{let s ← sample; let a ← f (input s) <$> adversary (input s)}[p s a] +
        Pr{let s ← sample; let o ← adversary (input s)}[bad s o] := by
  let _ : MeasurableSpace S := ⊤
  have _ : DiscreteMeasurableSpace S := ⟨fun _ => trivial⟩
  rw [prEvent_bind_bind_eq_lintegral_of_discrete, prEvent_bind_bind_eq_lintegral_of_discrete,
    prEvent_bind_bind_eq_lintegral_of_discrete, ← lintegral_add_left Measurable.of_discrete]
  refine lintegral_mono fun s => ?_
  rw [prEvent_map]
  exact (prEvent_mono _ _ _ (h s)).trans (prEvent_or_le _ _ _)

/-- The experiment of the games of columns, with the oracle answered at random.

The adversary outputs `a`, and the verifier hashes each of the `m` columns of `a`. -/
noncomputable def columnsRun {α : Type} {m : Nat} (columns : α → Vector ColumnBatch m)
    (adversary : SetupPowers → OracleComp (CellBatch →ₒ Fr) α) (pw : SetupPowers) :
    ProbComp (α × List (ColumnBatch × Fr)) :=
  (simulateQ randomOracle
    (batchesRomExperiment ColumnBatch.key (fun a => (columns a).toList) (adversary pw))).run' ∅

/-- **For each secret, a root of some column has probability at most `(q + m) (n - 1) / r`.**

The adversary makes at most `q` queries and outputs `m` columns.

The event asks that the column has at most `n` cells. -/
theorem prEvent_columnsRun_root_le {α : Type} {m : Nat} (columns : α → Vector ColumnBatch m)
    (adversary : SetupPowers → OracleComp (CellBatch →ₒ Fr) α) {q : Nat}
    (hq : ∀ pw, IsTotalQueryBound (adversary pw) q) (n : Nat) (τ : Fr) (pw : SetupPowers) :
    Pr{let p ← columnsRun columns adversary pw}[ColumnRoot τ n p.2] ≤
      (q + m) * ((n - 1 : Nat) / Fr.modulus) :=
  prEvent_batchesRomRoot_le ColumnBatch.key (fun a => (columns a).toList)
    (fun x => x.errorPoly τ scalarOf scalarOf) (fun x => x.cellIndices.size ≤ n)
    (fun _ hx => (natDegree_errorPoly_le _ _).trans (Nat.sub_le_sub_right hx 1))
    (fun _ => Vector.length_toList.le) (adversary pw) (hq pw)

/-! ## Position-binding, Lemma 3 -/

/-- **The winning condition of position-binding, with the batches of columns.**

The adversary outputs a commitment, two openings and columns.

The two openings are at one cell index, with different cells.

Every column has at most `n` cells and is accepted with its challenge from the oracle.

Some column holds the first opening for the commitment, and some column holds the second. -/
def ColumnPositionBindingWins (s : TrustedSetup) (τ : Fr) (n : Nat) {m : Nat}
    (p : (Bytes48 × (CellOpening × CellOpening) × Vector ColumnBatch m) ×
      List (ColumnBatch × Fr)) : Prop :=
  p.1.2.1.1.cellIndex = p.1.2.1.2.cellIndex ∧ p.1.2.1.1.cell ≠ p.1.2.1.2.cell ∧
    ColumnsAccepted s τ n p.2 ∧ (∃ c ∈ p.2, c.1.Holds p.1.1 p.1.2.1.1) ∧
    ∃ c ∈ p.2, c.1.Holds p.1.1 p.1.2.1.2

/-- **The advantage against position-binding, with the batches of columns.**

The secret `τ` is uniform in `Fr`, and the adversary receives its powers.

The verifier checks each column in one batch, with the setup built from the powers. -/
noncomputable def columnPositionBindingAdvantage (n : Nat) {m : Nat}
    (adversary : SetupPowers →
      OracleComp (CellBatch →ₒ Fr) (Bytes48 × (CellOpening × CellOpening) × Vector ColumnBatch m)) :
    ℝ≥0∞ :=
  Pr{let τ ← $ᵗ Fr; let p ← columnsRun (·.2.2) adversary (setupPowers τ)}[
    ColumnPositionBindingWins (TrustedSetup.ofPowers (setupPowers τ)) τ n p]

/-- The reduction from position-binding with columns to BSDH.

It runs the experiment, answering the oracle itself, then the search of Lemma 3. -/
noncomputable def columnPositionBsdhReduction {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    {m : Nat}
    (adversary : SetupPowers →
      OracleComp (CellBatch →ₒ Fr) (Bytes48 × (CellOpening × CellOpening) × Vector ColumnBatch m)) :
    SetupPowers → ProbComp (Fr × GT) :=
  fun pw => (fun p => positionBsdhSearch M (TrustedSetup.ofPowers pw) (p.1.1, p.1.2.1)) <$>
    columnsRun (·.2.2) adversary pw

/-- **When the adversary wins position-binding with columns, the search wins or a root occurs.**

Assume a well-formed setup of the secret `τ`. -/
theorem columnPositionBinding_cases {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ) {n m : Nat}
    {p : (Bytes48 × (CellOpening × CellOpening) × Vector ColumnBatch m) ×
      List (ColumnBatch × Fr)}
    (hw : ColumnPositionBindingWins s τ n p) :
    IsBsdhSolutionSub M τ (positionBsdhSearch M s (p.1.1, p.1.2.1)) ∨ ColumnRoot τ n p.2 := by
  obtain ⟨hidx, hne, hacc, ⟨c, hc, hh⟩, ⟨c', hc', hh'⟩⟩ := hw
  rcases columnsAccepted_cases hs hacc with hall | hroot
  · exact Or.inl (isBsdhSolutionSub_positionBsdhSearch M hs
      ⟨hidx, hne, hall c hc _ _ hh, hall c' hc' _ _ hh'⟩)
  · exact Or.inr hroot

/-- **Position-binding of PeerDAS, with the batches of columns.**

Take a model of the target group.

Let the adversary make at most `q` queries to the random oracle, and output `m` columns.

Its advantage is at most the sum of two terms.

- The advantage of the reduction against `(4095, 64)`-BSDH.
- `(q + m) (n - 1) / r`, for a challenge that is a root of a nonzero error polynomial.

Here `r` is the order of `Fr`, and the term `m` counts the queries of the verifier. -/
theorem columnPositionBindingAdvantage_le {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    (n : Nat) {m : Nat}
    (adversary : SetupPowers →
      OracleComp (CellBatch →ₒ Fr) (Bytes48 × (CellOpening × CellOpening) × Vector ColumnBatch m))
    {q : Nat} (hq : ∀ pw, IsTotalQueryBound (adversary pw) q) :
    columnPositionBindingAdvantage n adversary ≤
      bsdhAdvantage M (columnPositionBsdhReduction M adversary) +
        (q + m) * ((n - 1 : Nat) / Fr.modulus) := by
  have h := prEvent_le_add_of_reduction_or_bad ($ᵗ Fr) setupPowers (columnsRun (·.2.2) adversary)
    (fun pw p => positionBsdhSearch M (TrustedSetup.ofPowers pw) (p.1.1, p.1.2.1))
    (fun τ p => ColumnPositionBindingWins (TrustedSetup.ofPowers (setupPowers τ)) τ n p)
    (fun τ sol => IsBsdhSolutionSub M τ sol) (fun τ p => ColumnRoot τ n p.2)
    fun τ _ hw => columnPositionBinding_cases M (wellFormed_ofPowers τ) hw
  have hroot := prEvent_bind_le_of_forall ($ᵗ Fr)
    (fun τ => columnsRun (·.2.2) adversary (setupPowers τ)) (fun τ p => ColumnRoot τ n p.2)
    fun τ => prEvent_columnsRun_root_le _ adversary hq n τ (setupPowers τ)
  exact h.trans (add_le_add le_rfl hroot)

/-! ## Code-binding, Lemma 4 -/

/-- **The winning condition of code-binding, with the batches of columns.**

The adversary outputs a commitment, openings at distinct cell indices, and columns.

Every column has at most `n` cells and is accepted with its challenge from the oracle.

Some column holds each opening for the commitment.

No polynomial of degree below 4096 has a codeword that agrees with every opened cell. -/
def ColumnCodeBindingWins (s : TrustedSetup) (τ : Fr) (n : Nat) {m : Nat}
    (p : (Bytes48 × List CellOpening × Vector ColumnBatch m) × List (ColumnBatch × Fr)) :
    Prop :=
  (p.1.2.1.map (·.cellIndex)).Nodup ∧ ColumnsAccepted s τ n p.2 ∧
    (∀ o ∈ p.1.2.1, ∃ c ∈ p.2, c.1.Holds p.1.1 o) ∧
    ¬∃ f : Fr[X], f.natDegree < FIELD_ELEMENTS_PER_BLOB ∧
      ∀ o ∈ p.1.2.1, o.cell = codewordCell f o.cellIndex

/-- **The advantage against code-binding, with the batches of columns.**

The secret `τ` is uniform in `Fr`, and the adversary receives its powers.

The verifier checks each column in one batch, with the setup built from the powers. -/
noncomputable def columnCodeBindingAdvantage (n : Nat) {m : Nat}
    (adversary : SetupPowers →
      OracleComp (CellBatch →ₒ Fr) (Bytes48 × List CellOpening × Vector ColumnBatch m)) :
    ℝ≥0∞ :=
  Pr{let τ ← $ᵗ Fr; let p ← columnsRun (·.2.2) adversary (setupPowers τ)}[
    ColumnCodeBindingWins (TrustedSetup.ofPowers (setupPowers τ)) τ n p]

/-- The first reduction from code-binding with columns, to BSDH.

It runs the experiment, answering the oracle itself, then the search of Lemma 4. -/
noncomputable def columnCodeBsdhReduction {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    {m : Nat}
    (adversary : SetupPowers →
      OracleComp (CellBatch →ₒ Fr) (Bytes48 × List CellOpening × Vector ColumnBatch m)) :
    SetupPowers → ProbComp (Fr × GT) :=
  fun pw => (fun p => codeBsdhSearch M (TrustedSetup.ofPowers pw) (p.1.1, p.1.2.1)) <$>
    columnsRun (·.2.2) adversary pw

/-- The second reduction from code-binding with columns, to ARSDH.

It runs the experiment, answering the oracle itself, then the search of Lemma 4. -/
noncomputable def columnCodeArsdhReduction {m : Nat}
    (adversary : SetupPowers →
      OracleComp (CellBatch →ₒ Fr) (Bytes48 × List CellOpening × Vector ColumnBatch m)) :
    SetupPowers → ProbComp (Finset Fr × G1 × G1) :=
  fun pw => (fun p => codeArsdhSearch (TrustedSetup.ofPowers pw) (p.1.1, p.1.2.1)) <$>
    columnsRun (·.2.2) adversary pw

/-- **When the adversary wins code-binding with columns, a search wins or a challenge is a root.**

Assume a well-formed setup of the secret `τ`.

If no challenge is a root, every opening verifies alone.

Then the adversary wins code-binding with cells checked alone.

Then one of the two searches of Lemma 4 returns a solution. -/
theorem columnCodeBinding_cases {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ) {n m : Nat}
    {p : (Bytes48 × List CellOpening × Vector ColumnBatch m) × List (ColumnBatch × Fr)}
    (hw : ColumnCodeBindingWins s τ n p) :
    IsBsdhSolutionSub M τ (codeBsdhSearch M s (p.1.1, p.1.2.1)) ∨
      IsArsdhSolution (FIELD_ELEMENTS_PER_BLOB - 1) τ (codeArsdhSearch s (p.1.1, p.1.2.1)) ∨
      ColumnRoot τ n p.2 := by
  obtain ⟨hnd, hacc, hheld, hno⟩ := hw
  rcases columnsAccepted_cases hs hacc with hall | hroot
  · have hwin : CodeBindingWins s (p.1.1, p.1.2.1) := by
      refine ⟨hnd, fun o ho => ?_, hno⟩
      obtain ⟨c, hc, hh⟩ := hheld o ho
      exact hall c hc _ _ hh
    rcases codeBinding_searches M hs hwin with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr hroot)

/-- **Code-binding of PeerDAS, with the batches of columns.**

Take a model of the target group.

Let the adversary make at most `q` queries to the random oracle, and output `m` columns.

Its advantage is at most the sum of three terms.

- The advantage of the first reduction against `(4095, 64)`-BSDH.
- The advantage of the second reduction against `(4095, 64)`-ARSDH.
- `(q + m) (n - 1) / r`, for a challenge that is a root of a nonzero error polynomial.

Here `r` is the order of `Fr`, and the term `m` counts the queries of the verifier. -/
theorem columnCodeBindingAdvantage_le {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    (n : Nat) {m : Nat}
    (adversary : SetupPowers →
      OracleComp (CellBatch →ₒ Fr) (Bytes48 × List CellOpening × Vector ColumnBatch m))
    {q : Nat} (hq : ∀ pw, IsTotalQueryBound (adversary pw) q) :
    columnCodeBindingAdvantage n adversary ≤
      bsdhAdvantage M (columnCodeBsdhReduction M adversary) +
        arsdhAdvantage (columnCodeArsdhReduction adversary) +
          (q + m) * ((n - 1 : Nat) / Fr.modulus) :=
  (prEvent_le_add_add_of_reductions ($ᵗ Fr) setupPowers (columnsRun (·.2.2) adversary)
    (fun pw p => codeBsdhSearch M (TrustedSetup.ofPowers pw) (p.1.1, p.1.2.1))
    (fun pw p => codeArsdhSearch (TrustedSetup.ofPowers pw) (p.1.1, p.1.2.1))
    (fun τ p => ColumnCodeBindingWins (TrustedSetup.ofPowers (setupPowers τ)) τ n p)
    (fun τ sol => IsBsdhSolutionSub M τ sol)
    (fun τ sol => IsArsdhSolution (FIELD_ELEMENTS_PER_BLOB - 1) τ sol)
    (fun τ p => ColumnRoot τ n p.2)
    fun τ _ hw => columnCodeBinding_cases M (wellFormed_ofPowers τ) hw).trans
      (add_le_add le_rfl (prEvent_bind_le_of_forall _ _ _ fun τ =>
        prEvent_columnsRun_root_le _ adversary hq n τ (setupPowers τ)))

end EthLib.Cryptography.Kzg
