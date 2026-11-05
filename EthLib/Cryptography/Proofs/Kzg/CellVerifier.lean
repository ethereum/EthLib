module

public import EthLib.Cryptography.Proofs.Kzg.CellBinding

/-!
# Proofs: the outer batch check of cells

The outer check takes one commitment per cell, as bytes.

It keeps the first copy of each commitment, and gives each cell the index of its commitment.

It then decodes the cells and runs the core check on these inputs.

So an accepted outer check is an accepted core check.

The theorems of the core check then hold for the outer check, each cell with its own commitment.

- An accepted batch has every cell valid, or its challenge is a root of a nonzero polynomial.
- Two cells at one index, with commitments of one scalar, are equal.
  Otherwise a search returns a bilinear strong Diffie–Hellman solution, or the challenge is a root.
- With the hash a random oracle, the root case has probability at most `(q + 1) (n - 1) / r`.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (G1 G2 Fr TargetGroup)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr
open Polynomial

/-! ## The removal of repeated commitments -/

/-- One step of the removal of repeated commitments. -/
def dedupStep (acc : Array KZGCommitment × Array CommitmentIndex) (b : Bytes48) :
    Array KZGCommitment × Array CommitmentIndex :=
  match acc.1.idxOf? b with
  | some j => (acc.1, acc.2.push j)
  | none => (acc.1.push b, acc.2.push acc.1.size)

/-- The removal of repeated commitments.

It returns the commitments in order of first appearance, and the index of each input among them. -/
def dedupCommitments (bs : Array Bytes48) : Array KZGCommitment × Array CommitmentIndex :=
  bs.foldl dedupStep (#[], #[])

/-- An index found by the search holds the searched commitment. -/
private theorem idxOf?_eq_some_spec {d : Array Bytes48} {b : Bytes48} {j : Nat}
    (h : d.idxOf? b = some j) : j < d.size ∧ d[j]! = b := by
  rw [Array.idxOf?_eq_map_finIdxOf?_val] at h
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
  have := (Array.finIdxOf?_eq_some_iff.mp hi).1
  exact ⟨i.isLt, by rw [getElem!_pos d i.val i.isLt]; exact this⟩

/-- Entry `i` of an array with one more element. -/
private theorem getElem!_push' {α : Type} [Inhabited α] (xs : Array α) (x : α) (i : Nat) :
    (xs.push x)[i]! = if i = xs.size then x else xs[i]! := by
  simp only [getElem!_def, Array.getElem?_push]
  by_cases h : i = xs.size <;> simp [h]

/-- The removal keeps one index per commitment, and each index points to that commitment.

Each kept commitment is also one of the input commitments. -/
theorem dedupCommitments_spec (bs : Array Bytes48) :
    (dedupCommitments bs).2.size = bs.size ∧
      (∀ k < bs.size, (dedupCommitments bs).2[k]! < (dedupCommitments bs).1.size ∧
        (dedupCommitments bs).1[(dedupCommitments bs).2[k]!]! = bs[k]!) ∧
      ∀ i < (dedupCommitments bs).1.size, ∃ k < bs.size,
        bs[k]! = (dedupCommitments bs).1[i]! := by
  unfold dedupCommitments
  refine Array.foldl_induction
    (motive := fun n (acc : Array KZGCommitment × Array CommitmentIndex) =>
      acc.2.size = n ∧ (∀ k < n, acc.2[k]! < acc.1.size ∧ acc.1[acc.2[k]!]! = bs[k]!) ∧
        ∀ i < acc.1.size, ∃ k < n, bs[k]! = acc.1[i]!)
    ⟨rfl, by simp, by simp⟩ ?_
  intro n acc ⟨hsz, hidx, hmem⟩
  have hbn : bs[n] = bs[n.val]! := (getElem!_pos bs n.val n.isLt).symm
  unfold dedupStep
  split
  · rename_i j hj
    obtain ⟨hj, hjb⟩ := idxOf?_eq_some_spec hj
    refine ⟨by simp [hsz], fun k hk => ?_, fun i hi => ?_⟩
    · rw [getElem!_push']
      split
      · exact ⟨hj, by rw [hjb, hbn]; congr; omega⟩
      · exact hidx k (by omega)
    · obtain ⟨k, hk, h⟩ := hmem i hi
      exact ⟨k, by omega, h⟩
  · refine ⟨by simp [hsz], fun k hk => ?_, fun i hi => ?_⟩
    · rw [getElem!_push', Array.size_push]
      by_cases hkn : k = acc.2.size
      · rw [ite_eq_left hkn, getElem!_push', ite_eq_left rfl, hbn, hkn, hsz]
        exact ⟨Nat.lt_succ_self _, rfl⟩
      · obtain ⟨h1, h2⟩ := hidx k (by omega)
        have hne : acc.2[k]! ≠ acc.1.size := Nat.ne_of_lt h1
        rw [ite_eq_right hkn, getElem!_push', ite_eq_right hne]
        exact ⟨Nat.lt_succ_of_lt h1, h2⟩
    · rw [getElem!_push']
      rw [Array.size_push] at hi
      split
      · exact ⟨n, by omega, hbn.symm⟩
      · obtain ⟨k, hk, h⟩ := hmem i (by omega)
        exact ⟨k, by omega, h⟩

/-! ## The outer check as the core check -/

/-- A fold that fails or takes the step of the removal returns the removal. -/
theorem foldlM_eq_ok_dedup {ε : Type}
    {f : Array KZGCommitment × Array CommitmentIndex → Bytes48 × Nat →
      Except ε (Array KZGCommitment × Array CommitmentIndex)}
    (hf : ∀ acc p r, f acc p = .ok r → r = dedupStep acc p.1) :
    ∀ (L : List (Bytes48 × Nat)) init r, L.foldlM f init = .ok r →
      r = L.foldl (fun acc p => dedupStep acc p.1) init
  | [], init, r, h => by cases h; rfl
  | p :: L, init, r, h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    cases hp : f init p with
    | error e => rw [hp] at h; cases h
    | ok r' =>
      rw [hp] at h
      rw [List.foldl_cons, ← hf init p r' hp]
      exact foldlM_eq_ok_dedup hf L r' r h

/-- The removal in the batch check of cells returns the removal of repeated commitments. -/
theorem zipIdx_foldlM_eq_ok_dedup {ε : Type}
    {f : Array KZGCommitment × Array CommitmentIndex → Bytes48 × Nat →
      Except ε (Array KZGCommitment × Array CommitmentIndex)}
    (hf : ∀ acc p r, f acc p = .ok r → r = dedupStep acc p.1) {bs : Array Bytes48}
    {r : Array KZGCommitment × Array CommitmentIndex}
    (h : bs.zipIdx.foldlM f (#[], #[]) = .ok r) : r = dedupCommitments bs := by
  rw [← Array.foldlM_toList] at h
  rw [foldlM_eq_ok_dedup hf _ _ r h, dedupCommitments, ← Array.foldl_toList,
    Array.toList_zipIdx, ← List.foldl_map (f := Prod.fst) (g := dedupStep), List.zipIdx_map_fst]

/-- A map that validates each proof and returns it gives back the proofs. -/
theorem zipIdx_mapM_eq_ok {ε : Type} {g : Bytes48 × Nat → Except ε Bytes48}
    (hg : ∀ p r, g p = .ok r → r = p.1) {ps qs : Array Bytes48}
    (h : ps.zipIdx.mapM g = .ok qs) : qs = ps := by
  obtain ⟨hsz, hk⟩ := array_mapM_ok h
  rw [Array.size_zipIdx] at hsz
  refine Array.ext hsz fun i hi hi' => ?_
  have := hg _ _ (hk i (by rw [Array.size_zipIdx]; exact hi'))
  rw [← getElem!_pos qs i hi, ← getElem!_pos ps i hi', this,
    getElem!_pos _ i (by rw [Array.size_zipIdx]; exact hi'), Array.getElem_zipIdx]
  exact (getElem!_pos ps i hi').symm

/-- **An accepted outer check is an accepted core check.**

The cells, the proofs and the cell indices are as many as the commitments.

Each cell index is below 128, and each cell decodes to field elements.

The core check accepts the commitments without repeats, with the index of each cell's commitment.
-/
theorem verifyCellKzgProofBatch_eq_ok {setup : TrustedSetup} {bs : Array Bytes48}
    {cellIndices : Array CellIndex} {cells : Array Cell} {ps : Array Bytes48} {b : Bool}
    (h : verifyCellKzgProofBatch setup bs cellIndices cells ps = .ok b) :
    cells.size = bs.size ∧ ps.size = bs.size ∧ cellIndices.size = bs.size ∧
      (∀ k < cellIndices.size, cellIndices[k]! < CELLS_PER_EXT_BLOB) ∧
      ∃ evals, cells.mapM cellToCosetEvals = .ok evals ∧
        verifyCellKzgProofBatchImpl setup (dedupCommitments bs).1 (dedupCommitments bs).2
          cellIndices evals ps = .ok b := by
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
  rename_i evals hevals
  split at h
  · cases h
  rename_i qs hqs
  have hdd' := zipIdx_foldlM_eq_ok_dedup (fun acc p r hr => by
    unfold dedupStep
    cases hb : bytesToKzgCommitment p.1 <;> cases hi : acc.1.idxOf? p.1 <;>
      simp [hb, hi, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hr ⊢ <;>
      exact hr.symm) hdd
  have hqs' := zipIdx_mapM_eq_ok (fun p r hr => by
    cases hb : bytesToKzgProof p.1 <;>
      simp [hb, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hr
    rw [← hr]
    unfold bytesToKzgProof at hb
    split at hb <;> cases hb
    rfl) hqs
  subst hdd' hqs'
  refine ⟨h₁, h₂, h₃, fun k hk => ?_, evals, hevals, h⟩
  have hk' := Array.any_eq_false'.mp h₄ _ (Array.getElem_mem hk)
  rw [getElem!_pos cellIndices k hk]
  simpa using hk'

/-- A core check that returns decodes its commitments and its proofs. -/
theorem verifyCellKzgProofBatchImpl_decodes {s : TrustedSetup}
    {commitments : Array KZGCommitment} {commitmentIndices : Array CommitmentIndex}
    {cellIndices : Array CellIndex} {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    {b : Bool} (h : verifyCellKzgProofBatchImpl s commitments commitmentIndices cellIndices
      cosetsEvals proofs = .ok b) :
    (∃ G, commitments.mapM uncompressG1 = .ok G) ∧ ∃ G, proofs.mapM uncompressG1 = .ok G := by
  unfold verifyCellKzgProofBatchImpl at h
  constructor
  · cases hC : commitments.mapM uncompressG1 with
    | ok G => exact ⟨G, rfl⟩
    | error e =>
      exfalso
      simp only [hC, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
      repeat' split at h
      all_goals cases h
  · cases hP : proofs.mapM uncompressG1 with
    | ok G => exact ⟨G, rfl⟩
    | error e =>
      exfalso
      simp only [hP, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
      repeat' split at h
      all_goals cases h

/-! ## The decoding of cells -/

/-- A decoded field element encodes back to its bytes. -/
theorem blsFieldToBytes_of_bytesToBlsField {b : Base.Bytes32} {f : Fr}
    (h : bytesToBlsField b = .ok f) : blsFieldToBytes f = b := by
  have hval := (bytesToBlsField_ok h).1
  have hval' := (bytesToBlsField_ok (bytesToBlsField_blsFieldToBytes f)).1
  have harr : (⟨(blsFieldToBytes f).toArray⟩ : ByteArray) = ⟨b.toArray⟩ := by
    -- Both byte strings have 32 bytes and decode to the value of `f`.
    have h32 : (⟨b.toArray⟩ : ByteArray).size = 32 := by simp [ByteArray.size]
    have h32' : (⟨(blsFieldToBytes f).toArray⟩ : ByteArray).size = 32 := by
      simp [ByteArray.size]
    have e := intToBytesBE_bytesBEToNat (⟨b.toArray⟩ : ByteArray)
    have e' := intToBytesBE_bytesBEToNat (⟨(blsFieldToBytes f).toArray⟩ : ByteArray)
    rw [h32, ← hval] at e
    rw [h32', ← hval'] at e'
    rw [← e, ← e']
  apply Vector.toArray_inj.mp
  exact congrArg ByteArray.data harr

/-- Two byte strings with the same field-element chunks are equal. -/
theorem eq_of_fieldElementBytes {k : Nat} {x y : Vector UInt8 (k * BYTES_PER_FIELD_ELEMENT)}
    (h : ∀ i, fieldElementBytes x i = fieldElementBytes y i) : x = y := by
  apply Vector.ext
  intro j hj
  have hi : j / BYTES_PER_FIELD_ELEMENT < k := by
    simp only [BYTES_PER_FIELD_ELEMENT] at hj ⊢
    omega
  have hm : j % BYTES_PER_FIELD_ELEMENT < BYTES_PER_FIELD_ELEMENT := Nat.mod_lt _ (by decide)
  have hj' := congrArg (fun v : Base.Bytes32 => v[j % BYTES_PER_FIELD_ELEMENT]'hm) (h ⟨_, hi⟩)
  simp only [fieldElementBytes, Vector.getElem_ofFn, Nat.div_add_mod'] at hj'
  exact hj'

/-- A cell is the encoding of the values it decodes to. -/
theorem cosetEvalsToCell_of_cellToCosetEvals {a : Cell} {e : CosetEvals}
    (h : cellToCosetEvals a = .ok e) : cosetEvalsToCell e = a := by
  have hsz := size_bytesToBlsFields h
  apply eq_of_fieldElementBytes (k := FIELD_ELEMENTS_PER_CELL)
  intro i
  rw [cosetEvalsToCell, fieldElementBytes_flatten]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  rw [getElem!_pos e i.val (by rw [hsz]; exact i.isLt)]
  exact blsFieldToBytes_of_bytesToBlsField (getElem_bytesToBlsFields h i)

/-- Two cells that decode to the same values are equal. -/
theorem cellToCosetEvals_inj {a a' : Cell} {e : CosetEvals} (h : cellToCosetEvals a = .ok e)
    (h' : cellToCosetEvals a' = .ok e) : a = a' :=
  (cosetEvalsToCell_of_cellToCosetEvals h).symm.trans (cosetEvalsToCell_of_cellToCosetEvals h')

/-! ## Validity and binding of the outer check -/

/-- The inputs of the outer batch check of cells, as the caller gives them. -/
structure CellBatchInput where
  commitments : Array Bytes48
  cellIndices : Array CellIndex
  cells : Array Cell
  proofs : Array Bytes48

/-- The values of the cells, or no values if some cell does not decode. -/
def decodeCells (cells : Array Cell) : Array CosetEvals :=
  match cells.mapM cellToCosetEvals with
  | .ok evals => evals
  | .error _ => #[]

/-- The inputs that the outer check passes to the core check, which hashes them. -/
def CellBatchInput.toCellBatch (y : CellBatchInput) : CellBatch where
  commitments := (dedupCommitments y.commitments).1
  commitmentIndices := (dedupCommitments y.commitments).2
  cellIndices := y.cellIndices
  cosetsEvals := decodeCells y.cells
  proofs := y.proofs

/-- The challenge of the batch check of cells. -/
def CellBatch.challenge (x : CellBatch) : Fr :=
  computeVerifyCellKzgProofBatchChallenge x.commitments x.commitmentIndices x.cellIndices
    x.cosetsEvals x.proofs

/-- The error polynomial of a batch, where `c` and `w` give the scalars of the points.

Cell `k` has the scalar of its commitment's bytes and the scalar of its proof's bytes. -/
noncomputable def CellBatch.errorPoly (x : CellBatch) (τ : Fr) (c w : Bytes48 → Fr) : Fr[X] :=
  cellErrorPoly τ (fun i => c x.commitments[i]!) (fun k => w x.proofs[k]!) x.commitmentIndices
    x.cellIndices x.cosetsEvals

/-- **An accepted batch of cells is valid, or its challenge is a root.**

Assume the pairing law and a well-formed setup of the secret `τ`.

Let each commitment decode to a point that represents the scalar `c` of its bytes.

Let each proof decode to a point that represents the scalar `w` of its bytes.

If the outer check accepts, then every cell is valid for its own commitment.

Otherwise the error polynomial of the batch is not zero, and the challenge is one of its roots. -/
theorem verifyCellKzgProofBatch_valid_or_root (laws : Bls.PairingLaws) {s : TrustedSetup}
    {τ : Fr} (hs : s.WellFormed τ) (y : CellBatchInput) {c w : Bytes48 → Fr}
    (hC : ∀ k < y.commitments.size, ∀ P, uncompressG1 y.commitments[k]! = .ok P →
      G1.Represents P (c y.commitments[k]!))
    (hP : ∀ k < y.proofs.size, ∀ P, uncompressG1 y.proofs[k]! = .ok P →
      G1.Represents P (w y.proofs[k]!))
    (h : verifyCellKzgProofBatch s y.commitments y.cellIndices y.cells y.proofs = .ok true) :
    (∀ k < y.cells.size,
        c y.commitments[k]! - (cellInterpolant y.cellIndices[k]!
          y.toCellBatch.cosetsEvals[k]!).eval τ =
        w y.proofs[k]! * (τ ^ FIELD_ELEMENTS_PER_CELL -
          cellShift y.cellIndices[k]! ^ FIELD_ELEMENTS_PER_CELL)) ∨
      (y.toCellBatch.errorPoly τ c w ≠ 0 ∧
        (y.toCellBatch.errorPoly τ c w).eval y.toCellBatch.challenge = 0) := by
  obtain ⟨h₁, h₂, h₃, -, evals, hev, hI⟩ := verifyCellKzgProofBatch_eq_ok h
  have hx : decodeCells y.cells = evals := by simp only [decodeCells, hev]
  obtain ⟨⟨G, hG⟩, ⟨Q, hQ⟩⟩ := verifyCellKzgProofBatchImpl_decodes hI
  obtain ⟨hdsz, hdidx, hdmem⟩ := dedupCommitments_spec y.commitments
  obtain ⟨hGsz, hGk⟩ := array_mapM_ok hG
  obtain ⟨hQsz, hQk⟩ := array_mapM_ok hQ
  have hC' : ∀ i < G.size,
      G1.Represents G[i]! ((fun i => c (dedupCommitments y.commitments).1[i]!) i) := by
    intro i hi
    obtain ⟨k, hk, hkd⟩ := hdmem i (hGsz ▸ hi)
    have := hC k hk _ (hkd ▸ hGk i (hGsz ▸ hi))
    rwa [hkd] at this
  have hP' : ∀ k < Q.size, G1.Represents Q[k]! ((fun k => w y.proofs[k]!) k) :=
    fun k hk => hP k (hQsz ▸ hk) _ (hQk k (hQsz ▸ hk))
  rcases verifyCellKzgProofBatchImpl_valid_or_root laws hs hG hQ hC' hP' hI with hall | hroot
  · refine Or.inl fun k hk => ?_
    have hv := hall k (by omega)
    rw [(hdidx k (by omega)).2] at hv
    simpa only [CellBatchInput.toCellBatch, hx] using hv
  · refine Or.inr ?_
    simpa only [CellBatch.errorPoly, CellBatch.challenge, CellBatchInput.toCellBatch, hx]
      using hroot

/-- **Binding of the outer batch check of cells.**

Take a model of the target group, the pairing law and a well-formed setup of the secret `τ`.

Let the scalars `c` and `w` be as in the previous theorem, and let the outer check accept.

Let two cells of the batch have one cell index, and commitments with one scalar.

Let their proofs decode to `P` and `P'`.

Then one of three cases holds.

- The two cells are equal.
- The search on the two cells returns a bilinear strong Diffie–Hellman solution for `τ`.
- The challenge is a root of the error polynomial of the batch, which is not zero. -/
theorem verifyCellKzgProofBatch_binding {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    (laws : Bls.PairingLaws) {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ)
    (y : CellBatchInput) {c w : Bytes48 → Fr}
    (hC : ∀ k < y.commitments.size, ∀ P, uncompressG1 y.commitments[k]! = .ok P →
      G1.Represents P (c y.commitments[k]!))
    (hP : ∀ k < y.proofs.size, ∀ P, uncompressG1 y.proofs[k]! = .ok P →
      G1.Represents P (w y.proofs[k]!))
    (h : verifyCellKzgProofBatch s y.commitments y.cellIndices y.cells y.proofs = .ok true)
    {k k' : Nat} (hk : k < y.cells.size) (hk' : k' < y.cells.size)
    (hc : c y.commitments[k]! = c y.commitments[k']!)
    (hj : y.cellIndices[k]! = y.cellIndices[k']!) {P P' : G1}
    (hPk : uncompressG1 y.proofs[k]! = .ok P) (hPk' : uncompressG1 y.proofs[k']! = .ok P') :
    y.cells[k]! = y.cells[k']! ∨
      (∃ sol, findBsdh M s y.cellIndices[k]! y.toCellBatch.cosetsEvals[k]!
        y.toCellBatch.cosetsEvals[k']! P P' = some sol ∧ IsBsdhSolution M τ sol) ∨
      (y.toCellBatch.errorPoly τ c w ≠ 0 ∧
        (y.toCellBatch.errorPoly τ c w).eval y.toCellBatch.challenge = 0) := by
  obtain ⟨h₁, h₂, h₃, hci, evals, hev, -⟩ := verifyCellKzgProofBatch_eq_ok h
  have hx : y.toCellBatch.cosetsEvals = evals := by
    simp only [CellBatchInput.toCellBatch, decodeCells, hev]
  obtain ⟨hesz, hek⟩ := array_mapM_ok hev
  have hdec := hek k hk
  have hdec' := hek k' hk'
  by_cases hne : y.cells[k]! = y.cells[k']!
  · exact Or.inl hne
  have hne' : evals[k]! ≠ evals[k']! := fun heq =>
    hne (cellToCosetEvals_inj hdec (heq ▸ hdec'))
  rcases verifyCellKzgProofBatch_valid_or_root laws hs y hC hP h with hall | hroot
  · have hv := hall k hk
    have hv' := hall k' hk'
    rw [← hc, ← hj] at hv'
    rw [hx] at hv hv' ⊢
    exact Or.inr (Or.inl (findBsdh_valid M hs (hci k (by omega)) (size_bytesToBlsFields hdec)
      (size_bytesToBlsFields hdec') hne' (hP k (by omega) P hPk) (hP k' (by omega) P' hPk') hv
      hv'))
  · exact Or.inr (Or.inr hroot)

/-! ## The challenge from a random oracle -/

/-- The game of the batch challenge for the outer check.

The adversary queries the oracle as it likes, then outputs the inputs of the outer check.

The verifier hashes the inputs of the core check that the outer check builds. -/
def cellInputRomExperiment (adversary : OracleComp (CellBatch →ₒ Fr) CellBatchInput) :
    OracleComp (CellBatch →ₒ Fr) (CellBatchInput × Fr) := do
  let y ← adversary
  let r ← liftM ((CellBatch →ₒ Fr).query y.toCellBatch)
  return (y, r)

/-- **The bound for outer batches of at most `n` cells.**

The hash of the batch check is a random oracle on the inputs of the core check.

The adversary makes `q` queries, then outputs the inputs of an outer batch of at most `n` cells.

The event is that the challenge of that batch is a root of its error polynomial, which is not zero.

Its probability is at most `(q + 1) (n - 1) / r`.

The event does not ask that the check accepts.

An accepted batch with an invalid cell is in this event, by the theorem on accepted batches.

So the bound also covers such a batch. -/
theorem prEvent_cellInput_root_le (τ : Fr) (c w : Bytes48 → Fr) {n : Nat}
    (adversary : OracleComp (CellBatch →ₒ Fr) CellBatchInput) {q : Nat}
    (hq : OracleComp.IsTotalQueryBound adversary q) :
    Pr{let p ← (simulateQ OracleSpec.randomOracle (cellInputRomExperiment adversary)).run' ∅}[
        p.1.cellIndices.size ≤ n ∧ p.1.toCellBatch.errorPoly τ c w ≠ 0 ∧
        (p.1.toCellBatch.errorPoly τ c w).eval p.2 = 0] ≤
      (q + 1) * ((n - 1 : Nat) / Fr.modulus) := by
  have hq' : OracleComp.IsTotalQueryBound (CellBatchInput.toCellBatch <$> adversary) q := by
    rw [map_eq_bind_pure_comp, ← Nat.add_zero q]
    exact OracleComp.isTotalQueryBound_bind hq fun _ => trivial
  have hexp : batchRomExperiment (CellBatchInput.toCellBatch <$> adversary) =
      Prod.map CellBatchInput.toCellBatch id <$> cellInputRomExperiment adversary := by
    simp [batchRomExperiment, cellInputRomExperiment]
  have h := prEvent_cellErrorPoly_root_le τ (fun x i => c x.commitments[i]!)
    (fun x k => w x.proofs[k]!) (n := n) _ hq'
  rw [hexp, simulateQ_map, StateT.run'_map', prEvent_map] at h
  exact h

end EthLib.Cryptography.Kzg
