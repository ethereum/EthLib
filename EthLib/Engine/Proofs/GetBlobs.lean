module

public import EthLib.Base.Proofs.MapM
public import EthLib.Engine.GetBlobs
public import EthLib.Engine.Proofs.Json

/-!
# Proofs: `engine_getBlobs`, versions 1 to 4

A request is too large exactly when it names more hashes than the pool takes.

So a request of at most 128 hashes is never too large.

From Fusaka, version 1 is an unsupported fork for every request.

Each answer that is a list has one entry per requested hash, in the order of the request.

Each entry is what the pool holds for its hash, read for the version.

An entry of version 1 is `null` only when the pool lacks that data or does not serve.

An entry of version 3 is `null` only when the pool lacks that blob or one of its cell proofs.

Version 2 answers a list exactly when the pool serves and holds every blob with its cell proofs.

An entry of version 4 is `null` exactly when the pool holds none of the cells of its blob.

Otherwise it holds the selected cells of its blob, in increasing order of index.

Cell `i` is selected exactly when bit `i mod 8` of byte `i / 8` of the bitarray is set.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Cryptography.Kzg
open EthLib.Cryptography.Kzg.Constants

/-! ## The bitarray -/

/-- Cell `i` is selected exactly when bit `i mod 8` of byte `i / 8` of the bitarray is set. -/
@[simp] theorem mem_selectedCells (bits : CellBitarray) (i : Fin CELLS_PER_EXT_BLOB) :
    i ∈ selectedCells bits ↔
      (bits.toArray[i.val / 8]?.getD 0 >>> UInt8.ofNat (i.val % 8)) &&& 1 = 1 := by
  simp [selectedCells, Serialization.Ssz.unpackBits]

/-- The selected cell indices strictly increase. -/
theorem selectedCells_sorted (bits : CellBitarray) :
    (selectedCells bits).Pairwise (· < ·) := by
  unfold selectedCells
  exact (List.pairwise_lt_finRange CELLS_PER_EXT_BLOB).filter _

/-! ## The request limit -/

/-- A request of at most 128 hashes is never too large. -/
theorem checkRequestSize_eq_ok_of_length_le (pool : BlobPool) (hashes : List Bytes32)
    (h : hashes.length ≤ MIN_REQUEST_LIMIT) :
    checkRequestSize pool.maxRequest hashes.length = .ok () :=
  (checkRequestSize_eq_ok_iff _ _).2 (Nat.le_trans h pool.le_maxRequest)

/-! ## The entries of a pooled blob -/

namespace PooledBlob

/-- The blob and blob proof of version 1 are those that the pool holds. -/
theorem toV1_eq_some_iff (p : PooledBlob) (x : BlobAndProofV1) :
    p.toV1 = some x ↔ p.blob = some x.blob ∧ p.blobProof = some x.proof := by
  rcases x with ⟨b, q⟩
  cases hb : p.blob <;> cases hq : p.blobProof <;> simp [toV1, hb, hq, bind, Option.bind]

/-- The cell proofs exist exactly when the pool holds every cell. -/
theorem cellProofs_isSome_iff (p : PooledBlob) :
    p.cellProofs.isSome ↔ ∀ i : Fin CELLS_PER_EXT_BLOB, (p.cells[i]).isSome := by
  unfold cellProofs
  split
  · rename_i h; simp only [Option.isSome_some, true_iff]; exact h
  · rename_i h; simp only [Option.isSome_none, Bool.false_eq_true, false_iff]; exact h

/-- Each cell proof is the proof that the pool holds with that cell. -/
theorem map_snd_cells_getElem_of_cellProofs (p : PooledBlob)
    (proofs : Vector KZGProof CELLS_PER_EXT_BLOB) (h : p.cellProofs = some proofs)
    (i : Fin CELLS_PER_EXT_BLOB) : (p.cells[i]).map Prod.snd = some proofs[i] := by
  unfold cellProofs at h
  split at h
  · rename_i hs
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (hs i)
    rw [← Option.some_inj.1 h]
    simp only [Fin.getElem_fin, Vector.getElem_ofFn] at hc ⊢
    simp only [hc, Option.get_some, Option.map_some]
  · exact absurd h (by simp)

/-- Version 2 holds the pool's blob and the proof of each of its cells. -/
theorem toV2_eq_some_iff (p : PooledBlob) (x : BlobAndProofV2) :
    p.toV2 = some x ↔ p.blob = some x.blob ∧ p.cellProofs = some x.proofs := by
  rcases x with ⟨b, q⟩
  cases hb : p.blob <;> cases hq : p.cellProofs <;> simp [toV2, hb, hq, bind, Option.bind]

/-- Version 2 is absent exactly when the pool lacks the blob or one of its cells. -/
theorem toV2_eq_none_iff (p : PooledBlob) :
    p.toV2 = none ↔ p.blob = none ∨ ∃ i : Fin CELLS_PER_EXT_BLOB, p.cells[i] = none := by
  have := cellProofs_isSome_iff p
  cases hb : p.blob <;> cases hq : p.cellProofs <;>
    simp_all [toV2, bind, Option.bind, Option.isSome_iff_ne_none]

/-- The cells of version 4 are those at the selected indices, in turn, each with its proof. -/
theorem getElem?_cellsAt (p : PooledBlob) (indices : List (Fin CELLS_PER_EXT_BLOB)) (k : Nat) :
    (p.cellsAt indices)[k]? = indices[k]?.map fun i => p.cells[i] := by
  simp [cellsAt]

/-- Version 4 answers the cells at the indices exactly when the pool holds a cell of the blob. -/
theorem toV4_eq_some_iff (p : PooledBlob) (indices : List (Fin CELLS_PER_EXT_BLOB))
    (x : BlobCellsAndProofsV1) :
    p.toV4 indices = some x ↔ p.holdsCell = true ∧ x.cells = p.cellsAt indices := by
  rcases x with ⟨cells⟩
  unfold toV4
  by_cases hh : p.holdsCell = true
  · simp only [hh, ↓reduceIte, Option.some.injEq, BlobCellsAndProofsV1.mk.injEq, true_and]
    exact eq_comm
  · simp only [Bool.not_eq_true] at hh
    simp [hh]

/-- Version 4 is absent exactly when the pool holds none of the cells of the blob. -/
theorem toV4_eq_none_iff (p : PooledBlob) (indices : List (Fin CELLS_PER_EXT_BLOB)) :
    p.toV4 indices = none ↔ p.holdsCell = false := by
  unfold toV4
  cases p.holdsCell <;> simp

end PooledBlob

/-! ## Version 1 -/

/-- From Fusaka, version 1 is an unsupported fork. -/
theorem getBlobsV1_of_fusaka (pool : BlobPool) {fork : Fork} (hashes : List Bytes32)
    (h : .fusaka ≤ fork) : getBlobsV1 pool fork hashes = .error .unsupportedFork := by
  simp [getBlobsV1, h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- Before Fusaka, version 1 answers each hash in turn, or fails on a too large request. -/
theorem getBlobsV1_of_lt_fusaka (pool : BlobPool) {fork : Fork} (hashes : List Bytes32)
    (h : fork < .fusaka) :
    getBlobsV1 pool fork hashes = (checkRequestSize pool.maxRequest hashes.length).map fun _ =>
      hashes.map fun h => if pool.serving then (pool.lookup h).bind PooledBlob.toV1 else none := by
  have : ¬ .fusaka ≤ fork := Nat.not_le.2 h
  cases hc : checkRequestSize pool.maxRequest hashes.length <;>
    simp [getBlobsV1, this, hc, bind, Except.bind, pure, Except.pure, Except.map]

/-- An answer of version 1 has one entry per requested hash. -/
theorem getBlobsV1_length {pool : BlobPool} {fork : Fork} {hashes : List Bytes32}
    {r : List (Option BlobAndProofV1)} (h : getBlobsV1 pool fork hashes = .ok r) :
    r.length = hashes.length := by
  by_cases hf : .fusaka ≤ fork
  · rw [getBlobsV1_of_fusaka pool hashes hf] at h; cases h
  · rw [getBlobsV1_of_lt_fusaka pool hashes (Nat.not_le.1 hf)] at h
    cases hc : checkRequestSize pool.maxRequest hashes.length <;> simp_all [Except.map]
    subst h; simp

/-- Each entry of version 1 is the blob and blob proof that the pool holds for its hash. -/
theorem getBlobsV1_getElem? {pool : BlobPool} {fork : Fork} {hashes : List Bytes32}
    {r : List (Option BlobAndProofV1)} (h : getBlobsV1 pool fork hashes = .ok r) (i : Nat) :
    r[i]? = hashes[i]?.map fun h =>
      if pool.serving then (pool.lookup h).bind PooledBlob.toV1 else none := by
  by_cases hf : .fusaka ≤ fork
  · rw [getBlobsV1_of_fusaka pool hashes hf] at h; cases h
  · rw [getBlobsV1_of_lt_fusaka pool hashes (Nat.not_le.1 hf)] at h
    cases hc : checkRequestSize pool.maxRequest hashes.length <;> simp_all [Except.map]
    subst h; simp

/-- An entry of version 1 that is not `null` holds the pool's blob and blob proof for its hash. -/
theorem getBlobsV1_lookup_of_getElem? {pool : BlobPool} {fork : Fork} {hashes : List Bytes32}
    {r : List (Option BlobAndProofV1)} (h : getBlobsV1 pool fork hashes = .ok r) {i : Nat}
    {x : BlobAndProofV1} (hx : r[i]? = some (some x)) :
    ∃ hash p, hashes[i]? = some hash ∧ pool.lookup hash = some p ∧
      p.blob = some x.blob ∧ p.blobProof = some x.proof := by
  rw [getBlobsV1_getElem? h] at hx
  cases hh : hashes[i]? with
  | none => simp [hh] at hx
  | some hash =>
    simp only [hh, Option.map_some, Option.some.injEq] at hx
    split at hx
    · cases hp : pool.lookup hash with
      | none => simp [hp] at hx
      | some p =>
        simp only [hp, Option.bind_some] at hx
        exact ⟨hash, p, rfl, hp, (PooledBlob.toV1_eq_some_iff p x).1 hx⟩
    · cases hx

/-! ## Version 2 -/

/-- After the size check, version 2 maps each hash to its blob and cell proofs, if the pool serves.
-/
theorem getBlobsV2_eq (pool : BlobPool) (hashes : List Bytes32) :
    getBlobsV2 pool hashes = (checkRequestSize pool.maxRequest hashes.length).map fun _ =>
      if pool.serving then hashes.mapM fun h => (pool.lookup h).bind PooledBlob.toV2
      else none := by
  cases hc : checkRequestSize pool.maxRequest hashes.length <;>
    cases hs : pool.serving <;>
      simp [getBlobsV2, hc, hs, bind, Except.bind, pure, Except.pure, Except.map]

/-- The list answer of version 2 is the pool's blob and cell proofs for each hash in turn. -/
theorem getBlobsV2_eq_some {pool : BlobPool} {hashes : List Bytes32}
    {l : List BlobAndProofV2} (h : getBlobsV2 pool hashes = .ok (some l)) :
    pool.serving = true ∧ hashes.mapM (fun h => (pool.lookup h).bind PooledBlob.toV2) = some l := by
  rw [getBlobsV2_eq] at h
  cases hc : checkRequestSize pool.maxRequest hashes.length <;> simp only [hc, Except.map] at h
  · cases h
  · injection h with h
    split at h
    · exact ⟨by assumption, h⟩
    · cases h

/-- A list answer of version 2 has one entry per requested hash. -/
theorem getBlobsV2_length {pool : BlobPool} {hashes : List Bytes32}
    {l : List BlobAndProofV2} (h : getBlobsV2 pool hashes = .ok (some l)) :
    l.length = hashes.length :=
  mapM_some_length (getBlobsV2_eq_some h).2

/-- Each entry of a list answer of version 2 is the pool's blob and cell proofs for its hash. -/
theorem getBlobsV2_getElem? {pool : BlobPool} {hashes : List Bytes32}
    {l : List BlobAndProofV2} (h : getBlobsV2 pool hashes = .ok (some l)) (i : Nat) :
    l[i]? = (hashes[i]?).bind fun h => (pool.lookup h).bind PooledBlob.toV2 :=
  mapM_some_getElem? (getBlobsV2_eq_some h).2 i

/-- Version 2 answers a list exactly when the pool serves and holds each blob with all cell proofs.

This holds for every request that is not too large. -/
theorem getBlobsV2_isSome_iff {pool : BlobPool} {hashes : List Bytes32}
    {r : Option (List BlobAndProofV2)} (h : getBlobsV2 pool hashes = .ok r) :
    r.isSome ↔ pool.serving = true ∧
      ∀ hash ∈ hashes, ∃ p, pool.lookup hash = some p ∧ p.toV2.isSome := by
  rw [getBlobsV2_eq] at h
  cases hc : checkRequestSize pool.maxRequest hashes.length <;> simp only [hc, Except.map] at h
  · cases h
  · injection h with h
    subst h
    cases hs : pool.serving
    · simp
    · simp only [ite_true, true_and, isSome_mapM_iff]
      refine forall₂_congr fun hash _ => ?_
      cases pool.lookup hash <;> simp

/-! ## Version 3 -/

/-- Version 3 answers each hash in turn when the pool serves, after the size check. -/
theorem getBlobsV3_eq (pool : BlobPool) (hashes : List Bytes32) :
    getBlobsV3 pool hashes = (checkRequestSize pool.maxRequest hashes.length).map fun _ =>
      if pool.serving then some (hashes.map fun h => (pool.lookup h).bind PooledBlob.toV2)
      else none := by
  cases hc : checkRequestSize pool.maxRequest hashes.length <;>
    cases hs : pool.serving <;>
      simp [getBlobsV3, hc, hs, bind, Except.bind, pure, Except.pure, Except.map]

/-- A list answer of version 3 comes exactly when the pool serves, for a request not too large. -/
theorem getBlobsV3_isSome_iff {pool : BlobPool} {hashes : List Bytes32}
    {r : Option (List (Option BlobAndProofV2))} (h : getBlobsV3 pool hashes = .ok r) :
    r.isSome ↔ pool.serving = true := by
  rw [getBlobsV3_eq] at h
  cases hc : checkRequestSize pool.maxRequest hashes.length <;> simp only [hc, Except.map] at h
  · cases h
  · injection h with h
    subst h
    cases hs : pool.serving <;> simp

/-- The list answer of version 3 is the pool's blob and cell proofs for each hash, or `null`. -/
theorem getBlobsV3_eq_some {pool : BlobPool} {hashes : List Bytes32}
    {l : List (Option BlobAndProofV2)} (h : getBlobsV3 pool hashes = .ok (some l)) :
    l = hashes.map fun h => (pool.lookup h).bind PooledBlob.toV2 := by
  rw [getBlobsV3_eq] at h
  cases hc : checkRequestSize pool.maxRequest hashes.length <;> simp only [hc, Except.map] at h
  · cases h
  · injection h with h
    split at h
    · cases h; rfl
    · cases h

/-- A list answer of version 3 has one entry per requested hash. -/
theorem getBlobsV3_length {pool : BlobPool} {hashes : List Bytes32}
    {l : List (Option BlobAndProofV2)} (h : getBlobsV3 pool hashes = .ok (some l)) :
    l.length = hashes.length := by
  simp [getBlobsV3_eq_some h]

/-! ## Version 4 -/

/-- Version 4 answers each hash in turn when the pool serves, after the size check. -/
theorem getBlobsV4_eq (pool : BlobPool) (hashes : List Bytes32) (bits : CellBitarray) :
    getBlobsV4 pool hashes bits = (checkRequestSize pool.maxRequest hashes.length).map fun _ =>
      if pool.serving then
        some (hashes.map fun h => (pool.lookup h).bind (·.toV4 (selectedCells bits)))
      else none := by
  cases hc : checkRequestSize pool.maxRequest hashes.length <;>
    cases hs : pool.serving <;>
      simp [getBlobsV4, hc, hs, bind, Except.bind, pure, Except.pure, Except.map]

/-- A list answer of version 4 comes exactly when the pool serves, for a request not too large. -/
theorem getBlobsV4_isSome_iff {pool : BlobPool} {hashes : List Bytes32} {bits : CellBitarray}
    {r : Option (List (Option BlobCellsAndProofsV1))}
    (h : getBlobsV4 pool hashes bits = .ok r) : r.isSome ↔ pool.serving = true := by
  rw [getBlobsV4_eq] at h
  cases hc : checkRequestSize pool.maxRequest hashes.length <;> simp only [hc, Except.map] at h
  · cases h
  · injection h with h
    subst h
    cases hs : pool.serving <;> simp

/-- The list answer of version 4 is, for each hash, the selected cells of what the pool holds.

An entry is `null` when the pool holds nothing of that blob. -/
theorem getBlobsV4_eq_some {pool : BlobPool} {hashes : List Bytes32} {bits : CellBitarray}
    {l : List (Option BlobCellsAndProofsV1)}
    (h : getBlobsV4 pool hashes bits = .ok (some l)) :
    l = hashes.map fun h => (pool.lookup h).bind (·.toV4 (selectedCells bits)) := by
  rw [getBlobsV4_eq] at h
  cases hc : checkRequestSize pool.maxRequest hashes.length <;> simp only [hc, Except.map] at h
  · cases h
  · injection h with h
    split at h
    · cases h; rfl
    · cases h

/-- A list answer of version 4 has one entry per requested hash. -/
theorem getBlobsV4_length {pool : BlobPool} {hashes : List Bytes32} {bits : CellBitarray}
    {l : List (Option BlobCellsAndProofsV1)}
    (h : getBlobsV4 pool hashes bits = .ok (some l)) : l.length = hashes.length := by
  simp [getBlobsV4_eq_some h]

end EthLib.Engine
