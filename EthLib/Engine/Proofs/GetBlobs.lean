module

public import EthLib.Base.Proofs.MapM
public import EthLib.Engine.GetBlobs
public import EthLib.Engine.Proofs.Json
-- Showing that a written value is not `null` unfolds the null test of Lean's JSON.
import all Lean.Data.Json.Basic

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

The decoder reads back the parameters that the writer writes.

It reads no JSON value other than what the writer writes.

Each structure of the answer reads back from its JSON, and so does the answer of each version.

A JSON value reads as a blob with its proof, or with its cell proofs, exactly in canonical form.

Each blob and proof is then in lowercase hex.

The cells of version 4 decode only from two arrays of one length, with `null` at the same positions.
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
    (h : hashes.length ≤ MIN_BLOBS_REQUEST_LIMIT) :
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

/-- A JSON value reads as the parameters of a version exactly when it is the array below.

Its first item is the array of the versioned hashes in order, each `0x` and 64 lowercase hex digits.

Before version 4 it has no other item.

From version 4 its second and last item is the bitarray, `0x` and 32 lowercase hex digits.

The bitarray is returned exactly from version 4. -/
theorem getBlobsParams_eq_ok_iff {version : Nat} {params : Lean.Json} {hashes : List Bytes32}
    {bits : Option CellBitarray} :
    getBlobsParams version params = .ok (hashes, bits) ↔
      version < 4 ∧ bits = none ∧
          params = .arr #[.arr (hashes.map fun h => .str (hexString h.toList)).toArray] ∨
        4 ≤ version ∧ ∃ b, bits = some b ∧
          params = .arr #[.arr (hashes.map fun h => .str (hexString h.toList)).toArray,
            .str (hexString b.toList)] := by
  have count : decide (getBlobsParamCount version = 2) = decide (4 ≤ version) := by
    unfold getBlobsParamCount
    by_cases hv : 4 ≤ version <;> simp [hv]
  cases params with
  | arr items =>
    obtain ⟨xs⟩ := items
    simp only [getBlobsParams, Serialization.JsonRpc.paramsArray, count]
    by_cases hv : 4 ≤ version
    · simp only [hv, decide_true, Nat.not_lt.mpr hv, false_and, false_or, true_and]
      match xs with
      | [] => simp [bind, Except.bind, pure, Except.pure]
      | [_] => simp [bind, Except.bind, pure, Except.pure]
      | [h, b] =>
        simp only [Lean.Json.arr.injEq, Array.mk.injEq, List.cons.injEq, and_true,
          ← Serialization.JsonRpc.array_fixed_false_eq_ok_iff (what := "hashes")
            (w := "versioned hash")]
        cases hh : Serialization.JsonRpc.array "hashes"
          (Serialization.JsonRpc.fixed "versioned hash" 32 · false) h <;>
          cases hb : Serialization.JsonRpc.fixed "indices_bitarray" CELL_BITARRAY_BYTES b false <;>
          cases bits <;>
          simp [hh, hb, bind, Except.bind, pure, Except.pure,
            ← Serialization.JsonRpc.fixed_false_eq_ok_iff (what := "indices_bitarray")]
      | _ :: _ :: _ :: _ => simp [bind, Except.bind, pure, Except.pure]
    · simp only [hv, decide_false, Nat.not_le.mp hv, false_and, or_false, true_and]
      match xs with
      | [] => simp [bind, Except.bind, pure, Except.pure]
      | [h] =>
        simp only [Lean.Json.arr.injEq, Array.mk.injEq, List.cons.injEq, and_true,
          ← Serialization.JsonRpc.array_fixed_false_eq_ok_iff (what := "hashes")
            (w := "versioned hash")]
        cases hh : Serialization.JsonRpc.array "hashes"
          (Serialization.JsonRpc.fixed "versioned hash" 32 · false) h <;> cases bits <;>
          simp [hh, bind, Except.bind, pure, Except.pure]
      | _ :: _ :: _ => simp [bind, Except.bind, pure, Except.pure]
  | _ => simp [getBlobsParams, Serialization.JsonRpc.paramsArray, bind, Except.bind]

/-- The decoder of the parameters reads back the hashes and the bitarray that the writer writes.

A bitarray is given exactly from version 4. -/
theorem getBlobsParams_json {version : Nat} (hashes : List Bytes32)
    (bits : Option CellBitarray) (four : bits.isSome ↔ 4 ≤ version) :
    getBlobsParams version (getBlobsParamsJson hashes bits) = .ok (hashes, bits) := by
  apply getBlobsParams_eq_ok_iff.mpr
  cases bits <;> simp at four <;>
    simp [four, getBlobsParamsJson, Serialization.JsonRpc.listJson,
      Serialization.JsonRpc.dataJson]

/-! ## The answer as JSON -/

/-- A blob and its proof read back from their JSON. -/
theorem blobAndProofV1OfJson_json (x : BlobAndProofV1) :
    blobAndProofV1OfJson (blobAndProofV1Json x) = .ok x := by
  have hd : [("blob", Serialization.JsonRpc.dataJson x.blob.toList),
      ("proof", Serialization.JsonRpc.dataJson x.proof.toList)].Pairwise
      fun a b => a.1 ≠ b.1 := by simp
  obtain ⟨fs, hfs, hp⟩ := Serialization.JsonRpc.fields_mkObj "blobAndProof" hd
    (by simp [Serialization.JsonRpc.isNull_str, Serialization.JsonRpc.dataJson])
  have hex : Serialization.JsonRpc.hasExactly fs ["blob", "proof"] = true :=
    Serialization.JsonRpc.hasExactly_of_perm hp
  have r1 := Serialization.JsonRpc.field_of_perm (what := "blobAndProof") hp hd
    (List.mem_cons_self ..)
  have r2 := Serialization.JsonRpc.field_of_perm (what := "blobAndProof") hp hd
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  unfold blobAndProofV1OfJson blobAndProofV1Json
  simp only [bind, Except.bind, hfs, hex, ite_true, r1, r2, Serialization.JsonRpc.fixed_dataJson,
    pure, Except.pure]

/-- A blob and the proofs of its cells read back from their JSON. -/
theorem blobAndProofV2OfJson_json (x : BlobAndProofV2) :
    blobAndProofV2OfJson (blobAndProofV2Json x) = .ok x := by
  have hd : [("blob", Serialization.JsonRpc.dataJson x.blob.toList),
      ("proofs", Serialization.JsonRpc.listJson (Serialization.JsonRpc.dataJson ·.toList)
        x.proofs.toList)].Pairwise fun a b => a.1 ≠ b.1 := by simp
  obtain ⟨fs, hfs, hp⟩ := Serialization.JsonRpc.fields_mkObj "blobAndProof" hd
    (by simp [Serialization.JsonRpc.isNull_str, Serialization.JsonRpc.isNull_arr,
      Serialization.JsonRpc.dataJson, Serialization.JsonRpc.listJson])
  have hex : Serialization.JsonRpc.hasExactly fs ["blob", "proofs"] = true :=
    Serialization.JsonRpc.hasExactly_of_perm hp
  have r1 := Serialization.JsonRpc.field_of_perm (what := "blobAndProof") hp hd
    (List.mem_cons_self ..)
  have r2 := Serialization.JsonRpc.field_of_perm (what := "blobAndProof") hp hd
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  unfold blobAndProofV2OfJson blobAndProofV2Json
  simp only [bind, Except.bind, hfs, hex, ite_true, r1, r2, Serialization.JsonRpc.fixed_dataJson,
    Serialization.JsonRpc.array_fixed_listJson, pure, Except.pure]
  have hl : x.proofs.toList.length = CELLS_PER_EXT_BLOB := by simp
  simp only [hl, ↓reduceDIte]
  rcases x with ⟨b, ⟨⟨l⟩, h⟩⟩
  rfl

/-- A JSON value reads as a blob and its proof exactly when it is an object of the form below.

A member whose value is `null` counts as absent.

Its other members are `blob` and `proof`, each once.

Each is `0x` and two lowercase hex digits for each of its bytes. -/
theorem blobAndProofV1OfJson_eq_ok_iff {j : Lean.Json} {x : BlobAndProofV1} :
    blobAndProofV1OfJson j = .ok x ↔
      ∃ fs, Serialization.JsonRpc.fields "blobAndProof" j = .ok fs ∧
        Serialization.JsonRpc.hasExactly fs ["blob", "proof"] = true ∧
        fs.lookup "blob" = some (.str (hexString x.blob.toList)) ∧
        fs.lookup "proof" = some (.str (hexString x.proof.toList)) := by
  unfold blobAndProofV1OfJson
  simp only [bind_ok_iff]
  refine exists_congr fun fs => and_congr_right fun _ => ?_
  by_cases hex : Serialization.JsonRpc.hasExactly fs ["blob", "proof"] = true
  · rw [and_iff_right hex]
    simp only [hex, ↓reduceIte, bind_ok_iff, Serialization.JsonRpc.field_eq_ok_iff,
      Serialization.JsonRpc.fixed_false_eq_ok_iff, pure, Except.pure, Except.ok.injEq]
    obtain ⟨blob, proof⟩ := x
    constructor
    · rintro ⟨_, hb, blob, rfl, _, hp, proof, rfl, he⟩
      cases he
      exact ⟨hb, hp⟩
    · rintro ⟨hb, hp⟩
      exact ⟨_, hb, blob, rfl, _, hp, proof, rfl, rfl⟩
  -- Any other set of members fails, never with a blob.
  · simp [hex, bind, Except.bind, Serialization.JsonRpc.reject]

/-- A JSON value reads as a blob and its cell proofs exactly when it is an object of the form below.

A member whose value is `null` counts as absent.

Its other members are `blob` and `proofs`, each once.

The blob is `0x` and two lowercase hex digits for each of its bytes.

The proofs are an array of one proof per cell, each written in the same way. -/
theorem blobAndProofV2OfJson_eq_ok_iff {j : Lean.Json} {x : BlobAndProofV2} :
    blobAndProofV2OfJson j = .ok x ↔
      ∃ fs, Serialization.JsonRpc.fields "blobAndProof" j = .ok fs ∧
        Serialization.JsonRpc.hasExactly fs ["blob", "proofs"] = true ∧
        fs.lookup "blob" = some (.str (hexString x.blob.toList)) ∧
        fs.lookup "proofs" =
          some (.arr (x.proofs.toList.map fun p => .str (hexString p.toList)).toArray) := by
  unfold blobAndProofV2OfJson
  simp only [bind_ok_iff]
  refine exists_congr fun fs => and_congr_right fun _ => ?_
  by_cases hex : Serialization.JsonRpc.hasExactly fs ["blob", "proofs"] = true
  · rw [and_iff_right hex]
    simp only [hex, ↓reduceIte, bind_ok_iff, Serialization.JsonRpc.field_eq_ok_iff,
      Serialization.JsonRpc.fixed_false_eq_ok_iff,
      Serialization.JsonRpc.array_fixed_false_eq_ok_iff]
    obtain ⟨blob, proofs⟩ := x
    constructor
    · rintro ⟨_, hb, blob, rfl, _, hp, l, rfl, h⟩
      split at h
      · cases h
        exact ⟨hb, hp⟩
      -- A count of proofs other than one per cell fails.
      · cases h
    · rintro ⟨hb, hp⟩
      refine ⟨_, hb, blob, rfl, _, hp, proofs.toList, rfl, ?_⟩
      simp only [Vector.length_toList, ↓reduceDIte, pure, Except.pure]
      rcases proofs with ⟨⟨l⟩, h⟩
      rfl
  -- Any other set of members fails, never with a blob.
  · simp [hex, bind, Except.bind, Serialization.JsonRpc.reject]

/-- A list of optional byte strings of a size reads back from its encoding as data. -/
private theorem array_nullable_fixed_listJson {n : Nat} (what w : String)
    (l : List (Option (Vector UInt8 n))) :
    Serialization.JsonRpc.array what (Serialization.JsonRpc.nullable
      (Serialization.JsonRpc.fixed w n))
      (Serialization.JsonRpc.listJson (Serialization.JsonRpc.optionJson
        (Serialization.JsonRpc.dataJson ·.toList)) l) = .ok l :=
  Serialization.JsonRpc.array_listJson_of what (Serialization.JsonRpc.nullable_optionJson
    (fun v => Serialization.JsonRpc.fixed_dataJson w v false)
    (fun _ => Serialization.JsonRpc.isNull_str _)) l

/-- Encoding the images of a list encodes each item through the composite encoder. -/
private theorem listJson_map_option {α β : Type} (g : α → Lean.Json) (h : β → α)
    (l : List β) {g' : β → Lean.Json} (hg : ∀ x, g' x = g (h x)) :
    Serialization.JsonRpc.listJson g' l = Serialization.JsonRpc.listJson g (l.map h) := by
  unfold Serialization.JsonRpc.listJson
  congr 1
  apply Array.toList_inj.mp
  simp only [Array.toList_map, List.map_map]
  exact List.map_congr_left fun x _ => by simp [hg]

/-- Reading the cells and the proofs that a list of entries splits into gives back the entries. -/
private theorem mapM_cellAndProof (l : List (Option (Cell × KZGProof))) :
    ((l.map (·.map Prod.fst)).zip (l.map (·.map Prod.snd))).mapM cellAndProof = .ok l := by
  induction l with
  | nil => rfl
  | cons o l ih =>
    cases o <;> simp only [List.map_cons, List.zip_cons_cons, List.mapM_cons, Option.map_none,
      Option.map_some, cellAndProof, ih, bind, Except.bind, pure, Except.pure]

/-- The selected cells of a blob read back from their JSON, with `null` at the same positions. -/
theorem blobCellsOfJson_json (x : BlobCellsAndProofsV1) :
    blobCellsOfJson (blobCellsJson x) = .ok x := by
  have c1 : Serialization.JsonRpc.listJson
      (Serialization.JsonRpc.optionJson (Serialization.JsonRpc.dataJson ·.1.toList)) x.cells =
      Serialization.JsonRpc.listJson (Serialization.JsonRpc.optionJson
        (Serialization.JsonRpc.dataJson ·.toList)) (x.cells.map (·.map Prod.fst)) :=
    listJson_map_option _ _ _ (fun o => by cases o <;> rfl)
  have c2 : Serialization.JsonRpc.listJson
      (Serialization.JsonRpc.optionJson (Serialization.JsonRpc.dataJson ·.2.toList)) x.cells =
      Serialization.JsonRpc.listJson (Serialization.JsonRpc.optionJson
        (Serialization.JsonRpc.dataJson ·.toList)) (x.cells.map (·.map Prod.snd)) :=
    listJson_map_option _ _ _ (fun o => by cases o <;> rfl)
  have hd : [("blob_cells", Serialization.JsonRpc.listJson (Serialization.JsonRpc.optionJson
      (Serialization.JsonRpc.dataJson ·.toList)) (x.cells.map (·.map Prod.fst))),
      ("proofs", Serialization.JsonRpc.listJson (Serialization.JsonRpc.optionJson
      (Serialization.JsonRpc.dataJson ·.toList)) (x.cells.map (·.map Prod.snd)))
      ].Pairwise fun a b => a.1 ≠ b.1 := by simp
  obtain ⟨fs, hfs, hp⟩ := Serialization.JsonRpc.fields_mkObj "blobCells" hd
    (by simp [Serialization.JsonRpc.isNull_arr, Serialization.JsonRpc.listJson])
  have hex : Serialization.JsonRpc.hasExactly fs ["blob_cells", "proofs"] = true :=
    Serialization.JsonRpc.hasExactly_of_perm hp
  have r1 := Serialization.JsonRpc.field_of_perm (what := "blobCells") hp hd
    (List.mem_cons_self ..)
  have r2 := Serialization.JsonRpc.field_of_perm (what := "blobCells") hp hd
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  unfold blobCellsOfJson blobCellsJson
  rw [c1, c2]
  simp only [bind, Except.bind, hfs, hex, ite_true, r1, r2,
    array_nullable_fixed_listJson, List.length_map, pure, Except.pure, mapM_cellAndProof]

/-- A value that reads as optional is `null` exactly when it reads as absent. -/
private theorem isNull_of_nullable {α : Type} {f : Lean.Json → Serialization.JsonRpc.Read α}
    {j : Lean.Json} {o : Option α} (h : Serialization.JsonRpc.nullable f j = .ok o) :
    j.isNull = o.isNone := by
  cases j with
  | null => simp only [Serialization.JsonRpc.nullable, pure, Except.pure, Except.ok.injEq] at h
            subst h; rfl
  | _ =>
    revert h
    simp only [Serialization.JsonRpc.nullable]
    cases f _ <;> simp [Functor.map, Except.map] <;> rintro rfl <;> rfl

/-- A cell and its proof that read as one entry are both absent or both present, as the entry is.
-/
private theorem isNone_of_cellAndProof {c : Option Cell} {p : Option KZGProof}
    {r : Option (Cell × KZGProof)} (h : cellAndProof (c, p) = .ok r) :
    c.isNone = p.isNone ∧ r.isNone = c.isNone := by
  cases c <;> cases p <;> simp_all [cellAndProof, pure, Except.pure] <;> subst h <;> rfl

/-- Cells decode only from two arrays of one length, with `null` at the same positions.

Their number is the length of the arrays, and a decoded entry is absent exactly at a `null` cell.

Step 4 of `engine_getBlobsV4` asks for one direction of this rule, and EthLib requires both. -/
theorem blobCellsOfJson_nulls {j : Lean.Json} {x : BlobCellsAndProofsV1}
    (h : blobCellsOfJson j = .ok x) :
    ∃ fs cells proofs, Serialization.JsonRpc.fields "blobCells" j = .ok fs ∧
      fs.lookup "blob_cells" = some (.arr cells) ∧ fs.lookup "proofs" = some (.arr proofs) ∧
      cells.size = proofs.size ∧ x.cells.length = cells.size ∧
      (∀ i (hc : i < cells.size) (hp : i < proofs.size), cells[i].isNull = proofs[i].isNull) ∧
      ∀ i (hx : i < x.cells.length) (hc : i < cells.size), x.cells[i].isNone = cells[i].isNull := by
  unfold blobCellsOfJson at h
  rcases hf : Serialization.JsonRpc.fields "blobCells" j with e | fs
  · simp [hf, bind, Except.bind] at h
  by_cases hex : Serialization.JsonRpc.hasExactly fs ["blob_cells", "proofs"] = true
  case neg => simp [hf, hex, bind, Except.bind] at h
  rcases hc : Serialization.JsonRpc.field "blobCells" fs "blob_cells" with e | cj
  · simp [hf, hex, hc, bind, Except.bind] at h
  rcases hc2 : Serialization.JsonRpc.array "blob_cells"
    (Serialization.JsonRpc.nullable (Serialization.JsonRpc.fixed "cell" BYTES_PER_CELL)) cj with
    e | cl
  · simp [hf, hex, hc, hc2, bind, Except.bind] at h
  rcases hp : Serialization.JsonRpc.field "blobCells" fs "proofs" with e | pj
  · simp [hf, hex, hc, hc2, hp, bind, Except.bind] at h
  rcases hp2 : Serialization.JsonRpc.array "proofs"
    (Serialization.JsonRpc.nullable (Serialization.JsonRpc.fixed "proof" 48)) pj with e | pl
  · simp [hf, hex, hc, hc2, hp, hp2, bind, Except.bind] at h
  by_cases hlen : cl.length = pl.length
  case neg => simp [hf, hex, hc, hc2, hp, hp2, hlen, bind, Except.bind] at h
  rcases hm : (cl.zip pl).mapM cellAndProof with e | ys
  · simp [hf, hex, hc, hc2, hp, hp2, hlen, hm, bind, Except.bind] at h
  simp only [hf, hex, hc, hc2, hp, hp2, hlen, hm, bind, Except.bind, pure, Except.pure,
    ↓reduceIte, Except.ok.injEq] at h
  subst h
  obtain ⟨cs, rfl, hcl, hcg⟩ := Serialization.JsonRpc.array_eq_ok_iff.mp hc2
  obtain ⟨ps, rfl, hpl, hpg⟩ := Serialization.JsonRpc.array_eq_ok_iff.mp hp2
  have hsz : cs.size = ps.size := by omega
  refine ⟨fs, cs, ps, rfl, Serialization.JsonRpc.field_eq_ok_iff.mp hc,
    Serialization.JsonRpc.field_eq_ok_iff.mp hp, hsz, ?_, ?_, ?_⟩
  · rw [mapM_ok_length hm, List.length_zip]
    omega
  · intro i hi hi'
    have hz : i < (cl.zip pl).length := by rw [List.length_zip]; omega
    have h1 := mapM_ok_getElem hm i hz
    simp only [List.getElem_zip] at h1
    rw [isNull_of_nullable (hcg i hi), isNull_of_nullable (hpg i hi')]
    exact (isNone_of_cellAndProof h1).1
  · intro i hx hi
    have hz : i < (cl.zip pl).length := by rw [List.length_zip]; omega
    have h1 := mapM_ok_getElem hm i hz
    simp only [List.getElem_zip] at h1
    rw [isNull_of_nullable (hcg i hi)]
    exact (isNone_of_cellAndProof h1).2

/-- An answer of version 1 reads back from its JSON, with `null` at the same entries. -/
theorem getBlobsV1OfJson_json (blobs : List (Option BlobAndProofV1)) :
    getBlobsV1OfJson (getBlobsV1Json blobs) = .ok blobs := by
  unfold getBlobsV1OfJson getBlobsV1Json
  rw [Serialization.JsonRpc.array_listJson_of _
    (Serialization.JsonRpc.nullable_optionJson blobAndProofV1OfJson_json fun _ => rfl)]
  rfl

/-- An answer of version 2 reads back from its JSON, a list or `null` alone. -/
theorem getBlobsV2OfJson_json (blobs : Option (List BlobAndProofV2)) :
    getBlobsV2OfJson (getBlobsV2Json blobs) = .ok blobs := by
  unfold getBlobsV2OfJson getBlobsV2Json
  rw [Serialization.JsonRpc.nullable_optionJson
    (Serialization.JsonRpc.array_listJson_of _ blobAndProofV2OfJson_json)
    (fun _ => Serialization.JsonRpc.isNull_arr _)]
  rfl

/-- An answer of version 3 reads back from its JSON, a list or `null` alone. -/
theorem getBlobsV3OfJson_json (blobs : Option (List (Option BlobAndProofV2))) :
    getBlobsV3OfJson (getBlobsV3Json blobs) = .ok blobs := by
  unfold getBlobsV3OfJson getBlobsV3Json
  rw [Serialization.JsonRpc.nullable_optionJson (Serialization.JsonRpc.array_listJson_of _
    (Serialization.JsonRpc.nullable_optionJson
    blobAndProofV2OfJson_json fun _ => rfl)) (fun _ => Serialization.JsonRpc.isNull_arr _)]
  rfl

/-- An answer of version 4 reads back from its JSON, a list or `null` alone. -/
theorem getBlobsV4OfJson_json (blobs : Option (List (Option BlobCellsAndProofsV1))) :
    getBlobsV4OfJson (getBlobsV4Json blobs) = .ok blobs := by
  unfold getBlobsV4OfJson getBlobsV4Json
  rw [Serialization.JsonRpc.nullable_optionJson (Serialization.JsonRpc.array_listJson_of _
    (Serialization.JsonRpc.nullable_optionJson
    blobCellsOfJson_json fun _ => rfl)) (fun _ => Serialization.JsonRpc.isNull_arr _)]
  rfl

end EthLib.Engine
