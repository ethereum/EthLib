module

public import EthLib.Execution.Rpc.Methods
public import EthLib.Execution.Proofs.Rpc.Header
public import EthLib.Execution.Proofs.Rpc.TransactionInfo
public import EthLib.Serialization.Proofs.Ssz.Codec.JsonLaws
-- The fields of an encoded object unfold Lean's `Json.mkObj` and `Json.isNull`.
import all Lean.Data.Json.Basic

/-!
# Proofs: the JSON form of a block

The block object has the names of the header object of its fork and those of the fields of a block.

On each name of the header, it holds what the header object of the same block holds.

Each property holds whenever the writer gives an object.

The writer fails when the node cannot encode the block, or recover a sender in it.

Its transactions are their hashes, or their objects, which carry the same hashes in the same order.

Each list has one entry for each transaction of the block.
-/

public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Blocks (Header Withdrawal)
open EthLib.Execution.Transactions

/-- The names of the fields of a block after its header are those of its fork. -/
private theorem names_blockFields {fork : Fork} (size : Nat) (uncles : List Hash32)
    (transactions : Lean.Json) (withdrawals : Since .shapella fork (List Withdrawal)) :
    (blockFields size uncles transactions withdrawals).map Prod.fst = blockNames fork := by
  unfold blockFields blockNames sinceField sinceName
  by_cases h : Fork.shapella ≤ fork <;> simp [h]

/-- The writer succeeds only on a block that has the parts of its object, and then writes it. -/
private theorem blockJson_ok {r : BlockRecord} {full : Bool} {j : Lean.Json}
    (h : r.blockJson full = .ok j) :
    ∃ size uncles transactions, j = Lean.Json.mkObj (headerFields r.hash r.block.header ++
        blockFields size uncles transactions r.block.withdrawals) ∧
      (full = false → ∃ hashes, r.transactionHashes = .ok hashes ∧
        transactions = listJson hash32Json hashes) ∧
      (full = true → ∃ infos, r.transactionInfos = .ok infos ∧
        transactions = listJson transactionInfoJson infos) := by
  unfold BlockRecord.blockJson at h
  obtain ⟨size, -, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨uncles, -, h⟩ := EthLib.Base.bind_ok_iff.mp h
  refine ⟨size, uncles, ?_⟩
  cases full
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨t, ht, h⟩ := EthLib.Base.bind_ok_iff.mp h
    obtain ⟨hashes, hh, rfl⟩ := EthLib.Base.map_ok_iff.mp ht
    exact ⟨_, (Except.ok.inj h).symm, fun _ => ⟨hashes, hh, rfl⟩, fun hf => absurd hf (by simp)⟩
  · simp only [↓reduceIte] at h
    obtain ⟨t, ht, h⟩ := EthLib.Base.bind_ok_iff.mp h
    obtain ⟨infos, hi, rfl⟩ := EthLib.Base.map_ok_iff.mp ht
    exact ⟨_, (Except.ok.inj h).symm, fun hf => absurd hf (by simp), fun _ => ⟨infos, hi, rfl⟩⟩

/-- The object of a transaction names the hash that the transaction has, from any first index. -/
private theorem hashes_of_zipIdx {r : BlockRecord} :
    ∀ (l : List Transaction) (n : Nat) (infos : List TransactionInfo),
      (l.zipIdx n).mapM (fun (tx, index) => r.transactionInfo index tx) = .ok infos →
      (l.mapM fun tx => (transactionHash tx).mapError fun _ => BlockRecord.encodingError
        "transaction hash") = .ok (infos.map (·.hash)) := by
  intro l
  induction l with
  | nil =>
    intro n infos h
    simp only [List.zipIdx_nil, List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    simp [← h, pure, Except.pure]
  | cons tx l ih =>
    intro n infos h
    obtain ⟨info, rest, hi, hrest, rfl⟩ := EthLib.Base.mapM_cons_ok.mp
      (by simpa only [List.zipIdx_cons] using h)
    obtain ⟨sender, hash, -, hh, rfl⟩ := BlockRecord.transactionInfo_eq_ok.mp hi
    refine EthLib.Base.mapM_cons_ok.mpr ⟨hash, rest.map (·.hash), ?_, ih _ _ hrest, rfl⟩
    exact EthLib.Base.mapError_ok_iff.mpr hh

/-- No name of the block object comes twice, among the names of its header and of its block. -/
theorem nodup_headerNames_append_blockNames (fork : Fork) :
    (headerNames fork ++ blockNames fork).Nodup := by
  cases fork <;> decide

/-- The fields of the block object have distinct names. -/
private theorem names_distinct_block {fork : Fork} (hash : Hash32) (h : Header fork) (size : Nat)
    (uncles : List Hash32) (transactions : Lean.Json)
    (withdrawals : Since .shapella fork (List Withdrawal)) :
    (headerFields hash h ++ blockFields size uncles transactions withdrawals).Pairwise
      fun a b => a.1 ≠ b.1 := by
  have := nodup_headerNames_append_blockNames fork
  rw [← names_headerFields hash h, ← names_blockFields size uncles transactions withdrawals,
    ← List.map_append, List.Nodup, List.pairwise_map] at this
  exact this

/-- The object that the writer gives for a block has exactly the names of its header and its block.

The names of the header are those of the fork of the block. -/
theorem keys_blockJson {r : BlockRecord} {full : Bool} {j : Lean.Json}
    (h : r.blockJson full = .ok j) :
    ∃ kvs, j = .obj kvs ∧
      (kvs.toList.map Prod.fst).Perm (headerNames r.fork ++ blockNames r.fork) := by
  obtain ⟨size, uncles, t, rfl, -, -⟩ := blockJson_ok h
  have hd := names_distinct_block r.hash r.block.header size uncles t r.block.withdrawals
  obtain ⟨kvs, hobj, -, hmem, hd'⟩ := toList_mkObj hd
  refine ⟨kvs, hobj, ?_⟩
  have nodup : ∀ l : List (String × Lean.Json), (l.Pairwise fun a b => a.1 ≠ b.1) → l.Nodup :=
    fun l h => h.imp_of_mem (fun {a b} _ _ hne heq => hne (by rw [heq]))
  have hp := (List.perm_ext_iff_of_nodup (nodup _ hd') (nodup _ hd)).mpr hmem
  rw [← names_headerFields r.hash r.block.header, ← names_blockFields size uncles t,
    ← List.map_append]
  exact hp.map _

/-- On each name of the header, the block object holds what the header object holds. -/
theorem getObjVal_blockJson {r : BlockRecord} {full : Bool} {j : Lean.Json}
    (h : r.blockJson full = .ok j) {k : String} (hk : k ∈ headerNames r.fork) :
    j.getObjVal? k = (ChainView.headerObject r).getObjVal? k := by
  obtain ⟨size, uncles, t, rfl, -, -⟩ := blockJson_ok h
  have hd := names_distinct_block r.hash r.block.header size uncles t r.block.withdrawals
  have hdh := names_distinct_headerFields r.hash r.block.header
  rw [← names_headerFields r.hash r.block.header, List.mem_map] at hk
  obtain ⟨⟨k', v⟩, hm, rfl⟩ := hk
  have hm' : (k', v) ∈ headerFields r.hash r.block.header ++
      blockFields size uncles t r.block.withdrawals := List.mem_append_left _ hm
  rw [EthLib.Serialization.Ssz.getObjVal?_mkObj hd hm']
  exact (EthLib.Serialization.Ssz.getObjVal?_mkObj hdh hm).symm

/-- When transactions are not hydrated, the block object lists their hashes. -/
theorem transactions_blockJson_false {r : BlockRecord} {j : Lean.Json}
    (h : r.blockJson false = .ok j) :
    ∃ hashes, r.transactionHashes = .ok hashes ∧
      j.getObjVal? "transactions" = .ok (listJson hash32Json hashes) := by
  obtain ⟨size, uncles, t, rfl, hf, -⟩ := blockJson_ok h
  obtain ⟨hashes, hh, rfl⟩ := hf rfl
  refine ⟨hashes, hh, EthLib.Serialization.Ssz.getObjVal?_mkObj
    (names_distinct_block r.hash r.block.header _ _ _ _) ?_⟩
  simp [blockFields]

/-- When transactions are hydrated, the block object lists their objects. -/
theorem transactions_blockJson_true {r : BlockRecord} {j : Lean.Json}
    (h : r.blockJson true = .ok j) :
    ∃ infos, r.transactionInfos = .ok infos ∧
      j.getObjVal? "transactions" = .ok (listJson transactionInfoJson infos) := by
  obtain ⟨size, uncles, t, rfl, -, hf⟩ := blockJson_ok h
  obtain ⟨infos, hi, rfl⟩ := hf rfl
  refine ⟨infos, hi, EthLib.Serialization.Ssz.getObjVal?_mkObj
    (names_distinct_block r.hash r.block.header _ _ _ _) ?_⟩
  simp [blockFields]

/-- The objects of the transactions carry the hashes of the transactions, in the same order. -/
theorem transactionHashes_of_transactionInfos {r : BlockRecord} {infos : List TransactionInfo}
    (h : r.transactionInfos = .ok infos) : r.transactionHashes = .ok (infos.map (·.hash)) :=
  hashes_of_zipIdx _ _ _ h

/-- There is one object for each transaction of the block. -/
theorem length_transactionInfos {r : BlockRecord} {infos : List TransactionInfo}
    (h : r.transactionInfos = .ok infos) : infos.length = r.block.transactions.length := by
  simpa using EthLib.Base.mapM_ok_length h

/-- There is one hash for each transaction of the block. -/
theorem length_transactionHashes {r : BlockRecord} {hashes : List Hash32}
    (h : r.transactionHashes = .ok hashes) : hashes.length = r.block.transactions.length :=
  EthLib.Base.mapM_ok_length h

end EthLib.Execution.Rpc
