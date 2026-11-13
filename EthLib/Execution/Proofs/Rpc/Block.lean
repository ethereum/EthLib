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

Its transactions are their hashes, or their objects, which carry the same hashes in the same order.

Each list has one entry for each transaction of the block.

The size of the object is the length of the RLP form of the block, in bytes.

The object lists the hashes of the headers of the ommers, in order.

Each property holds whenever the writer gives an object.

The writer fails when the node cannot encode the block, or recover a sender in it.

In a valid view, a canonical block after the lowest has an object exactly when it has an RLP form.

From Fusaka, the size check gives that form, of at most 8 MiB, so the object exists.
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
        transactions = listJson transactionInfoJson infos) ∧
      r.size = .ok size ∧ r.block.ommers.mapM (fun o => o.2.hash.mapError fun _ =>
        BlockRecord.encodingError "ommer hash") = .ok uncles := by
  unfold BlockRecord.blockJson at h
  obtain ⟨size, hsize, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨uncles, huncles, h⟩ := EthLib.Base.bind_ok_iff.mp h
  refine ⟨size, uncles, ?_⟩
  cases full
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨t, ht, h⟩ := EthLib.Base.bind_ok_iff.mp h
    obtain ⟨hashes, hh, rfl⟩ := EthLib.Base.map_ok_iff.mp ht
    exact ⟨_, (Except.ok.inj h).symm, fun _ => ⟨hashes, hh, rfl⟩, fun hf => absurd hf (by simp),
      hsize, huncles⟩
  · simp only [↓reduceIte] at h
    obtain ⟨t, ht, h⟩ := EthLib.Base.bind_ok_iff.mp h
    obtain ⟨infos, hi, rfl⟩ := EthLib.Base.map_ok_iff.mp ht
    exact ⟨_, (Except.ok.inj h).symm, fun hf => absurd hf (by simp), fun _ => ⟨infos, hi, rfl⟩,
      hsize, huncles⟩

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
  obtain ⟨size, uncles, t, rfl, hf, -, -⟩ := blockJson_ok h
  obtain ⟨hashes, hh, rfl⟩ := hf rfl
  refine ⟨hashes, hh, EthLib.Serialization.Ssz.getObjVal?_mkObj
    (names_distinct_block r.hash r.block.header _ _ _ _) ?_⟩
  simp [blockFields]

/-- When transactions are hydrated, the block object lists their objects. -/
theorem transactions_blockJson_true {r : BlockRecord} {j : Lean.Json}
    (h : r.blockJson true = .ok j) :
    ∃ infos, r.transactionInfos = .ok infos ∧
      j.getObjVal? "transactions" = .ok (listJson transactionInfoJson infos) := by
  obtain ⟨size, uncles, t, rfl, -, hf, -⟩ := blockJson_ok h
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

/-- When the writer gives an object, its size is the length of the RLP form of the block. -/
theorem size_blockJson {r : BlockRecord} {full : Bool} {j : Lean.Json}
    (h : r.blockJson full = .ok j) :
    ∃ raw, r.rawBlock = .ok raw ∧ j.getObjVal? "size" = .ok (quantityJson raw.size) := by
  obtain ⟨size, uncles, t, rfl, -, -, hsize, -⟩ := blockJson_ok h
  obtain ⟨raw, hraw, rfl⟩ := EthLib.Base.map_ok_iff.mp hsize
  refine ⟨raw, hraw, EthLib.Serialization.Ssz.getObjVal?_mkObj
    (names_distinct_block r.hash r.block.header _ _ _ _) ?_⟩
  simp [blockFields]

/-- When the writer gives an object, its uncles are the hashes of the ommer headers, in order. -/
theorem uncles_blockJson {r : BlockRecord} {full : Bool} {j : Lean.Json}
    (h : r.blockJson full = .ok j) :
    ∃ hashes, r.block.ommers.mapM (fun o => o.2.hash) = .ok hashes ∧
      j.getObjVal? "uncles" = .ok (listJson hash32Json hashes) := by
  obtain ⟨size, uncles, t, rfl, -, -, -, huncles⟩ := blockJson_ok h
  obtain ⟨hlen, hget⟩ := EthLib.Base.mapM_eq_ok_iff.mp huncles
  refine ⟨uncles, EthLib.Base.mapM_eq_ok_iff.mpr ⟨hlen, fun k hk =>
    EthLib.Base.mapError_ok_iff.mp (hget k hk)⟩, EthLib.Serialization.Ssz.getObjVal?_mkObj
    (names_distinct_block r.hash r.block.header _ _ _ _) ?_⟩
  simp [blockFields]

/-- Each item of a list that has an RLP form has one too. -/
private theorem encode_of_mem_list {items : List Serialization.Rlp.Item} {e : ByteArray}
    (h : Serialization.Rlp.encode (.list items) = .ok e) :
    ∀ x ∈ items, ∃ e', Serialization.Rlp.encode x = .ok e' := by
  obtain ⟨payload, -, hjoin, -, -⟩ := Serialization.Rlp.encode_list_ok items e h
  clear h
  induction items generalizing payload with
  | nil => simp
  | cons item rest ih =>
    rw [Serialization.Rlp.joinEncodings_cons] at hjoin
    obtain ⟨head, hhead, hjoin⟩ := EthLib.Base.bind_ok_iff.mp hjoin
    obtain ⟨tail, htail, -⟩ := EthLib.Base.bind_ok_iff.mp hjoin
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨head, hhead⟩
    · exact ih tail htail x hx

/-- A transaction whose item in a body has an RLP form has bytes. -/
private theorem encodeTransaction_of_bodyItem {tx : Transaction} {item : Serialization.Rlp.Item}
    {e : ByteArray} (h : bodyItem tx = .ok item) (he : Serialization.Rlp.encode item = .ok e) :
    ∃ bytes, encodeTransaction tx = .ok bytes := by
  cases tx <;> simp only [bodyItem] at h
  · cases h
    exact ⟨e, he⟩
  all_goals
    obtain ⟨bytes, hb, -⟩ := EthLib.Base.map_ok_iff.mp h
    exact ⟨bytes, hb⟩

/-- A block with an RLP form has a hash for each of its ommers and each of its transactions. -/
private theorem hashes_of_rawBlock {r : BlockRecord} {raw : ByteArray} (h : r.rawBlock = .ok raw) :
    (∀ o ∈ r.block.ommers, ∃ hash, o.2.hash = .ok hash) ∧
      ∀ tx ∈ r.block.transactions, ∃ hash, transactionHash tx = .ok hash := by
  unfold BlockRecord.rawBlock at h
  obtain ⟨items, hitems, h⟩ := EthLib.Base.bind_ok_iff.mp h
  have hraw := EthLib.Base.mapError_ok_iff.mp h
  have hitems := EthLib.Base.mapError_ok_iff.mp hitems
  unfold Blocks.bodyItems at hitems
  obtain ⟨txItems, htx, hitems⟩ := EthLib.Base.bind_ok_iff.mp hitems
  have htx := EthLib.Base.mapError_ok_iff.mp htx
  cases hitems
  unfold Blocks.Block.encode Blocks.Block.toItem at hraw
  have hall := encode_of_mem_list hraw
  constructor
  · obtain ⟨eo, heo⟩ := hall (Blocks.ommersItem r.block.ommers) (by simp)
    intro o ho
    obtain ⟨e, he⟩ := encode_of_mem_list heo (Serialization.Rlp.Codec.toItem o.2)
      (List.mem_map.mpr ⟨o, ho, rfl⟩)
    exact ⟨_, by simp only [Header.hash, Serialization.Rlp.Codec.encode, he, bind, Except.bind,
      pure, Except.pure]; rfl⟩
  · obtain ⟨et, het⟩ := hall (Serialization.Rlp.Codec.toItem txItems) (by simp)
    intro tx htxm
    obtain ⟨item, hitem, hb⟩ := EthLib.Base.exists_mem_of_mapM_ok htx htxm
    obtain ⟨e, he⟩ := encode_of_mem_list het item (by simpa [Serialization.Rlp.Codec.toItem])
    obtain ⟨bytes, hbytes⟩ := encodeTransaction_of_bodyItem hb he
    exact ⟨_, by simp only [transactionHash, hbytes, bind, Except.bind, pure, Except.pure]; rfl⟩

/-- The writer gives an object when the block has an RLP form and each signature names a sender. -/
private theorem blockJson_of_rawBlock {r : BlockRecord} (full : Bool) {raw : ByteArray}
    (h : r.rawBlock = .ok raw)
    (hsender : ∀ tx ∈ r.block.transactions, ∃ sender, recoverSender r.fork tx = .ok sender) :
    ∃ j, r.blockJson full = .ok j := by
  obtain ⟨hom, htx⟩ := hashes_of_rawBlock h
  obtain ⟨uncles, hu⟩ := EthLib.Base.mapM_exists_ok (xs := r.block.ommers)
    (f := fun o => o.2.hash.mapError fun _ => BlockRecord.encodingError "ommer hash")
    fun o ho => by
      obtain ⟨hash, hh⟩ := hom o ho
      exact ⟨hash, EthLib.Base.mapError_ok_iff.mpr hh⟩
  obtain ⟨hashes, hhashes⟩ := EthLib.Base.mapM_exists_ok (xs := r.block.transactions)
    (f := fun tx => (transactionHash tx).mapError fun _ =>
      BlockRecord.encodingError "transaction hash")
    fun tx hm => by
      obtain ⟨hash, hh⟩ := htx tx hm
      exact ⟨hash, EthLib.Base.mapError_ok_iff.mpr hh⟩
  obtain ⟨infos, hinfos⟩ := EthLib.Base.mapM_exists_ok
    (xs := r.block.transactions.zipIdx) (f := fun (tx, index) => r.transactionInfo index tx)
    fun p hp => by
      have hm := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hp)
      obtain ⟨sender, hs⟩ := hsender p.1 hm
      obtain ⟨hash, hh⟩ := htx p.1 hm
      exact ⟨_, BlockRecord.transactionInfo_eq_ok.mpr ⟨sender, hash, hs, hh, rfl⟩⟩
  have hsize : r.size = .ok raw.size := by simp [BlockRecord.size, h, Functor.map, Except.map]
  cases full
  · exact ⟨_, by simp [BlockRecord.blockJson, hsize, hu, BlockRecord.transactionHashes, hhashes,
      bind, Except.bind, Functor.map, Except.map, pure, Except.pure]; rfl⟩
  · exact ⟨_, by simp [BlockRecord.blockJson, hsize, hu, BlockRecord.transactionInfos, hinfos,
      bind, Except.bind, Functor.map, Except.map, pure, Except.pure]; rfl⟩

namespace ChainView

/-- In a valid view, each signature of a canonical block after the lowest names a sender. -/
private theorem Valid.exists_recoverSender {v : ChainView} {checkSeal : Bool}
    (hv : v.Valid checkSeal) {i : Nat} (hi : i + 1 < v.canonical.length) :
    ∀ tx ∈ v.canonical[i + 1].block.transactions,
      ∃ sender, recoverSender v.canonical[i + 1].fork tx = .ok sender := by
  intro tx htx
  obtain ⟨index, hlt, hget⟩ := List.getElem_of_mem htx
  obtain ⟨_, _, _, _, _, -, -, -, -, hnext⟩ :=
    hv.applyTransaction_at hi (index := index) (by rw [List.getElem?_eq_getElem hlt, hget])
  obtain ⟨inc, -, hinc, -⟩ := Blocks.applyTransaction_eq_ok hnext
  exact ⟨inc.sender, (checkInclusion_ok hinc).1⟩

/-- In a valid view, take a canonical block after the lowest.

The writer gives its object exactly when the block has an RLP form.

This holds whether or not the transactions are hydrated. -/
theorem Valid.exists_blockJson_eq_ok_iff {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal)
    {i : Nat} (hi : i + 1 < v.canonical.length) (full : Bool) :
    (∃ j, v.canonical[i + 1].blockJson full = .ok j) ↔
      ∃ raw, v.canonical[i + 1].rawBlock = .ok raw := by
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨raw, hraw, -⟩ := size_blockJson hj
    exact ⟨raw, hraw⟩
  · rintro ⟨raw, hraw⟩
    exact blockJson_of_rawBlock full hraw (Valid.exists_recoverSender hv hi)

/-- In a valid view, from Fusaka, a canonical block after the lowest has an RLP form.

That form has at most 8 MiB, that is `8 * 2 ^ 20` bytes. -/
theorem Valid.exists_rawBlock_of_fusaka_le {v : ChainView} {checkSeal : Bool}
    (hv : v.Valid checkSeal) {i : Nat} (hi : i + 1 < v.canonical.length)
    (hf : .fusaka ≤ v.canonical[i + 1].fork) :
    ∃ raw, v.canonical[i + 1].rawBlock = .ok raw ∧ raw.size ≤ Blocks.MAX_RLP_BLOCK_SIZE := by
  obtain ⟨hst, -⟩ := hv.follows i hi
  obtain ⟨-, -, hcheck, -⟩ := Blocks.stateTransition_eq_ok hst
  unfold Blocks.checkBlock at hcheck
  obtain ⟨items, hitems, hcheck⟩ := EthLib.Base.bind_ok_iff.mp hcheck
  obtain ⟨_, hsize, -⟩ := EthLib.Base.bind_ok_iff.mp hcheck
  rcases (Blocks.validateBlockSize_eq_ok_iff items).mp hsize with hlt | ⟨bytes, hbytes, hle⟩
  · exact absurd hf (Nat.not_le_of_lt hlt)
  · refine ⟨bytes, ?_, hle⟩
    simp [BlockRecord.rawBlock, hitems, hbytes, Except.mapError, bind, Except.bind]

/-- In a valid view, from Fusaka, the writer gives the object of a canonical block after the lowest.

Its size is the length of the RLP form of the block, at most 8 MiB. -/
theorem Valid.exists_blockJson_of_fusaka_le {v : ChainView} {checkSeal : Bool}
    (hv : v.Valid checkSeal) {i : Nat} (hi : i + 1 < v.canonical.length)
    (hf : .fusaka ≤ v.canonical[i + 1].fork) (full : Bool) :
    ∃ j raw, v.canonical[i + 1].blockJson full = .ok j ∧ v.canonical[i + 1].rawBlock = .ok raw ∧
      j.getObjVal? "size" = .ok (quantityJson raw.size) ∧
        raw.size ≤ Blocks.MAX_RLP_BLOCK_SIZE := by
  obtain ⟨raw, hraw, hle⟩ := Valid.exists_rawBlock_of_fusaka_le hv hi hf
  obtain ⟨j, hj⟩ := (Valid.exists_blockJson_eq_ok_iff hv hi full).mpr ⟨raw, hraw⟩
  obtain ⟨raw', hraw', hs⟩ := size_blockJson hj
  cases hraw.symm.trans hraw'
  exact ⟨j, raw, hj, hraw, hs, hle⟩

end ChainView

end EthLib.Execution.Rpc
