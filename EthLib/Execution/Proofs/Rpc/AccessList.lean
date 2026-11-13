module

public import EthLib.Execution.Rpc.AccessList
public import EthLib.Execution.Proofs.Rpc.Base
public import EthLib.Execution.Proofs.Rpc.Raw
public import EthLib.Execution.Proofs.Blocks.BlockAccessList
public import EthLib.Base.Proofs.U256
import all Lean.Data.Json.Basic

/-!
# Proofs: block access-list queries

The JSON reader recovers every list that the writer writes, in the same order.

The raw getter decodes to the retained list too.

The hash guarantee holds in a valid view, from Glamsterdam.

There, a retained list of a canonical block after the lowest hashes to its header field.

The lowest block, side blocks and the pending block are inputs.

No transition checks their retained lists.
-/

public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Serialization.Rlp (Codec)
open EthLib.Execution.Blocks
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- The fields of a written object read back as a permutation of its distinct fields. -/
private theorem blockAccessFields_mkObj {pairs : List (String × Json)}
    (hd : pairs.Pairwise fun a b => a.1 ≠ b.1) :
    ∃ fs, blockAccessFields (pairs.map Prod.fst) (Json.mkObj pairs) = .ok fs ∧ fs.Perm pairs := by
  -- Object keys may be reordered, so the reader sees a permutation of the written pairs.
  obtain ⟨kvs, hobj, -, hmem, hd'⟩ := toList_mkObj hd
  have nodup : ∀ l : List (String × Json), (l.Pairwise fun a b => a.1 ≠ b.1) → l.Nodup :=
    fun l h => h.imp_of_mem (fun {a b} _ _ hne heq => hne (by rw [heq]))
  have hp := (List.perm_ext_iff_of_nodup (nodup _ hd') (nodup _ hd)).mpr hmem
  refine ⟨kvs.toList, ?_, hp⟩
  simp only [hobj, blockAccessFields, hasExactly_of_perm hp, ↓reduceIte]

/-- A storage word reads back from its 32-byte data form. -/
theorem storageWordOfJson_wordJson (word : U256) :
    storageWordOfJson (wordJson word) = .ok word := by
  unfold storageWordOfJson wordJson hash32
  rw [fixed_dataJson]
  change Except.ok (U256.fromBeBytes (U256.toBeBytes word)) = .ok word
  rw [U256.fromBeBytes_toBeBytes]

/-- Every `StorageChange` reads back from its JSON object. -/
theorem storageChangeOfJson_storageChangeJson (c : StorageChange) :
    storageChangeOfJson (storageChangeJson c) = .ok c := by
  let pairs : List (String × Json) := [("index", quantityJson c.index.toNat),
    ("value", wordJson c.value)]
  have hd : pairs.Pairwise (fun a b => a.1 ≠ b.1) := by simp [pairs]
  obtain ⟨fs, hfs, hp⟩ := blockAccessFields_mkObj hd
  have f0 := field_of_perm (what := "block access list") hp hd
    (k := "index") (v := quantityJson c.index.toNat) (by simp [pairs])
  have f1 := field_of_perm (what := "block access list") hp hd
    (k := "value") (v := wordJson c.value) (by simp [pairs])
  unfold storageChangeOfJson storageChangeJson
  change (do
    let fs ← blockAccessFields (pairs.map Prod.fst) (Json.mkObj pairs)
    return {
      index := ← uint32 "index" (← field "block access list" fs "index")
      value := ← storageWordOfJson (← field "block access list" fs "value")
    } : Read StorageChange) = .ok c
  rw [hfs]
  simp only [bind, Except.bind, f0, f1,
    uint32_quantityJson,
    storageWordOfJson_wordJson, pure, Except.pure]

/-- Every `BalanceChange` reads back from its JSON object. -/
theorem balanceChangeOfJson_balanceChangeJson (c : BalanceChange) :
    balanceChangeOfJson (balanceChangeJson c) = .ok c := by
  let pairs : List (String × Json) := [("index", quantityJson c.index.toNat),
    ("value", quantityJson c.balance.toNat)]
  have hd : pairs.Pairwise (fun a b => a.1 ≠ b.1) := by simp [pairs]
  obtain ⟨fs, hfs, hp⟩ := blockAccessFields_mkObj hd
  have f0 := field_of_perm (what := "block access list") hp hd
    (k := "index") (v := quantityJson c.index.toNat) (by simp [pairs])
  have f1 := field_of_perm (what := "block access list") hp hd
    (k := "value") (v := quantityJson c.balance.toNat) (by simp [pairs])
  unfold balanceChangeOfJson balanceChangeJson
  change (do
    let fs ← blockAccessFields (pairs.map Prod.fst) (Json.mkObj pairs)
    return {
      index := ← uint32 "index" (← field "block access list" fs "index")
      balance := ← uint256 "value" (← field "block access list" fs "value")
    } : Read BalanceChange) = .ok c
  rw [hfs]
  simp only [bind, Except.bind, f0, f1,
    uint32_quantityJson,
    uint256_quantityJson, pure, Except.pure]

/-- Every `NonceChange` reads back from its JSON object. -/
theorem nonceChangeOfJson_nonceChangeJson (c : NonceChange) :
    nonceChangeOfJson (nonceChangeJson c) = .ok c := by
  let pairs : List (String × Json) := [("index", quantityJson c.index.toNat),
    ("value", quantityJson c.nonce.toNat)]
  have hd : pairs.Pairwise (fun a b => a.1 ≠ b.1) := by simp [pairs]
  obtain ⟨fs, hfs, hp⟩ := blockAccessFields_mkObj hd
  have f0 := field_of_perm (what := "block access list") hp hd
    (k := "index") (v := quantityJson c.index.toNat) (by simp [pairs])
  have f1 := field_of_perm (what := "block access list") hp hd
    (k := "value") (v := quantityJson c.nonce.toNat) (by simp [pairs])
  unfold nonceChangeOfJson nonceChangeJson
  change (do
    let fs ← blockAccessFields (pairs.map Prod.fst) (Json.mkObj pairs)
    return {
      index := ← uint32 "index" (← field "block access list" fs "index")
      nonce := ← uint64 "value" (← field "block access list" fs "value")
    } : Read NonceChange) = .ok c
  rw [hfs]
  simp only [bind, Except.bind, f0, f1,
    uint32_quantityJson,
    uint64_toDigits, pure, Except.pure]

/-- Every `CodeChange` reads back from its JSON object. -/
theorem codeChangeOfJson_codeChangeJson (c : CodeChange) :
    codeChangeOfJson (codeChangeJson c) = .ok c := by
  let pairs : List (String × Json) := [("index", quantityJson c.index.toNat),
    ("code", dataJson c.code.data.toList)]
  have hd : pairs.Pairwise (fun a b => a.1 ≠ b.1) := by simp [pairs]
  obtain ⟨fs, hfs, hp⟩ := blockAccessFields_mkObj hd
  have f0 := field_of_perm (what := "block access list") hp hd
    (k := "index") (v := quantityJson c.index.toNat) (by simp [pairs])
  have f1 := field_of_perm (what := "block access list") hp hd
    (k := "code") (v := dataJson c.code.data.toList) (by simp [pairs])
  unfold codeChangeOfJson codeChangeJson
  change (do
    let fs ← blockAccessFields (pairs.map Prod.fst) (Json.mkObj pairs)
    return {
      index := ← uint32 "index" (← field "block access list" fs "index")
      code := ← bytes "code" (← field "block access list" fs "code") } : Read CodeChange) = .ok c
  rw [hfs]
  simp only [bind, Except.bind, f0, f1,
    uint32_quantityJson,
    bytes_dataJson, pure, Except.pure]

/-- A `SlotChanges` value reads back from its JSON object, including an empty change list. -/
theorem slotChangesOfJson_slotChangesJson (c : SlotChanges) :
    slotChangesOfJson (slotChangesJson c) = .ok c := by
  let pairs : List (String × Json) := [("key", wordJson c.slot),
    ("changes", listJson storageChangeJson c.changes)]
  have hd : pairs.Pairwise (fun a b => a.1 ≠ b.1) := by simp [pairs]
  obtain ⟨fs, hfs, hp⟩ := blockAccessFields_mkObj hd
  have f0 := field_of_perm (what := "block access list") hp hd
    (k := "key") (v := wordJson c.slot) (by simp [pairs])
  have f1 := field_of_perm (what := "block access list") hp hd
    (k := "changes") (v := listJson storageChangeJson c.changes) (by simp [pairs])
  unfold slotChangesOfJson slotChangesJson
  change (do
    let fs ← blockAccessFields (pairs.map Prod.fst) (Json.mkObj pairs)
    return {
      slot := ← storageWordOfJson (← field "block access list" fs "key")
      changes := ← array "changes" storageChangeOfJson (← field "block access list" fs "changes")
    } : Read SlotChanges) = .ok c
  rw [hfs]
  simp only [bind, Except.bind, f0, f1,
    storageWordOfJson_wordJson,
    array_listJson_of _ storageChangeOfJson_storageChangeJson, pure, Except.pure]

/-- An `AccountChanges` value reads back from its JSON object, including empty change lists. -/
theorem accountChangesOfJson_accountChangesJson (c : AccountChanges) :
    accountChangesOfJson (accountChangesJson c) = .ok c := by
  let pairs : List (String × Json) := [("address", dataJson c.address.toList),
    ("storageChanges", listJson slotChangesJson c.storageChanges),
    ("storageReads", listJson wordJson c.storageReads),
    ("balanceChanges", listJson balanceChangeJson c.balanceChanges),
    ("nonceChanges", listJson nonceChangeJson c.nonceChanges),
    ("codeChanges", listJson codeChangeJson c.codeChanges)]
  have hd : pairs.Pairwise (fun a b => a.1 ≠ b.1) := by simp [pairs]
  obtain ⟨fs, hfs, hp⟩ := blockAccessFields_mkObj hd
  have f0 := field_of_perm (what := "block access list") hp hd
    (k := "address") (v := dataJson c.address.toList) (by simp [pairs])
  have f1 := field_of_perm (what := "block access list") hp hd
    (k := "storageChanges") (v := listJson slotChangesJson c.storageChanges) (by simp [pairs])
  have f2 := field_of_perm (what := "block access list") hp hd
    (k := "storageReads") (v := listJson wordJson c.storageReads) (by simp [pairs])
  have f3 := field_of_perm (what := "block access list") hp hd
    (k := "balanceChanges") (v := listJson balanceChangeJson c.balanceChanges) (by simp [pairs])
  have f4 := field_of_perm (what := "block access list") hp hd
    (k := "nonceChanges") (v := listJson nonceChangeJson c.nonceChanges) (by simp [pairs])
  have f5 := field_of_perm (what := "block access list") hp hd
    (k := "codeChanges") (v := listJson codeChangeJson c.codeChanges) (by simp [pairs])
  unfold accountChangesOfJson accountChangesJson
  change (do
    let fs ← blockAccessFields (pairs.map Prod.fst) (Json.mkObj pairs)
    return {
      address := ← address "address" (← field "block access list" fs "address")
      storageChanges := ← array "storageChanges" slotChangesOfJson
        (← field "block access list" fs "storageChanges")
      storageReads := ← array "storageReads" storageWordOfJson
        (← field "block access list" fs "storageReads")
      balanceChanges := ← array "balanceChanges" balanceChangeOfJson
        (← field "block access list" fs "balanceChanges")
      nonceChanges := ← array "nonceChanges" nonceChangeOfJson
        (← field "block access list" fs "nonceChanges")
      codeChanges := ← array "codeChanges" codeChangeOfJson
        (← field "block access list" fs "codeChanges")
    } : Read AccountChanges) = .ok c
  rw [hfs]
  simp only [bind, Except.bind, f0, f1, f2, f3, f4, f5,
    address_dataJson,
    array_listJson_of _ slotChangesOfJson_slotChangesJson,
    array_listJson_of _ storageWordOfJson_wordJson,
    array_listJson_of _ balanceChangeOfJson_balanceChangeJson,
    array_listJson_of _ nonceChangeOfJson_nonceChangeJson,
    array_listJson_of _ codeChangeOfJson_codeChangeJson, pure, Except.pure]

/-- Every list reads back from the JSON writer, with all account and change orders unchanged. -/
theorem blockAccessListOfJson_blockAccessListJson (bal : BlockAccessList) :
    blockAccessListOfJson (blockAccessListJson bal) = .ok bal :=
  array_listJson_of _ accountChangesOfJson_accountChangesJson bal

namespace BlockRecord

/-- A retained list is returned exactly from Glamsterdam on, when it is present. -/
theorem retainedAccessList_eq_ok_iff {r : BlockRecord} {bal : BlockAccessList} :
    r.retainedAccessList = .ok bal ↔ .glamsterdam ≤ r.fork ∧ r.accessList = some bal := by
  unfold retainedAccessList
  split
  · rename_i h
    simp only [reduceCtorEq, false_iff, not_and]
    intro hf
    exact absurd hf (Nat.not_le_of_lt h)
  · rename_i h
    have hf : .glamsterdam ≤ r.fork := Nat.le_of_not_lt h
    cases r.accessList <;> simp [hf]

/-- A JSON answer is exactly the JSON form of an available list from Glamsterdam. -/
theorem blockAccessList_eq_ok_iff {r : BlockRecord} {j : Json} :
    r.blockAccessList = .ok j ↔ ∃ bal, .glamsterdam ≤ r.fork ∧
      r.accessList = some bal ∧ j = blockAccessListJson bal := by
  unfold blockAccessList
  rw [map_ok_iff]
  constructor
  · rintro ⟨bal, hb, hj⟩
    exact ⟨bal, (retainedAccessList_eq_ok_iff.mp hb).1,
      (retainedAccessList_eq_ok_iff.mp hb).2, hj.symm⟩
  · rintro ⟨bal, hf, hb, hj⟩
    exact ⟨bal, retainedAccessList_eq_ok_iff.mpr ⟨hf, hb⟩, hj.symm⟩

/-- A raw answer is exactly an encoding of an available list from Glamsterdam. -/
theorem rawBlockAccessList_eq_ok_iff {r : BlockRecord} {raw : ByteArray} :
    r.rawBlockAccessList = .ok raw ↔ ∃ bal, .glamsterdam ≤ r.fork ∧
      r.accessList = some bal ∧ Codec.encode bal = .ok raw := by
  unfold rawBlockAccessList
  rw [bind_ok_iff]
  constructor
  · rintro ⟨bal, hb, he⟩
    exact ⟨bal, (retainedAccessList_eq_ok_iff.mp hb).1,
      (retainedAccessList_eq_ok_iff.mp hb).2, mapError_ok_iff.mp he⟩
  · rintro ⟨bal, hf, hb, he⟩
    exact ⟨bal, retainedAccessList_eq_ok_iff.mpr ⟨hf, hb⟩, mapError_ok_iff.mpr he⟩

/-- Decoding a successful raw answer recovers the retained list. -/
theorem decode_of_rawBlockAccessList_eq_ok {r : BlockRecord} {raw : ByteArray}
    (h : r.rawBlockAccessList = .ok raw) :
    ∃ bal, r.retainedAccessList = .ok bal ∧ Codec.encode bal = .ok raw ∧
      Codec.decode raw = .ok bal := by
  obtain ⟨bal, hb, he⟩ := bind_ok_iff.mp h
  have he := mapError_ok_iff.mp he
  exact ⟨bal, hb, he, Codec.decode_encode he⟩

/-- The JSON and RLP answers both read back as the retained list of the record. -/
theorem blockAccessList_forms {r : BlockRecord} {j : Json} {raw : ByteArray}
    (hj : r.blockAccessList = .ok j) (hr : r.rawBlockAccessList = .ok raw) :
    ∃ bal, r.accessList = some bal ∧ blockAccessListOfJson j = .ok bal ∧
      Codec.decode raw = .ok bal := by
  obtain ⟨bal, hb, -, hd⟩ := decode_of_rawBlockAccessList_eq_ok hr
  have hj : j = blockAccessListJson bal := by
    unfold blockAccessList at hj
    rw [hb] at hj
    exact (Except.ok.inj hj).symm
  exact ⟨bal, (retainedAccessList_eq_ok_iff.mp hb).2,
    hj ▸ blockAccessListOfJson_blockAccessListJson bal, hd⟩

/-- A block before Glamsterdam is rejected before its retained list is read. -/
theorem retainedAccessList_of_lt {r : BlockRecord} (h : r.fork < .glamsterdam) :
    r.retainedAccessList =
      .error (resourceNotFound.toRpcError (some (.str "block predates Amsterdam"))) := by
  simp [retainedAccessList, h]

/-- From Glamsterdam, an unavailable list has the pruning error of the source. -/
theorem retainedAccessList_pruned {r : BlockRecord} (hf : .glamsterdam ≤ r.fork)
    (h : r.accessList = none) :
    r.retainedAccessList = .error (prunedHistoryUnavailable.toRpcError none) := by
  have hpre : ¬r.fork < .glamsterdam := Nat.not_lt_of_ge hf
  simp [retainedAccessList, hpre, h]

end BlockRecord

namespace ChainView

/-- The JSON RPC name dispatches a successfully read block parameter to its view method. -/
theorem call_blockAccessList {v : ChainView} {j : Json} {p : BlockParam}
    (hp : blockNumberOrTagOrHash "block" j = .ok p) :
    v.call "eth_getBlockAccessList" [j] = v.blockAccessList p := by
  change ((blockNumberOrTagOrHash "block" j).mapError RpcError.invalidParams >>=
    v.blockAccessList) = _
  rw [hp]
  rfl

/-- The raw RPC name writes the bytes returned by its view method as hexadecimal data. -/
theorem call_rawBlockAccessList {v : ChainView} {j : Json} {p : BlockParam}
    (hp : blockNumberOrTagOrHash "block" j = .ok p) :
    v.call "debug_getRawBlockAccessList" [j] =
      (fun raw => dataJson raw.data.toList) <$> v.rawBlockAccessList p := by
  change ((blockNumberOrTagOrHash "block" j).mapError RpcError.invalidParams >>= fun p =>
    (fun raw => dataJson raw.data.toList) <$> v.rawBlockAccessList p) = _
  rw [hp]
  rfl

/-- The JSON method answers `null` for `pending`, even if the view has a pending record. -/
@[simp] theorem blockAccessList_pending (v : ChainView) :
    v.blockAccessList (.tag .pending) = .ok .null := rfl

/-- A non-pending query uses the existing block resolver before reading a retained list. -/
theorem blockAccessList_of_ne {v : ChainView} {p : BlockParam} (hp : p ≠ .tag .pending) :
    v.blockAccessList p = v.resolve p >>= fun
      | none => .ok .null
      | some r => r.blockAccessList := by
  unfold blockAccessList
  split
  · exact absurd rfl hp
  · rfl

/-- A successful non-pending JSON query names either no block or the record supplying its list. -/
theorem blockAccessList_eq_ok_iff {v : ChainView} {p : BlockParam} {j : Json}
    (hp : p ≠ .tag .pending) :
    v.blockAccessList p = .ok j ↔
      (v.resolve p = .ok none ∧ j = .null) ∨
      ∃ r bal, v.resolve p = .ok (some r) ∧ .glamsterdam ≤ r.fork ∧
        r.accessList = some bal ∧ j = blockAccessListJson bal := by
  rw [blockAccessList_of_ne hp, bind_ok_iff]
  constructor
  · rintro ⟨found, hr, hj⟩
    cases found with
    | none => exact .inl ⟨hr, (Except.ok.inj hj).symm⟩
    | some r =>
      obtain ⟨bal, hf, hb, hj⟩ := BlockRecord.blockAccessList_eq_ok_iff.mp hj
      exact .inr ⟨r, bal, hr, hf, hb, hj⟩
  · rintro (⟨hr, rfl⟩ | ⟨r, bal, hr, hf, hb, hj⟩)
    · exact ⟨none, hr, rfl⟩
    · exact ⟨some r, hr, BlockRecord.blockAccessList_eq_ok_iff.mpr ⟨bal, hf, hb, hj⟩⟩

/-- A successful raw query encodes the retained list of the record that the resolver selects. -/
theorem rawBlockAccessList_eq_ok_iff {v : ChainView} {p : BlockParam} {raw : ByteArray} :
    v.rawBlockAccessList p = .ok raw ↔ ∃ r bal,
      v.resolve p = .ok (some r) ∧ .glamsterdam ≤ r.fork ∧
        r.accessList = some bal ∧ Codec.encode bal = .ok raw := by
  change v.ofBlock p BlockRecord.rawBlockAccessList = .ok raw ↔ _
  rw [ofBlock_eq_ok]
  constructor
  · rintro ⟨r, hr, hraw⟩
    obtain ⟨bal, hf, hb, he⟩ := BlockRecord.rawBlockAccessList_eq_ok_iff.mp hraw
    exact ⟨r, bal, hr, hf, hb, he⟩
  · rintro ⟨r, bal, hr, hf, hb, he⟩
    exact ⟨r, hr, BlockRecord.rawBlockAccessList_eq_ok_iff.mpr ⟨bal, hf, hb, he⟩⟩

/-- A successful query for a known non-pending block reads that block's retained list. -/
theorem blockAccessList_of_resolve {v : ChainView} {p : BlockParam} {r : BlockRecord}
    (hp : p ≠ .tag .pending) (hr : v.resolve p = .ok (some r)) :
    v.blockAccessList p = r.blockAccessList := by
  unfold blockAccessList
  split
  · exact absurd rfl hp
  · simp [hr, bind, Except.bind]

/-- For a non-pending query, both answers read back as the retained list of the resolved block. -/
theorem blockAccessList_forms {v : ChainView} {p : BlockParam} {j : Json} {raw : ByteArray}
    (hp : p ≠ .tag .pending) (hj : v.blockAccessList p = .ok j)
    (hr : v.rawBlockAccessList p = .ok raw) :
    ∃ r bal, v.resolve p = .ok (some r) ∧ r.accessList = some bal ∧
      blockAccessListOfJson j = .ok bal ∧ Codec.decode raw = .ok bal := by
  obtain ⟨r, hresolve, hraw⟩ := ofBlock_eq_ok.mp hr
  rw [blockAccessList_of_resolve hp hresolve] at hj
  obtain ⟨bal, hb, hjson, hd⟩ := r.blockAccessList_forms hj hraw
  exact ⟨r, bal, hresolve, hb, hjson, hd⟩

/-- In a valid view, a retained list of a canonical block after the lowest hashes to its header. -/
theorem Valid.accessList_hash {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal)
    {i : Nat} (hi : i + 1 < v.canonical.length) (hf : .glamsterdam ≤ v.canonical[i + 1].fork)
    {bal : BlockAccessList} (hb : v.canonical[i + 1].accessList = some bal) :
    BlockAccessList.hash bal = .ok (v.canonical[i + 1].block.header.blockAccessListHash hf) := by
  obtain ⟨hst, result, hbody, -, -, hkept⟩ := hv.follows i hi
  obtain ⟨-, -, -, hashes, output, roots, hh, hout, -, hchecks, -⟩ := stateTransition_eq_ok hst
  obtain ⟨hashes', hh', hout', -⟩ := runBody_eq_ok.mp hbody
  -- The transition and the record ran the same body on the same recent hashes.
  obtain rfl : hashes = hashes' := Except.ok.inj (hh.symm.trans hh')
  obtain rfl : output = result.output := Except.ok.inj (hout.symm.trans hout')
  -- The builder computes the list hash, and the output check equates it with the header.
  obtain ⟨value, hvalue, hhash⟩ := applyBody_accessListHash hout' hf
  have hheader := accessListHash_of_outputChecks hf hchecks
  have heq : value = v.canonical[i + 1].block.header.blockAccessListHash hf :=
    Option.some.inj (hvalue.symm.trans hheader)
  rw [← hkept bal hb, heq] at hhash
  exact hhash

/-- A retained list of an executed canonical block passes the order, uniqueness and size checks. -/
theorem Valid.check_accessList {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal)
    {i : Nat} (hi : i + 1 < v.canonical.length) (hf : .glamsterdam ≤ v.canonical[i + 1].fork)
    {bal : BlockAccessList} (hb : v.canonical[i + 1].accessList = some bal) :
    BlockAccessList.check bal v.canonical[i + 1].block.header.gasLimit = .ok () := by
  obtain ⟨-, result, hbody, -, -, hkept⟩ := hv.follows i hi
  obtain ⟨hashes, -, hout, -⟩ := runBody_eq_ok.mp hbody
  obtain ⟨-, -, -, -, requested, -, -, -, -, -, -, -, hBuilder, hHash, -⟩ :=
    applyBody_eq_ok hout
  have hcheck := (accessListHashOf_eq_ok hHash hf).1
  rw [← hBuilder, ← hkept bal hb] at hcheck
  exact hcheck

/-- A valid executed canonical block with a retained list has both answers, bound to its header. -/
theorem Valid.blockAccessList_answers {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal)
    {p : BlockParam} (hne : p ≠ .tag .pending) {i : Nat} (hi : i + 1 < v.canonical.length)
    (hp : v.resolve p = .ok (some v.canonical[i + 1]))
    (hf : .glamsterdam ≤ v.canonical[i + 1].fork) {bal : BlockAccessList}
    (hb : v.canonical[i + 1].accessList = some bal) :
    ∃ raw, v.blockAccessList p = .ok (blockAccessListJson bal) ∧
      v.rawBlockAccessList p = .ok raw ∧ Codec.decode raw = .ok bal ∧
      keccak256 raw = v.canonical[i + 1].block.header.blockAccessListHash hf := by
  have hhash := hv.accessList_hash hi hf hb
  -- The checked transition already computed these same RLP bytes, so encoding succeeds.
  unfold BlockAccessList.hash at hhash
  obtain ⟨raw, he, hk⟩ := bind_ok_iff.mp hhash
  refine ⟨raw, ?_, ?_, Codec.decode_encode he, Except.ok.inj hk⟩
  · rw [blockAccessList_of_resolve hne hp]
    exact BlockRecord.blockAccessList_eq_ok_iff.mpr ⟨bal, hf, hb, rfl⟩
  · apply ofBlock_eq_ok.mpr
    exact ⟨v.canonical[i + 1], hp,
      BlockRecord.rawBlockAccessList_eq_ok_iff.mpr ⟨bal, hf, hb, he⟩⟩

/-- The dispatched replies recover a checked retained list whose raw bytes hash to its header. -/
theorem Valid.call_blockAccessList_answers {v : ChainView} {checkSeal : Bool}
    (hv : v.Valid checkSeal) {j : Json} {p : BlockParam}
    (hj : blockNumberOrTagOrHash "block" j = .ok p) (hne : p ≠ .tag .pending)
    {i : Nat} (hi : i + 1 < v.canonical.length)
    (hp : v.resolve p = .ok (some v.canonical[i + 1]))
    (hf : .glamsterdam ≤ v.canonical[i + 1].fork) {bal : BlockAccessList}
    (hb : v.canonical[i + 1].accessList = some bal) :
    ∃ raw, v.call "eth_getBlockAccessList" [j] = .ok (blockAccessListJson bal) ∧
      v.call "debug_getRawBlockAccessList" [j] = .ok (dataJson raw.data.toList) ∧
      blockAccessListOfJson (blockAccessListJson bal) = .ok bal ∧
      Codec.decode raw = .ok bal ∧
      BlockAccessList.check bal v.canonical[i + 1].block.header.gasLimit = .ok () ∧
      keccak256 raw = v.canonical[i + 1].block.header.blockAccessListHash hf := by
  obtain ⟨raw, hjson, hraw, hdecode, hhash⟩ := hv.blockAccessList_answers hne hi hp hf hb
  refine ⟨raw, ?_, ?_, blockAccessListOfJson_blockAccessListJson bal, hdecode,
    hv.check_accessList hi hf hb, hhash⟩
  · rw [call_blockAccessList hj]
    exact hjson
  · rw [call_rawBlockAccessList hj, hraw]
    rfl

/-- A raw answer for a checked canonical block hashes to that block's header field. -/
theorem Valid.rawBlockAccessList_hash {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal)
    {p : BlockParam} {i : Nat} (hi : i + 1 < v.canonical.length)
    (hp : v.resolve p = .ok (some v.canonical[i + 1]))
    (hf : .glamsterdam ≤ v.canonical[i + 1].fork) {raw : ByteArray}
    (hr : v.rawBlockAccessList p = .ok raw) :
    keccak256 raw = v.canonical[i + 1].block.header.blockAccessListHash hf := by
  obtain ⟨r, hresolve, hraw⟩ := ofBlock_eq_ok.mp hr
  obtain rfl : v.canonical[i + 1] = r := Option.some.inj (Except.ok.inj (hp.symm.trans hresolve))
  obtain ⟨bal, hb, he, -⟩ := BlockRecord.decode_of_rawBlockAccessList_eq_ok hraw
  have hk := hv.accessList_hash hi hf (BlockRecord.retainedAccessList_eq_ok_iff.mp hb).2
  unfold BlockAccessList.hash at hk
  obtain ⟨encoded, hencoded, hhash⟩ := bind_ok_iff.mp hk
  -- The codec is deterministic, so these are the bytes that the getter returned.
  obtain rfl : raw = encoded := Except.ok.inj (he.symm.trans hencoded)
  exact Except.ok.inj hhash

end ChainView

end EthLib.Execution.Rpc
