module

public import EthLib.Execution.Rpc.Proof
public import EthLib.Execution.Proofs.Rpc.Account
public import EthLib.Execution.Proofs.Rpc.Base
public import EthLib.Execution.Proofs.Rpc.View
public import EthLib.Execution.Proofs.State.AccountProofOfState
import EthLib.Base.Proofs.BigEndian
import ToMathlib.Data.ByteArray
-- The hex digits of a number must unfold for the decision procedure to read them.
import all Init.Data.Repr
-- The fields of an encoded object unfold Lean's `Json.mkObj` and `Json.isNull`.
import all Lean.Data.Json.Basic

/-!
# Proofs: the answer of `eth_getProof`

The answer agrees with the account queries at the same block.

Its balance and nonce are those of the balance and nonce queries.

It echoes the address and the slots, and its words are those of the one-key storage query.

At a canonical block of a valid view, the answer passes the check.

The check is against the state root of the header.

The reader of answers reads back what the writer writes, for a nonce below `2^64`.
-/

public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.State (AccountProof StorageProof State StorageMap EMPTY_ACCOUNT)
open EthLib.Execution.Trie (IsCollision)
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- A number below `16 ^ k` has at most `k` hex digits, when `k` is positive. -/
private theorem toDigits_length_le {k : Nat} (hk : 0 < k) (n : Nat) (hn : n < 16 ^ k) :
    (Nat.toDigits 16 n).length ≤ k := by
  induction n using Nat.strongRecOn generalizing k with
  | _ n ih =>
    rw [Nat.toDigits_eq_ite (by decide : 1 < 16)]
    split
    · simp only [List.length_singleton]; omega
    · rename_i h16
      have hk2 : 2 ≤ k := by
        rcases k with _ | _ | k
        · omega
        · simp at hn; omega
        · omega
      have := ih (n / 16) (by omega) (k := k - 1) (by omega) (by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        calc n < 16 ^ k := hn
          _ = 16 ^ (k - 1) * 16 := by rw [← Nat.pow_succ]; congr 1; omega)
      simp only [List.length_append, List.length_singleton]
      omega

/-- The reader of slots reads back the key that the writer writes as a quantity. -/
theorem bytesMax32_quantityJson (what : String) (key : Bytes32) :
    bytesMax32 what (quantityJson (bytesToNat key.toList)) = .ok key := by
  have hv := natToBytes_bytesToNat key.toList
  simp only [Vector.length_toList] at hv
  have hlt : bytesToNat key.toList < 16 ^ 64 := by
    have := bytesToNat_natToBytes 32 (bytesToNat key.toList)
    rw [hv] at this
    have h2 := Nat.mod_lt (bytesToNat key.toList) (by decide : 0 < 256 ^ 32)
    rw [← this] at h2
    exact lt_of_lt_of_eq h2 (by decide)
  obtain ⟨hall, hval, -⟩ := toDigits_hex (bytesToNat key.toList)
  simp only [digitValue] at hval
  have hascii : ∀ c ∈ Nat.toDigits 16 (bytesToNat key.toList), c.val ≤ 0x7F := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := hall c hc
    exact (hexValue_digitChar d hd).2
  have hlen := toDigits_length_le (by decide : 0 < 64) _ hlt
  unfold bytesMax32 quantityJson
  rw [hexDigits_ascii _ _ hascii]
  simp only [bind, Except.bind]
  have hsize : (List.map (fun c => c.val.toUInt8)
      (Nat.toDigits 16 (bytesToNat key.toList))).toByteArray.size ≤ 64 := by simpa using hlen
  rw [ite_eq_right (by omega), forIn_eq_forIn_toList]
  have hdata : (List.map (fun c => c.val.toUInt8)
      (Nat.toDigits 16 (bytesToNat key.toList))).toByteArray.data.toList =
      List.map (fun c => c.val.toUInt8) (Nat.toDigits 16 (bytesToNat key.toList)) := by simp
  rw [hdata, forIn_hex, hval]
  · simp only [pure, Except.pure, Except.ok.injEq]
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_ofFn]
    have h := congrArg (·[i]?) hv
    rw [List.getElem?_eq_getElem (by rw [natToBytes_length]; exact hi), getElem_natToBytes hi,
      List.getElem?_eq_getElem (by simpa using hi), Option.some.injEq,
      Vector.getElem_toList] at h
    rw [← h]
  · intro c hc s
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
    obtain ⟨d, hd, rfl⟩ := hall c' hc'
    rw [(hexValue_digitChar d hd).1]
    rfl

/-- The fields of an object of distinct names and values other than `null` find each pair. -/
private theorem lookup_fields_mkObj {pairs : List (String × Lean.Json)} (what : String)
    (distinct : pairs.Pairwise fun a b => a.1 ≠ b.1) (hnn : ∀ p ∈ pairs, p.2.isNull = false) :
    ∃ fs, fields what (Lean.Json.mkObj pairs) = .ok fs ∧
      ∀ k v, (k, v) ∈ pairs → fs.lookup k = some v := by
  obtain ⟨fs, hfs, hperm⟩ := fields_mkObj what distinct hnn
  have hd : fs.Pairwise fun a b => a.1 ≠ b.1 :=
    (hperm.pairwise_iff fun h e => h e.symm).mpr distinct
  exact ⟨fs, hfs, fun k v h => lookup_of_mem hd (hperm.mem_iff.mpr h)⟩

/-- The reader of proof nodes reads back the nodes that the writer writes. -/
private theorem proofNodes_proofNodesJson (what : String) (nodes : List ByteArray) :
    proofNodes what (proofNodesJson nodes) = .ok nodes := by
  unfold proofNodes proofNodesJson
  rw [array_listJson]
  induction nodes with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.mapM_cons]
    have h : bytes what (dataJson n.toList) = .ok n := by
      unfold dataJson
      rw [bytes_hexString]
      congr 1
      exact ByteArray.ext (by simp [ByteArray.toList_eq_toList_data])
    rw [h, ih]
    rfl

/-- The reader of one slot of an answer reads back what the writer writes. -/
private theorem storageProofOfJson_storageProofJson (s : StorageProof) :
    storageProofOfJson (storageProofJson s) = .ok s := by
  obtain ⟨fs, hfs, hl⟩ := lookup_fields_mkObj "slot" (pairs := [
    ("key", quantityJson (bytesToNat s.key.toList)), ("value", quantityJson s.value.toNat),
    ("proof", proofNodesJson s.proof)]) (by simp)
    (by simp [Lean.Json.isNull, quantityJson, proofNodesJson, listJson])
  have f1 : field "slot" fs "key" = .ok (quantityJson (bytesToNat s.key.toList)) :=
    field_eq_ok_iff.mpr (hl "key" _ (by simp))
  have f2 : field "slot" fs "value" = .ok (quantityJson s.value.toNat) :=
    field_eq_ok_iff.mpr (hl "value" _ (by simp))
  have f3 : field "slot" fs "proof" = .ok (proofNodesJson s.proof) :=
    field_eq_ok_iff.mpr (hl "proof" _ (by simp))
  unfold storageProofOfJson
  rw [storageProofJson, hfs]
  simp only [bind, Except.bind, f1, f2, f3, bytesMax32_quantityJson,
    quantity_toDigits _ (bits := 256) (by simpa using s.value.isLt), proofNodes_proofNodesJson]
  simp [pure, Except.pure]

/-- The reader of the slots of an answer reads back the slots that the writer writes. -/
private theorem array_storageProofOfJson (what : String) (l : List StorageProof) :
    array what storageProofOfJson (listJson storageProofJson l) = .ok l := by
  rw [array_listJson]
  induction l with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.mapM_cons]
    rw [ih, storageProofOfJson_storageProofJson]
    rfl

/-- The reader of answers reads back what the writer writes, for a nonce below `2^64`. -/
theorem accountProofOfJson_accountProofJson {p : AccountProof} (hnonce : p.nonce < 2 ^ 64) :
    accountProofOfJson (accountProofJson p) = .ok p := by
  obtain ⟨fs, hfs, hl⟩ := lookup_fields_mkObj "answer" (pairs := [
    ("address", dataJson p.address.toList), ("accountProof", proofNodesJson p.accountProof),
    ("balance", quantityJson p.balance.toNat), ("codeHash", dataJson p.codeHash.toList),
    ("nonce", quantityJson p.nonce), ("storageHash", dataJson p.storageHash.toList),
    ("storageProof", listJson storageProofJson p.storageProof)]) (by simp)
    (by simp [Lean.Json.isNull, quantityJson, proofNodesJson, listJson, dataJson])
  have f1 : field "answer" fs "address" = .ok (dataJson p.address.toList) :=
    field_eq_ok_iff.mpr (hl "address" _ (by simp))
  have f2 : field "answer" fs "accountProof" = .ok (proofNodesJson p.accountProof) :=
    field_eq_ok_iff.mpr (hl "accountProof" _ (by simp))
  have f3 : field "answer" fs "balance" = .ok (quantityJson p.balance.toNat) :=
    field_eq_ok_iff.mpr (hl "balance" _ (by simp))
  have f4 : field "answer" fs "codeHash" = .ok (dataJson p.codeHash.toList) :=
    field_eq_ok_iff.mpr (hl "codeHash" _ (by simp))
  have f5 : field "answer" fs "nonce" = .ok (quantityJson p.nonce) :=
    field_eq_ok_iff.mpr (hl "nonce" _ (by simp))
  have f6 : field "answer" fs "storageHash" = .ok (dataJson p.storageHash.toList) :=
    field_eq_ok_iff.mpr (hl "storageHash" _ (by simp))
  have f7 : field "answer" fs "storageProof" = .ok (listJson storageProofJson p.storageProof) :=
    field_eq_ok_iff.mpr (hl "storageProof" _ (by simp))
  unfold accountProofOfJson
  rw [accountProofJson, hfs]
  simp only [bind, Except.bind, f1, f2, f3, f4, f5, f6, f7, proofNodes_proofNodesJson,
    array_storageProofOfJson, quantity_toDigits _ hnonce,
    quantity_toDigits _ (bits := 256) (by simpa using p.balance.isLt)]
  unfold dataJson
  simp only [fixed_hexString, address]
  simp [pure, Except.pure]

/-- The word of the storage map that the state gives is the word that the proof reads. -/
private theorem getD_storage (state : State) (a : Address) (key : Bytes32) :
    (state.storage.getD a ∅).getD key 0 = state.getStorage a key := by
  unfold State.getStorage StorageMap.slot
  rw [Std.ExtTreeMap.getD_eq_getD_getElem?, Std.ExtTreeMap.getD_eq_getD_getElem?]
  cases state.storage[a]? <;> simp

/-- The fields of a built answer: the address, the account fields and the slots in order. -/
private theorem ofState_spec {hash : ByteArray → Hash32} {state : State} {a : Address}
    {keys : List Bytes32} {answer : AccountProof}
    (hp : AccountProof.ofState hash state a keys = .ok answer) :
    answer.address = a ∧ answer.nonce = (state.accounts[a]?.getD EMPTY_ACCOUNT).nonce ∧
      answer.balance = (state.accounts[a]?.getD EMPTY_ACCOUNT).balance ∧
      answer.storageProof.map (·.key) = keys ∧
      answer.storageProof.map (·.value) = keys.map fun key => state.getStorage a key := by
  unfold AccountProof.ofState at hp
  obtain ⟨_, _, hp⟩ := bind_ok_iff.mp hp
  obtain ⟨_, _, hp⟩ := bind_ok_iff.mp hp
  try dsimp only at hp
  obtain ⟨_, _, hp⟩ := bind_ok_iff.mp hp
  try dsimp only at hp
  rcases hs : state.accounts[a]? with _ | acc <;> rw [hs] at hp <;> dsimp only at hp
  all_goals
    obtain ⟨_, _, hp⟩ := bind_ok_iff.mp hp
    obtain ⟨sp, hsp, hp⟩ := bind_ok_iff.mp hp
    obtain rfl := Except.ok.inj hp
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · rw [map_of_mapM_ok (q := id) ?_ hsp, List.map_id]
      intro x y hy
      obtain ⟨_, _, hy⟩ := bind_ok_iff.mp hy
      obtain rfl := Except.ok.inj hy
      rfl
    · rw [map_of_mapM_ok (q := fun key => (state.storage.getD a ∅).getD key 0) ?_ hsp]
      · exact List.map_congr_left fun key _ => getD_storage state a key
      intro x y hy
      obtain ⟨_, _, hy⟩ := bind_ok_iff.mp hy
      obtain rfl := Except.ok.inj hy
      rfl

namespace ChainView

/-- When the proof query answers, a block resolves and the answer is that of the builder. -/
private theorem accountProof_eq_ok {v : ChainView} {a : Address} {keys : List Bytes32}
    {p : BlockParam} {answer : AccountProof} (h : v.accountProof a keys p = .ok answer) :
    ∃ r, v.resolve p = .ok (some r) ∧
      AccountProof.ofState keccak256 r.state a keys = .ok answer := by
  obtain ⟨r, hr, hf⟩ := ofBlock_eq_ok.mp h
  refine ⟨r, hr, ?_⟩
  cases hx : AccountProof.ofState keccak256 r.state a keys with
  | error e => rw [hx] at hf; cases hf
  | ok x => rw [hx] at hf; exact congrArg Except.ok (Except.ok.inj hf)

/-- When the proof query answers, it agrees with the account queries of the same block.

Its balance and nonce are the answers of the balance and nonce queries.

It echoes the address and the slots, in order.

Its words are the answers of the one-key storage query, in order. -/
theorem accountProof_agree {v : ChainView} {a : Address} {keys : List Bytes32} {p : BlockParam}
    {answer : AccountProof} (h : v.accountProof a keys p = .ok answer) :
    v.balance a p = .ok answer.balance ∧ v.nonce a p = .ok answer.nonce ∧
      answer.address = a ∧ answer.storageProof.map (·.key) = keys ∧
      keys.mapM (fun key => v.storageAt a key p) = .ok (answer.storageProof.map (·.value)) := by
  obtain ⟨r, hr, hp⟩ := accountProof_eq_ok h
  obtain ⟨h1, h2, h3, h4, h5⟩ := ofState_spec hp
  refine ⟨ofBlock_eq_ok.mpr ⟨r, hr, ?_⟩, ofBlock_eq_ok.mpr ⟨r, hr, ?_⟩, h1, h4, ?_⟩
  · rw [h3]
    simp [BlockRecord.account, State.getAccountOptional]
  · rw [h2]
    simp [BlockRecord.account, State.getAccountOptional]
  · rw [h5]
    exact mapM_eq_ok_map (g := fun key => r.state.getStorage a key) fun key _ =>
      ofBlock_eq_ok.mpr ⟨r, hr, rfl⟩

/-- Completeness: at a canonical block of a valid view, the answer passes the check.

The check is against the state root of the header of the block.

It reports the account present exactly when the state after the block has it.

The proof assumes that an address with no account has the word zero at each slot asked for.

When the answer does not pass the check, a search finds two keys with one hash. -/
theorem Valid.verify_accountProof {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal)
    {p : BlockParam} {r : BlockRecord} (hres : v.resolve p = .ok (some r)) (hr : r ∈ v.canonical)
    {a : Address} {keys : List Bytes32} {answer : AccountProof}
    (h : v.accountProof a keys p = .ok answer)
    (hstorage : r.state.accounts[a]? = none → ∀ key ∈ keys, r.storage a key = 0) :
    answer.verify keccak256 r.block.header.stateRoot =
        .ok (AccountProof.outcomeOfState r.state a keys) ∨
      ∃ pair, AccountProof.findAnswerCollision keccak256 r.state a keys = some pair ∧
        IsCollision keccak256 pair := by
  obtain ⟨r', hr', hp⟩ := accountProof_eq_ok h
  have hrr : r' = r := Option.some.inj (Except.ok.inj (hr'.symm.trans hres))
  rw [hrr] at hp
  exact AccountProof.verify_ofState (hv.stateRoot_eq hr) hp fun hnone key hk =>
    (getD_storage r.state a key).trans (hstorage hnone key hk)

end ChainView

end EthLib.Execution.Rpc
