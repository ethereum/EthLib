module

public import EthLib.Execution.Rpc.Transaction
public import EthLib.Execution.Proofs.Rpc.Base
public import EthLib.Execution.Rpc.TransactionInfo
public import EthLib.Base.Except
-- The fields of an encoded object unfold Lean's `Json.mkObj` and `Json.isNull`.
import all Lean.Data.Json.Basic

/-!
# Proofs: the JSON form of a signed transaction

The reader of transactions reads back what the writer writes, for every kind of transaction.

A typed transaction holds its parity as a 256-bit number, while the schemas type it as a byte.

So the round trip needs the parity of a typed transaction to be below 256.

A transaction whose signature names a sender has a parity of 0 or 1, so it meets that bound.

The object of a transaction of a block, which the methods return, reads back as the transaction.
-/

public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Transactions

/-- The parity of a typed transaction is below 256, so that it fits the byte of its JSON form.

A legacy transaction has no parity, and always satisfies it. -/
def ParityIsByte : Transaction → Prop
  | .legacy _ => True
  | .accessList tx => tx.yParity.toNat < 256
  | .feeMarket tx => tx.yParity.toNat < 256
  | .blob tx => tx.yParity.toNat < 256
  | .setCode tx => tx.yParity.toNat < 256

/-- A computation that has succeeded passes its value on. -/
private theorem ok_bind {α β : Type} (a : α) (f : α → Read β) :
    (Except.ok a >>= f : Read β) = f a := rfl

/-- The reader of bytes reads back the quantity of any number below 256. -/
private theorem byte_quantityJson (what : String) {n : Nat} (h : n < 256) :
    byte what (quantityJson n) = .ok n.toUInt8 := by
  have := byte_byteJson what n.toUInt8
  simpa [byteJson, Nat.mod_eq_of_lt h] using this

/-- The reader of byte strings reads back a byte string that holds its bytes as data. -/
private theorem bytes_dataJson (what : String) (b : ByteArray) :
    bytes what (dataJson b.data.toList) = .ok b := by
  rw [dataJson, bytes_hexString]
  congr 1
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

/-- The reader of a list reads back a list whose items each read back from their writer. -/
private theorem array_of_items {α : Type} (what : String) (f : Lean.Json → Read α)
    (g : α → Lean.Json) (items : List α) (h : ∀ x ∈ items, f (g x) = .ok x) :
    array what f (listJson g items) = .ok items := by
  rw [array_listJson]
  induction items with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    rfl

/-- The JSON of a quantity is not `null`. -/
private theorem isNull_quantityJson (n : Nat) : (quantityJson n).isNull = false := isNull_str _

/-- The JSON of data is not `null`. -/
private theorem isNull_dataJson (l : List UInt8) : (dataJson l).isNull = false := isNull_str _

/-- The JSON of a list is not `null`. -/
private theorem isNull_listJson {α : Type} (g : α → Lean.Json) (l : List α) :
    (listJson g l).isNull = false := isNull_arr _

/-- The fields of a transaction have distinct names. -/
private theorem names_distinct (gp : Nat) (tx : Transaction) :
    (transactionFields gp tx).Pairwise fun a b => a.1 ≠ b.1 := by
  cases tx with
  | legacy tx =>
    by_cases h : 35 ≤ tx.v.toNat <;> simp [transactionFields, h]
  | accessList => simp [transactionFields, typedFields]
  | feeMarket => simp [transactionFields, typedFields]
  | blob => simp [transactionFields, typedFields]
  | setCode => simp [transactionFields, typedFields]

/-- The names that the fields of a transaction can have. -/
private def txNames : List String :=
  ["type", "nonce", "gas", "value", "input", "to", "gasPrice", "v", "r", "s", "chainId",
    "accessList", "yParity", "maxPriorityFeePerGas", "maxFeePerGas", "maxFeePerBlobGas",
    "blobVersionedHashes", "authorizationList"]

/-- Each field of a transaction has one of the names of `txNames`. -/
private theorem names_subset (gp : Nat) (tx : Transaction) :
    ∀ p ∈ transactionFields gp tx, p.1 ∈ txNames := by
  intro p hp
  cases tx with
  | legacy tx =>
    by_cases h : 35 ≤ tx.v.toNat <;> simp [transactionFields, h] at hp <;>
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [txNames]
  | accessList tx =>
    simp [transactionFields, typedFields] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [txNames]
  | feeMarket tx =>
    simp [transactionFields, typedFields] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> simp [txNames]
  | blob tx =>
    simp [transactionFields, typedFields] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> simp [txNames]
  | setCode tx =>
    simp [transactionFields, typedFields] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> simp [txNames]

/-- The object of a transaction, after other fields, reads each of its fields by its name.

A field that is `null` reads as absent. -/
private theorem fields_transaction (extra : List (String × Lean.Json)) (gp : Nat)
    (tx : Transaction) (hx : extra.Pairwise fun a b => a.1 ≠ b.1)
    (hdis : ∀ p ∈ extra, p.1 ∉ txNames) :
    ∃ fs, fields "transaction" (Lean.Json.mkObj (extra ++ transactionFields gp tx)) = .ok fs ∧
      (∀ k ∈ txNames, fs.lookup k = ((transactionFields gp tx).lookup k).filter
        fun v => !v.isNull) ∧
      ∀ k v, (transactionFields gp tx).lookup k = some v → v.isNull = false →
        field "transaction" fs k = .ok v := by
  have hd : (extra ++ transactionFields gp tx).Pairwise fun a b => a.1 ≠ b.1 := by
    rw [List.pairwise_append]
    refine ⟨hx, names_distinct gp tx, fun a ha b hb h => ?_⟩
    exact hdis a ha (h ▸ names_subset gp tx b hb)
  obtain ⟨fs, hfs, hp⟩ := fields_mkObj_filter "transaction" hd
  have hl := lookup_of_perm_filter hp hd
  -- Reading a name of a transaction in the whole object is reading it in the transaction.
  have hk : ∀ k ∈ txNames, (extra ++ transactionFields gp tx).lookup k =
      (transactionFields gp tx).lookup k := by
    intro k hk
    cases hv : (transactionFields gp tx).lookup k with
    | none =>
      rw [List.lookup_eq_none_iff] at hv ⊢
      intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact bne_iff_ne.mpr fun e => hdis q hq (by rw [← e]; exact hk)
      · exact hv q hq
    | some v =>
      obtain ⟨l₁, l₂, e, -⟩ := List.lookup_eq_some_iff.mp hv
      exact lookup_of_mem hd (List.mem_append_right _ (by rw [e]; simp))
  have hl' : ∀ k ∈ txNames, fs.lookup k = ((transactionFields gp tx).lookup k).filter
      fun v => !v.isNull := fun k hkn => by rw [hl k, hk k hkn]
  refine ⟨fs, hfs, hl', fun k v hv hn => field_eq_ok_iff.mpr ?_⟩
  have hkn : k ∈ txNames := by
    obtain ⟨l₁, l₂, e, -⟩ := List.lookup_eq_some_iff.mp hv
    exact names_subset gp tx (k, v) (by rw [e]; simp)
  rw [hl' k hkn, hv]
  simp [hn]

/-- The reader of the recipient reads back a recipient that its writer writes. -/
private theorem recipient_of {fs : List (String × Lean.Json)} (o : Option Address)
    (h : fs.lookup "to" = (some (optionJson (fun (a : Address) => dataJson a.toList) o)).filter
      fun v => !v.isNull) :
    recipient fs = .ok o := by
  unfold recipient
  cases o with
  | none => rw [h]; rfl
  | some a =>
    rw [h]
    simp only [optionJson, Option.filter_some, isNull_dataJson, Bool.not_false, ite_true]
    simp [address_dataJson, Functor.map, Except.map]

/-- A parity below 256 goes through its byte and comes back. -/
private theorem yParity_byte {y : U256} (h : y.toNat < 256) :
    BitVec.ofNat 256 y.toNat.toUInt8.toNat = y := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt h]

/-- The reader of access list entries reads back the entry that its writer writes. -/
theorem access_accessJson (a : Access) : access (accessJson a) = .ok a := by
  have hd : [("address", dataJson a.account.toList),
      ("storageKeys", listJson (fun (k : Bytes32) => dataJson k.toList) a.slots)].Pairwise
        fun x y => x.1 ≠ y.1 := by simp
  obtain ⟨fs, hfs, hp⟩ := fields_mkObj "access list entry" hd (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact isNull_dataJson _
    · exact isNull_listJson _ _)
  have hex : hasExactly fs ["address", "storageKeys"] = true := hasExactly_of_perm hp
  have r1 := field_of_perm (what := "access list entry") hp hd
    (k := "address") (v := dataJson a.account.toList) (by simp)
  have r2 := field_of_perm (what := "access list entry") hp hd
    (k := "storageKeys") (v := listJson (fun (k : Bytes32) => dataJson k.toList) a.slots)
    (by simp)
  unfold access accessJson
  simp only [hfs, ok_bind]
  rw [ite_eq_left hex]
  simp only [r1, r2, ok_bind, address_dataJson, array_of_items _ (bytes32 "storage key")
    (fun (k : Bytes32) => dataJson k.toList) _
    (fun k _ => fixed_dataJson "storage key" k false)]
  rfl

/-- The reader of authorizations reads back the authorization that its writer writes. -/
theorem authorization_authorizationJson (a : Authorization) :
    authorization (authorizationJson a) = .ok a := by
  have hd : [("chainId", quantityJson a.chainId.toNat), ("nonce", quantityJson a.nonce.toNat),
      ("address", dataJson a.address.toList), ("yParity", byteJson a.yParity),
      ("r", quantityJson a.r.toNat), ("s", quantityJson a.s.toNat)].Pairwise
        fun x y => x.1 ≠ y.1 := by simp
  obtain ⟨fs, hfs, hp⟩ := fields_mkObj "authorization" hd (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact isNull_str _)
  have r1 := field_of_perm (what := "authorization") hp hd
    (k := "chainId") (v := quantityJson a.chainId.toNat) (by simp)
  have r2 := field_of_perm (what := "authorization") hp hd
    (k := "nonce") (v := quantityJson a.nonce.toNat) (by simp)
  have r3 := field_of_perm (what := "authorization") hp hd
    (k := "address") (v := dataJson a.address.toList) (by simp)
  have r4 := field_of_perm (what := "authorization") hp hd
    (k := "yParity") (v := byteJson a.yParity) (by simp)
  have r5 := field_of_perm (what := "authorization") hp hd
    (k := "r") (v := quantityJson a.r.toNat) (by simp)
  have r6 := field_of_perm (what := "authorization") hp hd
    (k := "s") (v := quantityJson a.s.toNat) (by simp)
  unfold authorization authorizationJson
  simp only [hfs, ok_bind, r1, r2, r3, r4, r5, r6, uint256_quantityJson, uint64_toDigits,
    address_dataJson, byte_byteJson]
  rfl

/-- The reader of transactions reads a transaction from an object with other fields as well.

The other fields must have distinct names that no transaction field has.

The gas price of the object must be that of the transaction when it is legacy or of type 1. -/
private theorem transactionOfJson_extra (extra : List (String × Lean.Json)) (g : Nat)
    (tx : Transaction) (hx : extra.Pairwise fun a b => a.1 ≠ b.1)
    (hdis : ∀ p ∈ extra, p.1 ∉ txNames)
    (hg0 : ∀ t, tx = .legacy t → g = t.gasPrice.toNat)
    (hg1 : ∀ t, tx = .accessList t → g = t.gasPrice.toNat) (h : ParityIsByte tx) :
    transactionOfJson (Lean.Json.mkObj (extra ++ transactionFields g tx)) = .ok tx := by
  have ty0 : UInt8.toNat 0 = 0 := rfl
  have ty1 : UInt8.toNat 1 = 1 := rfl
  have ty2 : UInt8.toNat 2 = 2 := rfl
  have ty3 : UInt8.toNat 3 = 3 := rfl
  have ty4 : UInt8.toNat 4 = 4 := rfl
  cases tx with
  | legacy t =>
    obtain rfl := hg0 t rfl
    obtain ⟨fs, hfs, hl, rd⟩ := fields_transaction extra t.gasPrice.toNat (.legacy t) hx hdis
    have rto := recipient_of (fs := fs) t.to (by rw [hl "to" (by simp [txNames])]; rfl)
    have r1 := rd "type" _ rfl (isNull_quantityJson _)
    have r2 := rd "nonce" _ rfl (isNull_quantityJson _)
    have r3 := rd "gas" _ rfl (isNull_quantityJson _)
    have r4 := rd "value" _ rfl (isNull_quantityJson _)
    have r5 := rd "input" _ rfl (isNull_dataJson _)
    have r6 := rd "r" _ rfl (isNull_quantityJson _)
    have r7 := rd "s" _ rfl (isNull_quantityJson _)
    have r8 := rd "gasPrice" _ rfl (isNull_quantityJson _)
    have r9 := rd "v" _ rfl (isNull_quantityJson _)
    unfold transactionOfJson
    simp only [hfs, ok_bind, r1, r2, r3, r4, r5, r6, r7, r8, r9, rto, byteJson, u256Json,
      uint_quantityJson, uint256_quantityJson, bytes_dataJson,
      ty0, Nat.reduceLT, ↓reduceIte]
    rfl
  | accessList t =>
    obtain rfl := hg1 t rfl
    obtain ⟨fs, hfs, hl, rd⟩ := fields_transaction extra t.gasPrice.toNat (.accessList t) hx hdis
    have hy : t.yParity.toNat < 256 := h
    have rto := recipient_of (fs := fs) t.to (by rw [hl "to" (by simp [txNames])]; rfl)
    have r1 := rd "type" _ rfl (isNull_quantityJson _)
    have r2 := rd "nonce" _ rfl (isNull_quantityJson _)
    have r3 := rd "gas" _ rfl (isNull_quantityJson _)
    have r4 := rd "value" _ rfl (isNull_quantityJson _)
    have r5 := rd "input" _ rfl (isNull_dataJson _)
    have r6 := rd "r" _ rfl (isNull_quantityJson _)
    have r7 := rd "s" _ rfl (isNull_quantityJson _)
    have r8 := rd "chainId" _ rfl (isNull_quantityJson _)
    have r9 := rd "accessList" _ rfl (isNull_listJson _ _)
    have r10 := rd "yParity" _ rfl (isNull_quantityJson _)
    have r11 := rd "gasPrice" _ rfl (isNull_quantityJson _)
    unfold transactionOfJson
    simp only [hfs, ok_bind, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11,  rto, byteJson,
      u256Json, accessListJson, uint_quantityJson, uint256_quantityJson, uint64_toDigits,
      bytes_dataJson, byte_quantityJson _ hy, yParity_byte hy,
      array_of_items _ access accessJson _ (fun a _ => access_accessJson a),
      ty1, Nat.reduceLT, ↓reduceIte, Nat.reduceEqDiff]
    rfl
  | feeMarket t =>
    obtain ⟨fs, hfs, hl, rd⟩ := fields_transaction extra g (.feeMarket t) hx hdis
    have hy : t.yParity.toNat < 256 := h
    have rto := recipient_of (fs := fs) t.to (by rw [hl "to" (by simp [txNames])]; rfl)
    have r1 := rd "type" _ rfl (isNull_quantityJson _)
    have r2 := rd "nonce" _ rfl (isNull_quantityJson _)
    have r3 := rd "gas" _ rfl (isNull_quantityJson _)
    have r4 := rd "value" _ rfl (isNull_quantityJson _)
    have r5 := rd "input" _ rfl (isNull_dataJson _)
    have r6 := rd "r" _ rfl (isNull_quantityJson _)
    have r7 := rd "s" _ rfl (isNull_quantityJson _)
    have r8 := rd "chainId" _ rfl (isNull_quantityJson _)
    have r9 := rd "accessList" _ rfl (isNull_listJson _ _)
    have r10 := rd "yParity" _ rfl (isNull_quantityJson _)
    have r11 := rd "gasPrice" _ rfl (isNull_quantityJson _)
    have r12 := rd "maxPriorityFeePerGas" _ rfl (isNull_quantityJson _)
    have r13 := rd "maxFeePerGas" _ rfl (isNull_quantityJson _)
    unfold transactionOfJson
    simp only [hfs, ok_bind, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, rto, byteJson,
      u256Json, accessListJson, uint_quantityJson, uint256_quantityJson, uint64_toDigits,
      bytes_dataJson, byte_quantityJson _ hy, yParity_byte hy,
      array_of_items _ access accessJson _ (fun a _ => access_accessJson a),
      ty2, Nat.reduceLT, ↓reduceIte, Nat.reduceEqDiff]
    rfl
  | blob t =>
    obtain ⟨fs, hfs, hl, rd⟩ := fields_transaction extra g (.blob t) hx hdis
    have hy : t.yParity.toNat < 256 := h
    have rto := rd "to" _ rfl (isNull_dataJson _)
    have r1 := rd "type" _ rfl (isNull_quantityJson _)
    have r2 := rd "nonce" _ rfl (isNull_quantityJson _)
    have r3 := rd "gas" _ rfl (isNull_quantityJson _)
    have r4 := rd "value" _ rfl (isNull_quantityJson _)
    have r5 := rd "input" _ rfl (isNull_dataJson _)
    have r6 := rd "r" _ rfl (isNull_quantityJson _)
    have r7 := rd "s" _ rfl (isNull_quantityJson _)
    have r8 := rd "chainId" _ rfl (isNull_quantityJson _)
    have r9 := rd "accessList" _ rfl (isNull_listJson _ _)
    have r10 := rd "yParity" _ rfl (isNull_quantityJson _)
    have r11 := rd "gasPrice" _ rfl (isNull_quantityJson _)
    have r12 := rd "maxPriorityFeePerGas" _ rfl (isNull_quantityJson _)
    have r13 := rd "maxFeePerGas" _ rfl (isNull_quantityJson _)
    have r14 := rd "maxFeePerBlobGas" _ rfl (isNull_quantityJson _)
    have r15 := rd "blobVersionedHashes" _ rfl (isNull_listJson _ _)
    unfold transactionOfJson
    simp only [hfs, ok_bind, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, rto,
      byteJson,
      u256Json, accessListJson, uint_quantityJson, uint256_quantityJson, uint64_toDigits,
      bytes_dataJson, byte_quantityJson _ hy, yParity_byte hy,
      array_of_items _ (bytes32 "blob hash") (fun (k : Bytes32) => dataJson k.toList) _
      (fun k _ => fixed_dataJson "blob hash" k false),
      address_dataJson,
      array_of_items _ access accessJson _ (fun a _ => access_accessJson a),
      ty3, Nat.reduceLT, ↓reduceIte, Nat.reduceEqDiff]
    rfl
  | setCode t =>
    obtain ⟨fs, hfs, hl, rd⟩ := fields_transaction extra g (.setCode t) hx hdis
    have hy : t.yParity.toNat < 256 := h
    have rto := rd "to" _ rfl (isNull_dataJson _)
    have r1 := rd "type" _ rfl (isNull_quantityJson _)
    have r2 := rd "nonce" _ rfl (isNull_quantityJson _)
    have r3 := rd "gas" _ rfl (isNull_quantityJson _)
    have r4 := rd "value" _ rfl (isNull_quantityJson _)
    have r5 := rd "input" _ rfl (isNull_dataJson _)
    have r6 := rd "r" _ rfl (isNull_quantityJson _)
    have r7 := rd "s" _ rfl (isNull_quantityJson _)
    have r8 := rd "chainId" _ rfl (isNull_quantityJson _)
    have r9 := rd "accessList" _ rfl (isNull_listJson _ _)
    have r10 := rd "yParity" _ rfl (isNull_quantityJson _)
    have r11 := rd "gasPrice" _ rfl (isNull_quantityJson _)
    have r12 := rd "maxPriorityFeePerGas" _ rfl (isNull_quantityJson _)
    have r13 := rd "maxFeePerGas" _ rfl (isNull_quantityJson _)
    have r14 := rd "authorizationList" _ rfl (isNull_listJson _ _)
    unfold transactionOfJson
    simp only [hfs, ok_bind, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, rto,
      byteJson,
      u256Json, accessListJson, uint_quantityJson, uint256_quantityJson, uint64_toDigits,
      bytes_dataJson, byte_quantityJson _ hy, yParity_byte hy,
      array_of_items _ authorization authorizationJson _
      (fun a _ => authorization_authorizationJson a), address_dataJson,
      array_of_items _ access accessJson _ (fun a _ => access_accessJson a),
      ty4, Nat.reduceLT, ↓reduceIte, Nat.reduceEqDiff]
    rfl

/-- The reader of transactions reads back the transaction that its writer writes.

A typed transaction needs a parity below 256. -/
theorem transactionOfJson_transactionJson (tx : Transaction) (h : ParityIsByte tx) :
    transactionOfJson (transactionJson tx) = .ok tx := by
  have := transactionOfJson_extra [] tx.maxFeePerGas tx (by simp) (by simp)
    (by rintro t rfl; rfl) (by rintro t rfl; rfl) h
  simpa only [transactionJson, List.nil_append] using this

/-- A parity that the recovery accepts is below 256. -/
private theorem parityRecovery_lt {y : U256} {i : Fin 2} (h : parityRecovery y = .ok i) :
    y.toNat < 256 := by
  unfold parityRecovery at h
  by_cases h0 : y.toNat = 0
  · omega
  · by_cases h1 : y.toNat = 1
    · omega
    · rw [ite_eq_right h0, ite_eq_right h1] at h
      cases h

/-- A sender that the signature names comes with the signing input of the transaction. -/
private theorem signingInput_of_recoverSender {fork : Fork} {tx : Transaction} {sender : Address}
    (h : recoverSender fork tx = .ok sender) : ∃ a, signingInput fork tx = .ok a := by
  unfold recoverSender at h
  split at h
  · obtain ⟨a, ha, -⟩ := bind_ok_iff.mp h
    exact ⟨a, ha⟩
  · cases h

/-- A transaction whose signature names a sender has a parity of 0 or 1, so below 256. -/
theorem parityIsByte_of_recoverSender {fork : Fork} {tx : Transaction} {sender : Address}
    (h : recoverSender fork tx = .ok sender) : ParityIsByte tx := by
  obtain ⟨a, ha⟩ := signingInput_of_recoverSender h
  cases tx with
  | legacy t => trivial
  | accessList t =>
    obtain ⟨_, -, ha⟩ := bind_ok_iff.mp ha
    obtain ⟨i, hi, -⟩ := bind_ok_iff.mp ha
    exact parityRecovery_lt hi
  | feeMarket t =>
    obtain ⟨_, -, ha⟩ := bind_ok_iff.mp ha
    obtain ⟨i, hi, -⟩ := bind_ok_iff.mp ha
    exact parityRecovery_lt hi
  | blob t =>
    obtain ⟨_, -, ha⟩ := bind_ok_iff.mp ha
    obtain ⟨i, hi, -⟩ := bind_ok_iff.mp ha
    exact parityRecovery_lt hi
  | setCode t =>
    obtain ⟨_, -, ha⟩ := bind_ok_iff.mp ha
    obtain ⟨i, hi, -⟩ := bind_ok_iff.mp ha
    exact parityRecovery_lt hi

/-- A step whose error is mapped succeeds only when the step succeeds with that value. -/
private theorem ok_of_mapError {ε ε' α : Type} {f : ε → ε'} {x : Except ε α} {a : α}
    (h : x.mapError f = .ok a) : x = .ok a := by
  cases x <;> simp_all [Except.mapError]

/-- The reader of transactions reads the transaction back from the object that a method returns. -/
theorem transactionOfJson_transactionInfoJson {r : BlockRecord} {index : Nat} {tx : Transaction}
    {info : TransactionInfo} (h : r.transactionInfo index tx = .ok info) :
    transactionOfJson (transactionInfoJson info) = .ok tx := by
  unfold BlockRecord.transactionInfo at h
  obtain ⟨sender, hs, h⟩ := bind_ok_iff.mp h
  obtain ⟨hash, -, h⟩ := bind_ok_iff.mp h
  have hinfo := Except.ok.inj h
  subst hinfo
  have hpar := parityIsByte_of_recoverSender (ok_of_mapError hs)
  exact transactionOfJson_extra _ _ tx (by simp) (by simp [txNames])
    (by rintro t rfl; rfl) (by rintro t rfl; rfl) hpar

end EthLib.Execution.Rpc
