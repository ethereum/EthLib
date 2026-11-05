module

public import EthLib.Base.Proofs.Fork
public import EthLib.Execution.Transactions.Envelope
public import EthLib.Serialization.Proofs.Rlp.Codec

/-!
# Proofs: the bytes of a transaction

The codec of each kind of transaction is lawful.

A legacy transaction starts with a byte of at least `0xc0`, and a typed one starts with its type.

A fork decodes exactly the bytes of the transactions of the kinds that it has.

So two transactions with the same bytes are equal.

A block holds a typed transaction as a byte string, and from Glamsterdam also a legacy one.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Serialization.Rlp

/-! ## Each codec is lawful -/

instance : LawfulCodec Access where
  ofItem_toItem _ := Item.fields_bind_eq_ok.mpr
    ⟨_, rfl, rfl, by simp [Item.field_toItem, bind, Except.bind, pure, Except.pure]⟩
  toItem_of_ofItem h := by
    obtain ⟨items, rfl, hLen, h⟩ := Item.fields_bind_eq_ok.mp h
    match items, hLen, h with
    | [x0, x1], _, h =>
      simp only [Item.field_bind_eq_ok, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨y0, rfl, y1, rfl, rfl⟩ := h
      rfl

instance : LawfulCodec Authorization where
  ofItem_toItem _ := Item.fields_bind_eq_ok.mpr
    ⟨_, rfl, rfl, by simp [Item.field_toItem, bind, Except.bind, pure, Except.pure]⟩
  toItem_of_ofItem h := by
    obtain ⟨items, rfl, hLen, h⟩ := Item.fields_bind_eq_ok.mp h
    match items, hLen, h with
    | [x0, x1, x2, x3, x4, x5], _, h =>
      simp only [Item.field_bind_eq_ok, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨y0, rfl, y1, rfl, y2, rfl, y3, rfl, y4, rfl, y5, rfl, rfl⟩ := h
      rfl

instance : LawfulCodec LegacyTransaction where
  ofItem_toItem _ := Item.fields_bind_eq_ok.mpr
    ⟨_, rfl, rfl, by simp [Item.field_toItem, bind, Except.bind, pure, Except.pure]⟩
  toItem_of_ofItem h := by
    obtain ⟨items, rfl, hLen, h⟩ := Item.fields_bind_eq_ok.mp h
    match items, hLen, h with
    | [x0, x1, x2, x3, x4, x5, x6, x7, x8], _, h =>
      simp only [Item.field_bind_eq_ok, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨y0, rfl, y1, rfl, y2, rfl, y3, rfl, y4, rfl, y5, rfl, y6, rfl, y7, rfl, y8, rfl,
        rfl⟩ := h
      rfl

instance : LawfulCodec AccessListTransaction where
  ofItem_toItem _ := Item.fields_bind_eq_ok.mpr
    ⟨_, rfl, rfl, by simp [Item.field_toItem, bind, Except.bind, pure, Except.pure]⟩
  toItem_of_ofItem h := by
    obtain ⟨items, rfl, hLen, h⟩ := Item.fields_bind_eq_ok.mp h
    match items, hLen, h with
    | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10], _, h =>
      simp only [Item.field_bind_eq_ok, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨y0, rfl, y1, rfl, y2, rfl, y3, rfl, y4, rfl, y5, rfl, y6, rfl, y7, rfl, y8, rfl, y9,
        rfl, y10, rfl, rfl⟩ := h
      rfl

instance : LawfulCodec FeeMarketTransaction where
  ofItem_toItem _ := Item.fields_bind_eq_ok.mpr
    ⟨_, rfl, rfl, by simp [Item.field_toItem, bind, Except.bind, pure, Except.pure]⟩
  toItem_of_ofItem h := by
    obtain ⟨items, rfl, hLen, h⟩ := Item.fields_bind_eq_ok.mp h
    match items, hLen, h with
    | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11], _, h =>
      simp only [Item.field_bind_eq_ok, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨y0, rfl, y1, rfl, y2, rfl, y3, rfl, y4, rfl, y5, rfl, y6, rfl, y7, rfl, y8, rfl, y9,
        rfl, y10, rfl, y11, rfl, rfl⟩ := h
      rfl

instance : LawfulCodec BlobTransaction where
  ofItem_toItem _ := Item.fields_bind_eq_ok.mpr
    ⟨_, rfl, rfl, by simp [Item.field_toItem, bind, Except.bind, pure, Except.pure]⟩
  toItem_of_ofItem h := by
    obtain ⟨items, rfl, hLen, h⟩ := Item.fields_bind_eq_ok.mp h
    match items, hLen, h with
    | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13], _, h =>
      simp only [Item.field_bind_eq_ok, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨y0, rfl, y1, rfl, y2, rfl, y3, rfl, y4, rfl, y5, rfl, y6, rfl, y7, rfl, y8, rfl, y9,
        rfl, y10, rfl, y11, rfl, y12, rfl, y13, rfl, rfl⟩ := h
      rfl

instance : LawfulCodec SetCodeTransaction where
  ofItem_toItem _ := Item.fields_bind_eq_ok.mpr
    ⟨_, rfl, rfl, by simp [Item.field_toItem, bind, Except.bind, pure, Except.pure]⟩
  toItem_of_ofItem h := by
    obtain ⟨items, rfl, hLen, h⟩ := Item.fields_bind_eq_ok.mp h
    match items, hLen, h with
    | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12], _, h =>
      simp only [Item.field_bind_eq_ok, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨y0, rfl, y1, rfl, y2, rfl, y3, rfl, y4, rfl, y5, rfl, y6, rfl, y7, rfl, y8, rfl, y9,
        rfl, y10, rfl, y11, rfl, y12, rfl, rfl⟩ := h
      rfl

/-! ## The first byte -/

/-- The bytes of a typed transaction have one more byte than its payload. -/
theorem size_typedBytes (type : UInt8) (payload : ByteArray) :
    (typedBytes type payload).size = payload.size + 1 := by
  simp only [typedBytes, ByteArray.size_append]
  exact Nat.add_comm _ _

/-- The first byte of a typed transaction is its type. -/
theorem typedBytes_getElem_zero (type : UInt8) (payload : ByteArray) :
    (typedBytes type payload)[0]'(by simp [size_typedBytes]) = type := by
  simp [typedBytes, ByteArray.getElem_eq_getElem_data, ByteArray.data_append]

/-- The bytes after the type are the payload. -/
theorem extract_typedBytes (type : UInt8) (payload : ByteArray) :
    (typedBytes type payload).extract 1 (typedBytes type payload).size = payload := by
  apply ByteArray.ext
  simp [typedBytes, ByteArray.data_extract, ByteArray.data_append, -ByteArray.size_data,
    ByteArray.size]

/-- Bytes that are not empty are their first byte, then the bytes after it. -/
theorem typedBytes_getElem_extract (bytes : ByteArray) (h : 0 < bytes.size) :
    typedBytes bytes[0] (bytes.extract 1 bytes.size) = bytes := by
  rcases bytes with ⟨⟨_ | ⟨x, xs⟩⟩⟩
  · simp [ByteArray.size] at h
  · apply ByteArray.ext
    simp [typedBytes, ByteArray.data_extract, ByteArray.data_append, -ByteArray.size_data,
      ByteArray.size, ByteArray.getElem_eq_getElem_data]

/-- Bytes whose list starts with `first` are not empty, and their first byte is `first`. -/
theorem getElem_zero_of_toList {bytes : ByteArray} {first : UInt8} {rest : List UInt8}
    (h : bytes.data.toList = first :: rest) : ∃ h0 : 0 < bytes.size, bytes[0] = first := by
  rcases bytes with ⟨⟨l⟩⟩
  simp only at h
  subst h
  exact ⟨by simp [ByteArray.size], by simp [ByteArray.getElem_eq_getElem_data]⟩

/-- A map in `Except` succeeds exactly when the mapped computation succeeds. -/
private theorem map_eq_ok {ε α β : Type} {f : α → β} {x : Except ε α} {y : β} :
    f <$> x = .ok y ↔ ∃ a, x = .ok a ∧ f a = y := by
  cases x <;> simp [Functor.map, Except.map]

/-- A map, then a change of error, succeeds exactly when the computation succeeds. -/
private theorem map_mapError_eq_ok {ε ε' α β : Type} {f : α → β} {g : ε → ε'}
    {x : Except ε α} {y : β} : (f <$> x).mapError g = .ok y ↔ ∃ a, x = .ok a ∧ f a = y := by
  cases x <;> simp [Functor.map, Except.map, Except.mapError]

/-- The type of a transaction is at most 4, so it is below `0xc0`. -/
theorem Transaction.type_le (t : Transaction) : t.type ≤ 4 := by
  cases t <;> simp only [Transaction.type] <;> decide

/-- The bytes of a transaction are not empty, and their first byte tells its kind.

The first byte is at least `0xc0` exactly for a legacy transaction.

For a typed transaction, the first byte is the type. -/
theorem encodeTransaction_head {t : Transaction} {bytes : ByteArray}
    (h : encodeTransaction t = .ok bytes) :
    ∃ h0 : 0 < bytes.size,
      (t.type = 0 ↔ (0xc0 : UInt8) ≤ bytes[0]) ∧ (t.type ≠ 0 → bytes[0] = t.type) := by
  cases t with
  | legacy tx =>
    obtain ⟨first, rest, hList, hFirst⟩ := encode_list_head _ _ h
    obtain ⟨h0, hEq⟩ := getElem_zero_of_toList hList
    exact ⟨h0, by simp [Transaction.type, hEq, hFirst], by simp [Transaction.type]⟩
  | accessList tx | feeMarket tx | blob tx | setCode tx =>
    simp only [encodeTransaction, map_eq_ok] at h
    obtain ⟨payload, -, rfl⟩ := h
    exact ⟨by simp [size_typedBytes], by simp [Transaction.type, typedBytes_getElem_zero],
      by simp [Transaction.type, typedBytes_getElem_zero]⟩

/-! ## Decoding undoes encoding -/

/-- Decoding the bytes of a transaction gives the transaction, at each fork that has its kind. -/
theorem decodeTransaction_encodeTransaction {fork : Fork} {t : Transaction} {bytes : ByteArray}
    (h : encodeTransaction t = .ok bytes) (hFork : t.fork ≤ fork) :
    decodeTransaction fork bytes = .ok t := by
  obtain ⟨h0, hLegacy, -⟩ := encodeTransaction_head h
  cases t with
  | legacy tx =>
    have hFirst : (0xc0 : UInt8) ≤ bytes[0] :=hLegacy.mp rfl
    simp [decodeTransaction, h0, hFirst, Codec.decode_encode h, Functor.map, Except.map,
      Except.mapError]
  | accessList tx | feeMarket tx | blob tx | setCode tx =>
    simp only [encodeTransaction, map_eq_ok] at h
    obtain ⟨payload, hPayload, rfl⟩ := h
    simp [Transaction.fork, Transaction.type, typeFork] at hFork
    simp [decodeTransaction, h0, typedBytes_getElem_zero, typeFork, hFork, decodePayload,
      extract_typedBytes, Codec.decode_encode hPayload, Functor.map, Except.map, Except.mapError]

/-- Bytes that decode to a transaction are its bytes, and the fork has its kind. -/
theorem encodeTransaction_of_decodeTransaction {fork : Fork} {bytes : ByteArray}
    {t : Transaction} (h : decodeTransaction fork bytes = .ok t) :
    encodeTransaction t = .ok bytes ∧ t.fork ≤ fork := by
  unfold decodeTransaction at h
  split at h
  · rename_i h0
    dsimp only at h
    split at h
    · -- A legacy transaction: the RLP codec is canonical.
      obtain ⟨tx, hTx, rfl⟩ := map_mapError_eq_ok.mp h
      exact ⟨Codec.encode_decode hTx, Fork.frontier_le fork⟩
    · -- A typed transaction: its type, then the payload that the codec reads back.
      rw [← typedBytes_getElem_extract bytes h0]
      split at h
      · rename_i since hSince
        split at h
        · rename_i hLe
          unfold decodePayload at h
          unfold typeFork at hSince
          repeat' split at h
          all_goals first
            | cases h
            | obtain ⟨tx, hTx, rfl⟩ := map_mapError_eq_ok.mp h
              simp_all [encodeTransaction, Codec.encode_decode hTx, Functor.map, Except.map,
                Transaction.fork, Transaction.type, typeFork]
        · cases h
      · cases h
  · cases h

/-- A fork decodes bytes to a transaction exactly when they encode it and the fork has its kind.
-/
theorem decodeTransaction_eq_ok_iff (fork : Fork) (bytes : ByteArray) (t : Transaction) :
    decodeTransaction fork bytes = .ok t ↔ encodeTransaction t = .ok bytes ∧ t.fork ≤ fork :=
  ⟨encodeTransaction_of_decodeTransaction, fun ⟨h, hFork⟩ =>
    decodeTransaction_encodeTransaction h hFork⟩

/-- Two transactions with the same bytes are equal. -/
theorem encodeTransaction_injective {t u : Transaction} {bytes : ByteArray}
    (ht : encodeTransaction t = .ok bytes) (hu : encodeTransaction u = .ok bytes) : t = u := by
  -- The last fork has every kind, so it decodes both to the same transaction.
  have := (decodeTransaction_encodeTransaction ht (Fork.le_hegota t.fork)).symm.trans
    (decodeTransaction_encodeTransaction hu (Fork.le_hegota u.fork))
  cases this
  rfl

/-! ## The transactions of a block -/

/-- A byte string that starts with a type holds the transaction of its bytes, at every fork. -/
theorem decodeBodyTransaction_typed (fork : Fork) {bytes : ByteArray} (h0 : 0 < bytes.size)
    (hType : bytes[0] < (0xc0 : UInt8)) :
    decodeBodyTransaction fork (.bytes bytes) = decodeTransaction fork bytes := by
  simp [decodeBodyTransaction, h0, hType]

/-- Before Glamsterdam, a byte string that starts like an RLP list holds no transaction. -/
theorem decodeBodyTransaction_legacy_of_lt {fork : Fork} (hFork : fork < .glamsterdam)
    {bytes : ByteArray} (h0 : 0 < bytes.size) (hList : (0xc0 : UInt8) ≤ bytes[0]) :
    decodeBodyTransaction fork (.bytes bytes) = .error (.unsupportedType bytes[0]) := by
  have hType : ¬bytes[0] < 0xc0 := UInt8.not_lt.mpr hList
  have hGlam : ¬Fork.glamsterdam ≤ fork := fun h => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hFork h)
  simp [decodeBodyTransaction, h0, hType, hGlam]

/-- From Glamsterdam, a byte string holds the transaction of its bytes, unless it starts with 0xff.
-/
theorem decodeBodyTransaction_bytes {fork : Fork} (hFork : .glamsterdam ≤ fork)
    {bytes : ByteArray} (hFF : ∀ h : 0 < bytes.size, bytes[0] ≠ (0xff : UInt8)) :
    decodeBodyTransaction fork (.bytes bytes) = decodeTransaction fork bytes := by
  unfold decodeBodyTransaction
  by_cases h0 : 0 < bytes.size
  · simp [h0, hFork, hFF h0]
  · simp [h0, decodeTransaction]

end EthLib.Execution.Transactions
