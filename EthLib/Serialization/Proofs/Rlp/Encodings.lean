module

public import Batteries.Data.List.Basic
public import EthLib.Serialization.Proofs.Rlp.Canonical
import EthLib.Base.Proofs.Bytes

/-!
# Proofs: the encodings of the items of a list

The encoding of a list splits into the encodings of its items, in order.

So an item paired with its slice of the bytes is paired with its own encoding.

Pairing items with encodings succeeds exactly when the two lists have one length.

An item that keeps its own encoding splits into its items, each with its own encoding.
-/

@[expose] public section

namespace EthLib.Serialization.Rlp

/-- An item that the decoder reads ends where the head of the item says it ends. -/
private theorem readHead_of_decodeItem {input : ByteArray} {pos stop next : Nat}
    {bounded : stop ≤ input.size} {x : Item} {hNext : pos < next ∧ next ≤ stop}
    (h : decodeItem input pos stop bounded = .ok (x, ⟨next, hNext⟩)) :
    (∃ value after within, readHead input pos stop bounded = .ok (.bytes value next after within))
      ∨ ∃ start after ordered within,
        readHead input pos stop bounded = .ok (.list start next after ordered within) := by
  unfold decodeItem at h
  split at h
  · cases h
  · simp only [Except.ok.injEq, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact .inl ⟨_, _, _, by assumption⟩
  · split at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq, Subtype.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact .inr ⟨_, _, _, _, by assumption⟩

/-- The splitter steps over one item whose head ends at `next`. -/
private theorem splitItems_step {input : ByteArray} {pos stop next : Nat}
    {bounded : stop ≤ input.size} {done : Array ByteArray} (hPos : pos < stop)
    (hHead : (∃ value after within,
        readHead input pos stop bounded = .ok (.bytes value next after within))
      ∨ ∃ start after ordered within,
        readHead input pos stop bounded = .ok (.list start next after ordered within)) :
    splitItems input pos stop bounded done =
      splitItems input next stop bounded (done.push (input.extract pos next)) := by
  rw [splitItems, ite_eq_left hPos]
  rcases hHead with ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ <;> rw [h]

/-- Where the decoder reads items, the splitter cuts out the encoding of each. -/
private theorem splitItems_of_decodeItems (n : Nat) {input : ByteArray} {pos stop : Nat}
    {bounded : stop ≤ input.size} (hLen : stop - pos ≤ n) {done : Array ByteArray}
    {xs : List Item} (h : decodeItems input pos stop bounded = .ok xs) :
    ∃ encodings, splitItems input pos stop bounded done = .ok (done ++ encodings.toArray) ∧
      List.Forall₂ (fun item e => encode item = .ok e) xs encodings := by
  induction n generalizing pos done xs with
  | zero =>
    -- No byte is left, so there is no item.
    rw [decodeItems_eq input pos stop bounded, ite_eq_right (by omega)] at h
    cases h
    refine ⟨[], ?_, .nil⟩
    rw [splitItems, ite_eq_right (by omega)]
    simp
  | succ m ih =>
    rw [decodeItems_eq input pos stop bounded] at h
    by_cases hPos : pos < stop
    case neg =>
      rw [ite_eq_right hPos] at h
      cases h
      refine ⟨[], ?_, .nil⟩
      rw [splitItems, ite_eq_right hPos]
      simp
    rw [ite_eq_left hPos] at h
    -- The first item, then the items of the rest, which is shorter.
    cases hFirst : decodeItem input pos stop bounded with
    | error err =>
      rw [hFirst] at h
      cases h
    | ok res =>
      obtain ⟨item, ⟨next, hNext⟩⟩ := res
      rw [hFirst] at h
      cases hRest : decodeItems input next stop bounded with
      | error err =>
        simp [hRest, bind, Except.bind] at h
      | ok items =>
        simp only [hRest, bind, Except.bind, Except.ok.injEq] at h
        subst h
        -- The bytes of the first item are its encoding.
        obtain ⟨e, hEncode, hBytes⟩ := encode_of_decodeItem bounded hFirst
        have hE : input.extract pos next = e := Base.byteArray_eq_of_toList hBytes
        obtain ⟨encodings, hSplit, hAll⟩ :=
          ih (pos := next) (done := done.push (input.extract pos next)) (by omega) hRest
        refine ⟨e :: encodings, ?_, .cons hEncode hAll⟩
        rw [splitItems_step hPos (readHead_of_decodeItem hFirst), hSplit, hE]
        simp

/-- The items of pairs made from as many items as encodings are those items. -/
private theorem map_item_zipWith : {items : List Item} → {encodings : List ByteArray} →
    items.length = encodings.length →
    (List.zipWith Encoded.mk items encodings).map (·.item) = items
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [map_item_zipWith h]

/-- The encodings of pairs made from as many items as encodings are those encodings. -/
private theorem map_bytes_zipWith : {items : List Item} → {encodings : List ByteArray} →
    items.length = encodings.length →
    (List.zipWith Encoded.mk items encodings).map (·.bytes) = encodings
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [map_bytes_zipWith h]

/-- Pairing the items of a list with its encodings gives the list back. -/
private theorem zipWith_map_item_map_bytes : (kept : List Encoded) →
    List.zipWith Encoded.mk (kept.map (·.item)) (kept.map (·.bytes)) = kept
  | [] => rfl
  | _ :: rest => by simp [zipWith_map_item_map_bytes rest]

/-- Pairs whose encodings are related to their items, in order, each hold the relation. -/
private theorem forall_of_forall₂ : {kept : List Encoded} →
    List.Forall₂ (fun item e => encode item = .ok e) (kept.map (·.item)) (kept.map (·.bytes)) →
    ∀ e ∈ kept, encode e.item = .ok e.bytes
  | [], _ => by simp
  | _ :: _, .cons hHead hRest => by
    simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨hHead, forall_of_forall₂ hRest⟩

/-- An encoding is a function of its item, so encodings related to the items are the bytes. -/
private theorem eq_bytes_of_forall₂ : {kept : List Encoded} → {encodings : List ByteArray} →
    (∀ e ∈ kept, encode e.item = .ok e.bytes) →
    List.Forall₂ (fun item e => encode item = .ok e) (kept.map (·.item)) encodings →
    encodings = kept.map (·.bytes)
  | [], [], _, _ => rfl
  | head :: _, _ :: _, hEach, .cons hHead hRest => by
    simp only [List.mem_cons, forall_eq_or_imp] at hEach
    have hSame : _ = head.bytes := Except.ok.inj (hHead.symm.trans hEach.1)
    rw [List.map_cons, hSame, eq_bytes_of_forall₂ hEach.2 hRest]

/-- The encoding of a list splits into the encodings of its items, one for each item, in order. -/
theorem listEncodings_of_encode {items : List Item} {data : ByteArray}
    (h : encode (.list items) = .ok data) :
    ∃ encodings, listEncodings data = .ok encodings ∧
      List.Forall₂ (fun item e => encode item = .ok e) items encodings := by
  -- The whole input is read as the list, so its head is a list head that ends at the end.
  obtain ⟨hNext, hDecode⟩ := decodeItem_encode (.list items) data h (input := data) (pos := 0)
    (rest := []) (Nat.le_refl _) (by simp)
  have hDecode' := hDecode
  unfold decodeItem at hDecode'
  split at hDecode'
  · cases hDecode'
  · simp at hDecode'
  rename_i start next after ordered within hHead
  split at hDecode'
  · cases hDecode'
  rename_i payload hItems
  simp only [Except.ok.injEq, Prod.mk.injEq, Item.list.injEq, Subtype.mk.injEq] at hDecode'
  obtain ⟨rfl, rfl⟩ := hDecode'
  -- The payload splits into the encodings of its items.
  obtain ⟨encodings, hSplit, hAll⟩ :=
    splitItems_of_decodeItems _ (Nat.le_refl _) (done := #[]) hItems
  refine ⟨encodings, ?_, hAll⟩
  simp only [Nat.zero_add] at hSplit hHead
  unfold listEncodings
  rw [hHead]
  simp [hSplit, Except.map]

/-- Pairing gives the items with the encodings, when there are as many of each. -/
theorem Encoded.zip_eq_ok_iff {items : List Item} {encodings : List ByteArray}
    {kept : List Encoded} :
    Encoded.zip items encodings = .ok kept ↔
      kept.map (·.item) = items ∧ kept.map (·.bytes) = encodings := by
  unfold Encoded.zip
  constructor
  · intro h
    split at h
    · cases h
      rename_i hLen
      exact ⟨map_item_zipWith hLen, map_bytes_zipWith hLen⟩
    · cases h
  · rintro ⟨rfl, rfl⟩
    -- Both lists come from the same pairs, so they have one length and pair back to them.
    rw [ite_eq_left (by simp), zipWith_map_item_map_bytes]

/-- Each item of a list, paired with its slice of the encoding of the list, keeps its encoding.

And every list of items with their own encodings comes out of that pairing. -/
theorem zip_listEncodings_eq_ok_iff {items : List Item} {data : ByteArray}
    {kept : List Encoded} (h : encode (.list items) = .ok data) :
    (listEncodings data >>= Encoded.zip items) = .ok kept ↔
      kept.map (·.item) = items ∧ ∀ e ∈ kept, encode e.item = .ok e.bytes := by
  obtain ⟨encodings, hList, hAll⟩ := listEncodings_of_encode h
  simp only [hList, bind, Except.bind, Encoded.zip_eq_ok_iff]
  constructor
  · rintro ⟨rfl, rfl⟩
    -- Each pair is an item and the encoding next to it.
    exact ⟨rfl, forall_of_forall₂ hAll⟩
  · rintro ⟨rfl, hEach⟩
    -- The encoding of each item is a function of the item, so the encodings are the bytes.
    exact ⟨rfl, (eq_bytes_of_forall₂ hEach hAll).symm⟩

/-- The parts of an item that keeps its own encoding are its items, each with its own encoding.

And every list of items with their own encodings comes out as its parts. -/
theorem Encoded.parts_eq_ok_iff {e : Encoded} {kept : List Encoded}
    (h : encode e.item = .ok e.bytes) :
    e.parts = .ok kept ↔
      e.item = .list (kept.map (·.item)) ∧ ∀ k ∈ kept, encode k.item = .ok k.bytes := by
  obtain ⟨item, bytes⟩ := e
  cases item with
  | bytes b => simp [Encoded.parts]
  | list items =>
    simp only [Encoded.parts, Item.list.injEq] at h ⊢
    rw [zip_listEncodings_eq_ok_iff h, eq_comm (a := items)]

/-- The parts of an item are its items, whatever bytes it keeps. -/
theorem Encoded.item_of_parts {e : Encoded} {kept : List Encoded} (h : e.parts = .ok kept) :
    e.item = .list (kept.map (·.item)) := by
  obtain ⟨item, bytes⟩ := e
  cases item with
  | bytes b => simp [Encoded.parts] at h
  | list items =>
    simp only [Encoded.parts, bind, Except.bind] at h
    split at h
    · cases h
    · rw [(Encoded.zip_eq_ok_iff.mp h).1]

/-- Lists related item by item have one length. -/
private theorem length_of_forall₂ {items : List Item} {encodings : List ByteArray} :
    List.Forall₂ (fun item e => encode item = .ok e) items encodings →
    items.length = encodings.length
  | .nil => rfl
  | .cons _ hRest => by simp [length_of_forall₂ hRest]

/-- A list that keeps its own encoding has parts: its items, each with its own encoding. -/
theorem Encoded.parts_of_encode {e : Encoded} {items : List Item}
    (h : encode e.item = .ok e.bytes) (hl : e.item = .list items) :
    ∃ kept, e.parts = .ok kept ∧ kept.map (·.item) = items ∧
      ∀ k ∈ kept, encode k.item = .ok k.bytes := by
  obtain ⟨encodings, -, hAll⟩ := listEncodings_of_encode (hl ▸ h)
  -- Each item is paired with its own encoding.
  have hLen := length_of_forall₂ hAll
  have hItems := map_item_zipWith hLen
  have hBytes := map_bytes_zipWith hLen
  have hEach : ∀ k ∈ List.zipWith Encoded.mk items encodings, encode k.item = .ok k.bytes :=
    forall_of_forall₂ (by rw [hItems, hBytes]; exact hAll)
  exact ⟨_, (Encoded.parts_eq_ok_iff h).mpr ⟨by rw [hl, hItems], hEach⟩, hItems, hEach⟩

/-- The payload of a two-item list that encodes as `data` is cut from `data` with its encoding. -/
theorem payloadEncodings_of_encode {first : Item} {items : List Item} {data : ByteArray}
    (h : encode (.list [first, .list items]) = .ok data) :
    ∃ payload, encode (.list items) = .ok payload ∧
      payloadEncodings data = listEncodings payload := by
  -- The list has two encodings, and the second is that of the payload.
  obtain ⟨encodings, hList, hAll⟩ := listEncodings_of_encode h
  cases hAll with
  | cons _ hRest =>
    cases hRest with
    | cons hPayload hNil =>
      cases hNil
      exact ⟨_, hPayload, by simp [payloadEncodings, hList, bind, Except.bind]⟩

end EthLib.Serialization.Rlp
