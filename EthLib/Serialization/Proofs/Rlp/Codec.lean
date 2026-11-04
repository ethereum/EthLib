module

public import EthLib.Serialization.Rlp.Codec
public import EthLib.Serialization.Proofs.Rlp.Canonical
public import EthLib.Serialization.Proofs.Rlp.Scalar
public import EthLib.Serialization.Proofs.Rlp.Vectors

/-!
# Proofs: typed RLP codecs

A lawful codec reads back each value it writes, and writes back each item it reads.

Every codec here is lawful.

So a typed decoder accepts a byte string for a value exactly when it encodes that value.
-/

@[expose] public section

namespace EthLib.Serialization.Rlp

open EthLib.Base

/-- A codec whose two directions undo each other. -/
class LawfulCodec (α : Type) [Codec α] : Prop where
  /-- Reading the item of a value gives the value. -/
  ofItem_toItem (x : α) : Codec.ofItem (Codec.toItem x) = .ok x
  /-- An item that holds a value is the item of that value. -/
  toItem_of_ofItem {item : Item} {x : α} : Codec.ofItem item = .ok x → Codec.toItem x = item

namespace Codec

variable {α : Type} [Codec α] [LawfulCodec α]

/-- Two values with the same item are equal. -/
theorem toItem_injective : Function.Injective (Codec.toItem : α → Item) := by
  intro x y h
  have hx := LawfulCodec.ofItem_toItem x
  rw [h, LawfulCodec.ofItem_toItem y] at hx
  cases hx
  rfl

/-- Decoding the encoding of a value gives the value. -/
theorem decode_encode {x : α} {b : ByteArray} (h : encode x = .ok b) : decode b = .ok x := by
  simp [decode, Rlp.decode_encode _ _ h, LawfulCodec.ofItem_toItem, bind, Except.bind]

/-- A byte string that decodes to a value is the encoding of that value. -/
theorem encode_decode {b : ByteArray} {x : α} (h : decode b = .ok x) : encode x = .ok b := by
  unfold decode at h
  cases hItem : Rlp.decode b with
  | error e => simp [hItem, bind, Except.bind] at h
  | ok item =>
    simp only [hItem, bind, Except.bind] at h
    -- The item of the value is the decoded item, which encodes as `b`.
    rw [encode, LawfulCodec.toItem_of_ofItem h]
    exact Rlp.encode_decode b item hItem

/-- A typed decoder accepts exactly the encoding of each value. -/
theorem decode_eq_ok_iff (b : ByteArray) (x : α) : decode b = .ok x ↔ encode x = .ok b :=
  ⟨encode_decode, decode_encode⟩

end Codec

/-! ## The helpers -/

/-- Reading the bytes of an item succeeds exactly on a byte string. -/
theorem Item.toBytes_eq_ok {item : Item} {data : ByteArray} :
    item.toBytes = .ok data ↔ item = .bytes data := by
  cases item <;> simp [Item.toBytes]

/-- Reading the items of an item succeeds exactly on a list. -/
theorem Item.toItems_eq_ok {item : Item} {items : List Item} :
    item.toItems = .ok items ↔ item = .list items := by
  cases item <;> simp [Item.toItems]

/-- The fields of a structure with `count` fields are a list of `count` items. -/
theorem Item.fields_eq_ok {count : Nat} {item : Item} {items : List Item} :
    item.fields count = .ok items ↔ item = .list items ∧ items.length = count := by
  cases item with
  | bytes data => simp [Item.fields, Item.toItems, bind, Except.bind]
  | list xs =>
    simp only [Item.fields, Item.toItems, bind, Except.bind, Item.list.injEq]
    split <;> simp_all [eq_comm]

/-- A scalar below `2 ^ bits` reads back as itself. -/
theorem Item.toScalarBelow_scalar {bits n : Nat} (h : n < 2 ^ bits) :
    (Item.scalar n).toScalarBelow bits = .ok n := by
  simp [Item.toScalarBelow, toScalar_scalar, h, bind, Except.bind]

/-- An item that holds a scalar below `2 ^ bits` is that scalar. -/
theorem Item.eq_scalar_of_toScalarBelow {bits n : Nat} {item : Item}
    (h : item.toScalarBelow bits = .ok n) : item = .scalar n ∧ n < 2 ^ bits := by
  unfold Item.toScalarBelow at h
  cases hs : item.toScalar with
  | error e => simp [hs, bind, Except.bind] at h
  | ok m =>
    simp only [hs, bind, Except.bind] at h
    split at h
    · cases h
      exact ⟨eq_scalar_of_toScalar item _ hs, by assumption⟩
    · cases h

/-! ## Each codec is lawful -/

instance : LawfulCodec Nat where
  ofItem_toItem := toScalar_scalar
  toItem_of_ofItem h := (eq_scalar_of_toScalar _ _ h).symm

instance : LawfulCodec U256 where
  ofItem_toItem w := by
    simp [Codec.ofItem, Codec.toItem, Item.toScalarBelow_scalar w.isLt, bind, Except.bind,
      pure, Except.pure]
  toItem_of_ofItem {item w} h := by
    simp only [Codec.ofItem, bind, Except.bind] at h
    cases hs : item.toScalarBelow 256 with
    | error e => simp [hs] at h
    | ok n =>
      simp only [hs, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨rfl, hn⟩ := Item.eq_scalar_of_toScalarBelow hs
      subst h
      simp [Codec.toItem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

instance : LawfulCodec UInt64 where
  ofItem_toItem x := by
    simp [Codec.ofItem, Codec.toItem, Item.toScalarBelow_scalar x.toNat_lt, bind, Except.bind,
      pure, Except.pure]
  toItem_of_ofItem {item x} h := by
    simp only [Codec.ofItem, bind, Except.bind] at h
    cases hs : item.toScalarBelow 64 with
    | error e => simp [hs] at h
    | ok n =>
      simp only [hs, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨rfl, hn⟩ := Item.eq_scalar_of_toScalarBelow hs
      subst h
      simp [Codec.toItem, UInt64.toNat_ofNat_of_lt' hn]

instance : LawfulCodec Bool where
  ofItem_toItem b := by
    cases b <;>
      simp [Codec.ofItem, Codec.toItem, Item.toScalarBelow_scalar, bind, Except.bind, pure,
        Except.pure]
  toItem_of_ofItem {item b} h := by
    simp only [Codec.ofItem, bind, Except.bind] at h
    cases hs : item.toScalarBelow 1 with
    | error e => simp [hs] at h
    | ok n =>
      simp only [hs, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨rfl, hn⟩ := Item.eq_scalar_of_toScalarBelow hs
      subst h
      -- The scalar is 0 or 1, and each is the item of its boolean.
      have : n = 0 ∨ n = 1 := by omega
      rcases this with rfl | rfl <;> rfl

instance : LawfulCodec ByteArray where
  ofItem_toItem _ := rfl
  toItem_of_ofItem h := (Item.toBytes_eq_ok.mp h).symm

instance {n : Nat} : LawfulCodec (Vector UInt8 n) where
  ofItem_toItem v := by
    have hSize : ({ data := v.toArray } : ByteArray).size = n := by simp [ByteArray.size]
    simp [Codec.ofItem, Codec.toItem, Item.toBytes, bind, Except.bind, hSize]
  toItem_of_ofItem {item v} h := by
    simp only [Codec.ofItem, bind, Except.bind] at h
    cases hb : item.toBytes with
    | error e => simp [hb] at h
    | ok data =>
      simp only [hb] at h
      split at h
      · cases h
        rw [Item.toBytes_eq_ok.mp hb]
        rfl
      · cases h

/-- Reading back the items of a list of values gives the values. -/
theorem mapM_ofItem_map_toItem {α : Type} [Codec α] [LawfulCodec α] :
    (xs : List α) → (xs.map Codec.toItem).mapM Codec.ofItem = .ok xs
  | [] => rfl
  | x :: xs => by
    simp [List.mapM_cons, LawfulCodec.ofItem_toItem, mapM_ofItem_map_toItem xs, bind,
      Except.bind, pure, Except.pure]

/-- Items that read back as values are the items of those values. -/
theorem map_toItem_of_mapM_ofItem {α : Type} [Codec α] [LawfulCodec α] :
    (items : List Item) → (xs : List α) → items.mapM Codec.ofItem = .ok xs →
      xs.map Codec.toItem = items
  | [], xs, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    simp [← h]
  | item :: items, xs, h => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases hx : (Codec.ofItem item : Except RlpError α) with
    | error e => simp [hx] at h
    | ok x =>
      cases hxs : items.mapM (Codec.ofItem : Item → Except RlpError α) with
      | error e => simp [hx, hxs] at h
      | ok ys =>
        simp only [hx, hxs, pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [LawfulCodec.toItem_of_ofItem hx, map_toItem_of_mapM_ofItem items ys hxs]

instance {α : Type} [Codec α] [LawfulCodec α] : LawfulCodec (List α) where
  ofItem_toItem xs := by
    simp only [Codec.ofItem, Codec.toItem, Item.toItems, bind, Except.bind]
    exact mapM_ofItem_map_toItem xs
  toItem_of_ofItem {item xs} h := by
    simp only [Codec.ofItem, bind, Except.bind] at h
    cases hi : item.toItems with
    | error e => simp [hi] at h
    | ok items =>
      simp only [hi] at h
      rw [Item.toItems_eq_ok.mp hi]
      exact congrArg Item.list (map_toItem_of_mapM_ofItem items xs h)

instance {α : Type} [Codec α] [LawfulCodec α] [NeverEmpty α] : LawfulCodec (Option α) where
  ofItem_toItem
    | none => rfl
    | some x => by
      -- The item of a value is not the empty byte string, so it reads back as that value.
      simp [Codec.ofItem, Codec.toItem, NeverEmpty.toItem_ne_empty x, LawfulCodec.ofItem_toItem x,
        Functor.map, Except.map]
  toItem_of_ofItem {item x} h := by
    simp only [Codec.ofItem] at h
    split at h
    · -- The empty byte string is the item of none.
      cases h
      rename_i hEmpty
      exact hEmpty.symm
    · -- Any other item must hold a value of the type.
      cases hy : (Codec.ofItem item : Except RlpError α) with
      | error e => simp [hy, Functor.map, Except.map] at h
      | ok y =>
        simp only [hy, Functor.map, Except.map, Except.ok.injEq] at h
        subst h
        exact (LawfulCodec.toItem_of_ofItem hy : Codec.toItem y = item)

/-- An integer has no optional form.

The integer 0 is the empty byte string, so it would read back as none. -/
theorem not_neverEmpty_nat : ¬ NeverEmpty Nat :=
  fun h => h.toItem_ne_empty 0 rfl

/-- None is written as the single byte `80`, and no other byte string reads back as none. -/
theorem Codec.decode_eq_ok_none_iff {α : Type} [Codec α] [LawfulCodec α] [NeverEmpty α]
    (b : ByteArray) : Codec.decode b = .ok (none : Option α) ↔ b = ⟨#[0x80]⟩ := by
  rw [Codec.decode_eq_ok_iff]
  have : Codec.encode (none : Option α) = .ok ⟨#[0x80]⟩ := rfl
  rw [this]
  exact ⟨fun h => (Except.ok.inj h).symm, fun h => h ▸ rfl⟩

/-! ## Known answers

Each claim pins one typed decoding, and the kernel evaluates it.

The inputs are worked out by hand from the rules of the codecs. -/

open Vectors

/-- The error of a failed decoding, or `none` for a success. -/
def decodeError {α : Type} (result : Except RlpError α) : Option RlpError :=
  match result with
  | .error e => some e
  | .ok _ => none

/-- `82 04 00` holds the word 1024. -/
theorem decode_u256_1024 :
    (Codec.decode (byteArrayOf 3 0x820400) : Except RlpError U256).toOption = some 1024 := by
  decide +kernel

/-- `80` holds false, and `01` holds true. -/
theorem decode_bool :
    (Codec.decode (byteArrayOf 1 0x80) : Except RlpError Bool).toOption = some false ∧
      (Codec.decode (byteArrayOf 1 0x01) : Except RlpError Bool).toOption = some true := by
  decide +kernel

/-- `02` holds no boolean: 2 is not below 2^1. -/
theorem decode_bool_two :
    decodeError (Codec.decode (byteArrayOf 1 0x02) : Except RlpError Bool) =
      some (.scalarTooLarge 2 1) := by
  decide +kernel

/-- `89 01` then 8 zero bytes holds 2^64, which is no 64-bit integer. -/
theorem decode_uint64_overflow :
    decodeError (Codec.decode (byteArrayOf 10 0x89010000000000000000) : Except RlpError UInt64) =
      some (.scalarTooLarge (2 ^ 64) 64) := by
  decide +kernel

/-- `80`, the empty byte string, is the recipient of a contract creation. -/
theorem decode_recipient_none :
    (Codec.decode (byteArrayOf 1 0x80) : Except RlpError (Option Address)).toOption =
      some none := by
  decide +kernel

/-- `81 ff` is one byte, which is no address. -/
theorem decode_recipient_short :
    decodeError (Codec.decode (byteArrayOf 2 0x81ff) : Except RlpError (Option Address)) =
      some (.wrongLength 20 1) := by
  decide +kernel

/-- `c2 01 02` holds the list of the integers 1 and 2. -/
theorem decode_list :
    (Codec.decode (byteArrayOf 3 0xc20102) : Except RlpError (List Nat)).toOption =
      some [1, 2] := by
  decide +kernel

/-- `c2 01 02` is a list, so it holds no word. -/
theorem decode_u256_list :
    decodeError (Codec.decode (byteArrayOf 3 0xc20102) : Except RlpError U256) =
      some .listAsScalar := by
  decide +kernel

end EthLib.Serialization.Rlp
