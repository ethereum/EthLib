module

public import EthLib.Base.Proofs.Fork
public import EthLib.Serialization.Rlp.Codec
public import EthLib.Serialization.Proofs.Rlp.Canonical
public import EthLib.Serialization.Proofs.Rlp.Scalar

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

/-- A list of `count` items holds the fields of a structure with `count` fields. -/
theorem Item.fields_list {count : Nat} {items : List Item} (h : items.length = count) :
    (Item.list items).fields count = .ok items :=
  Item.fields_eq_ok.mpr ⟨rfl, h⟩

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

/-- A structure reads back exactly when its item is a list of its fields and they read back. -/
theorem Item.fields_bind_eq_ok {β : Type} {count : Nat} {item : Item}
    {f : List Item → Except RlpError β} {y : β} :
    (item.fields count >>= f) = .ok y ↔
      ∃ items, item = .list items ∧ items.length = count ∧ f items = .ok y := by
  cases h : item.fields count with
  | error e =>
    simp only [bind, Except.bind, reduceCtorEq, false_iff, not_exists, not_and]
    intro items hItem hLen
    rw [Item.fields_eq_ok.mpr ⟨hItem, hLen⟩] at h
    cases h
  | ok items =>
    obtain ⟨rfl, hLen⟩ := Item.fields_eq_ok.mp h
    simp [bind, Except.bind, hLen]

/-- A field of a structure holds a value exactly when its item holds that value. -/
theorem Item.field_eq_ok {α : Type} [Codec α] {index : Nat} {item : Item} {x : α} :
    Item.field index item = .ok x ↔ Codec.ofItem item = .ok x := by
  unfold Item.field
  cases (Codec.ofItem item : Except RlpError α) <;> simp [Except.mapError]

/-- The fields of a structure, read back from their items. -/
theorem Item.field_toItem {α : Type} [Codec α] [LawfulCodec α] (index : Nat) (x : α) :
    Item.field index (Codec.toItem x) = .ok x :=
  Item.field_eq_ok.mpr (LawfulCodec.ofItem_toItem x)

/-- A field and the rest of a structure read back exactly when the field holds a value.

The rest must also read back from that value, and the field is then the item of the value. -/
theorem Item.field_bind_eq_ok {α β : Type} [Codec α] [LawfulCodec α] {index : Nat} {item : Item}
    {f : α → Except RlpError β} {y : β} :
    (Item.field index item >>= f) = .ok y ↔ ∃ x, item = Codec.toItem x ∧ f x = .ok y := by
  constructor
  · intro h
    cases hx : (Item.field index item : Except RlpError α) with
    | error e => simp [hx, bind, Except.bind] at h
    | ok x =>
      simp only [hx, bind, Except.bind] at h
      exact ⟨x, (LawfulCodec.toItem_of_ofItem (Item.field_eq_ok.mp hx)).symm, h⟩
  · rintro ⟨x, rfl, h⟩
    simp [Item.field_toItem, bind, Except.bind, h]

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

instance : LawfulCodec UInt16 where
  ofItem_toItem x := by
    simp [Codec.ofItem, Codec.toItem, Item.toScalarBelow_scalar x.toNat_lt, bind, Except.bind,
      pure, Except.pure]
  toItem_of_ofItem {item x} h := by
    simp only [Codec.ofItem, bind, Except.bind] at h
    cases hs : item.toScalarBelow 16 with
    | error e => simp [hs] at h
    | ok n =>
      simp only [hs, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨rfl, hn⟩ := Item.eq_scalar_of_toScalarBelow hs
      subst h
      simp [Codec.toItem, UInt16.toNat_ofNat_of_lt' hn]

instance : LawfulCodec UInt8 where
  ofItem_toItem x := by
    simp [Codec.ofItem, Codec.toItem, Item.toScalarBelow_scalar x.toNat_lt, bind, Except.bind,
      pure, Except.pure]
  toItem_of_ofItem {item x} h := by
    simp only [Codec.ofItem, bind, Except.bind] at h
    cases hs : item.toScalarBelow 8 with
    | error e => simp [hs] at h
    | ok n =>
      simp only [hs, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨rfl, hn⟩ := Item.eq_scalar_of_toScalarBelow hs
      subst h
      simp [Codec.toItem, UInt8.toNat_ofNat_of_lt' hn]

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

instance : LawfulCodec Item where
  ofItem_toItem _ := rfl
  toItem_of_ofItem h := (Except.ok.inj h).symm

/-! ## Structures

A decoder of a structure reads its fields one after another.

Each read takes the item of one field, so the items are the items of the fields, in order. -/

/-- A step of a decoder succeeds exactly when it and the rest succeed. -/
theorem bind_eq_ok {α β : Type} {x : Except RlpError α} {f : α → Except RlpError β} {y : β} :
    x >>= f = .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x <;> simp [bind, Except.bind]

section Fields

variable {α : Type} [Codec α] [LawfulCodec α]

/-- A field reads back from its item. -/
theorem Item.readField_cons (count : Nat) (x : α) (rest : List Item) :
    Item.readField count (Codec.toItem x :: rest) = .ok (x, rest) := by
  simp [Item.readField, Item.field_toItem, bind, Except.bind, pure, Except.pure]

/-- A field that reads from some items is the first of them. -/
theorem Item.eq_of_readField {count : Nat} {items rest : List Item} {x : α}
    (h : Item.readField count items = .ok (x, rest)) : items = Codec.toItem x :: rest := by
  cases items with
  | nil => simp [Item.readField] at h
  | cons item tail =>
    obtain ⟨y, hItem, h⟩ := Item.field_bind_eq_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [hItem]

omit [LawfulCodec α] in
/-- A field that appears at a fork has one item from that fork on, and none before. -/
theorem Item.length_ofSince {f fork : Fork} (x : Since f fork α) :
    (Item.ofSince x).length = Item.sinceCount f fork := by
  unfold Item.ofSince Item.sinceCount
  split <;> rfl

/-- A field that appears at a fork reads back from its items. -/
theorem Item.readSince_append {f fork : Fork} (count : Nat) (x : Since f fork α)
    (rest : List Item) : Item.readSince count (Item.ofSince x ++ rest) = .ok (x, rest) := by
  unfold Item.readSince Item.ofSince
  by_cases h : f ≤ fork
  · simp only [h, ↓reduceDIte, List.singleton_append, Item.readField_cons, bind, Except.bind,
      pure, Except.pure]
  · simp only [h, ↓reduceDIte, List.nil_append, Except.ok.injEq]
    -- Before its fork, the field has only one value.
    exact Prod.ext (Since.eq_of_not_le h _ _) rfl

/-- A field that appears at a fork, read from some items, has its items first among them. -/
theorem Item.eq_of_readSince {f fork : Fork} {count : Nat} {items rest : List Item}
    {x : Since f fork α} (h : Item.readSince count items = .ok (x, rest)) :
    items = Item.ofSince x ++ rest := by
  unfold Item.readSince at h
  unfold Item.ofSince
  by_cases hf : f ≤ fork
  · simp only [hf, ↓reduceDIte] at h ⊢
    obtain ⟨⟨y, tail⟩, hy, h⟩ := bind_eq_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Item.eq_of_readField hy
  · simp only [hf, ↓reduceDIte, Except.ok.injEq] at h ⊢
    exact congrArg Prod.snd h

end Fields

end EthLib.Serialization.Rlp
