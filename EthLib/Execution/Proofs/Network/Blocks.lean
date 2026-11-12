module

public import EthLib.Execution.Network.Blocks
public import EthLib.Execution.Proofs.Blocks.Header
public import EthLib.Serialization.Proofs.Rlp.Codec
public import EthLib.Serialization.Proofs.Rlp.Item

/-!
# Proofs: the block exchange

Each request reads back from its RLP item.

Headers that pass the check of a request are at most as many as asked.

Each one is `skip + 1` blocks after the one before it, or before it when the request is reversed.

An answer passes the check exactly when three conditions hold.

It is not longer than asked, and its first header, if any, is the start block.

Each header follows the one before it.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Serialization.Rlp

instance : LawfulCodec BlockId where
  ofItem_toItem b := by
    show BlockId.ofItem (BlockId.toItem b) = _
    cases b with
    | number n =>
      have hn : (Codec.toItem n : Item) = .bytes (bigEndian n.toNat) := rfl
      -- A number below 2^64 has at most 8 bytes, so it never reads as a 32-byte hash.
      have hsz : (bigEndian n.toNat).size ≠ 32 := by
        have := bigEndian_size_le n.toNat 8 (by simpa using n.toNat_lt)
        omega
      simp only [BlockId.toItem, hn, BlockId.ofItem, hsz, ↓reduceIte]
      rw [← hn, LawfulCodec.ofItem_toItem]
      rfl
    | hash h =>
      have hh : (Codec.toItem h : Item) = .bytes ⟨h.toArray⟩ := rfl
      have hs : (⟨h.toArray⟩ : ByteArray).size = 32 := by simp [ByteArray.size]
      simp only [BlockId.toItem, hh, BlockId.ofItem, hs, ↓reduceIte]
      rw [← hh, LawfulCodec.ofItem_toItem]
      rfl
  toItem_of_ofItem {item b} h := by
    change BlockId.ofItem item = .ok b at h
    cases item with
    | list _ => cases h
    | bytes d =>
      simp only [BlockId.ofItem] at h
      split at h
      · cases hx : (Codec.ofItem (.bytes d) : Except RlpError Hash32) with
        | error e => simp [hx, Functor.map, Except.map] at h
        | ok x =>
          simp only [hx, Functor.map, Except.map, Except.ok.injEq] at h
          subst h
          show Codec.toItem x = _
          exact LawfulCodec.toItem_of_ofItem hx
      · cases hx : (Codec.ofItem (.bytes d) : Except RlpError UInt64) with
        | error e => simp [hx, Functor.map, Except.map] at h
        | ok x =>
          simp only [hx, Functor.map, Except.map, Except.ok.injEq] at h
          subst h
          show Codec.toItem x = _
          exact LawfulCodec.toItem_of_ofItem hx

instance : LawfulCodec HeaderRequest where
  ofItem_toItem r := by
    show HeaderRequest.ofItem (HeaderRequest.toItem r) = _
    simp only [HeaderRequest.ofItem, HeaderRequest.toItem, Item.fields, Item.toItems,
      List.length_cons, List.length_nil, ↓reduceIte, Item.field_toItem, bind, Except.bind, pure,
      Except.pure]
  toItem_of_ofItem {item r} h := by
    change HeaderRequest.ofItem item = .ok r at h
    obtain ⟨items, rfl, hlen, hrest⟩ := Item.fields_bind_eq_ok.mp h
    rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at hlen
    obtain ⟨w, rfl, h1⟩ := Item.field_bind_eq_ok.mp hrest
    obtain ⟨x, rfl, h2⟩ := Item.field_bind_eq_ok.mp h1
    obtain ⟨y, rfl, h3⟩ := Item.field_bind_eq_ok.mp h2
    obtain ⟨z, rfl, h4⟩ := Item.field_bind_eq_ok.mp h3
    cases h4
    rfl

instance : LawfulCodec BlockAnnouncement where
  ofItem_toItem a := by
    show BlockAnnouncement.ofItem (BlockAnnouncement.toItem a) = _
    simp only [BlockAnnouncement.ofItem, BlockAnnouncement.toItem, Item.fields, Item.toItems,
      List.length_cons, List.length_nil, ↓reduceIte, Item.field_toItem, bind, Except.bind, pure,
      Except.pure]
  toItem_of_ofItem {item a} h := by
    change BlockAnnouncement.ofItem item = .ok a at h
    obtain ⟨items, rfl, hlen, hrest⟩ := Item.fields_bind_eq_ok.mp h
    rcases items with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;> simp at hlen
    obtain ⟨u, rfl, h1⟩ := Item.field_bind_eq_ok.mp hrest
    obtain ⟨v, rfl, h2⟩ := Item.field_bind_eq_ok.mp h1
    cases h2
    rfl

/-! ## The headers that answer a request -/

/-- Two errors with one code come from one constructor. -/
theorem HeadersError.code_injective (e₁ e₂ : HeadersError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [HeadersError.code] at h; exact absurd h (by decide))

/-- A header that follows another has the next number of the request. -/
theorem numbers_of_followsIn {r : HeaderRequest} {a b : Item} (h : followsIn r a b = .ok ()) :
    ∃ na nb, headerNumber a = .ok na ∧ headerNumber b = .ok nb ∧ r.next na = some nb := by
  unfold followsIn at h
  cases ha : headerNumber a with
  | error e => simp [ha, Except.mapError, bind, Except.bind] at h
  | ok na =>
    cases hb : headerNumber b with
    | error e => simp [ha, hb, Except.mapError, bind, Except.bind] at h
    | ok nb =>
      refine ⟨na, nb, rfl, rfl, ?_⟩
      by_cases hne : r.next na = some nb
      · exact hne
      · simp [ha, hb, Except.mapError, bind, Except.bind, hne, throw, throwThe,
          MonadExceptOf.throw] at h

/-- Each header of a list that passes `followAll` follows the one before it. -/
theorem followsIn_of_followAll {r : HeaderRequest} :
    ∀ {l : List Item}, followAll r l = .ok () →
      ∀ (i : Nat) (hi : i + 1 < l.length), followsIn r l[i] l[i + 1] = .ok ()
  | [], _, i, hi => by simp at hi
  | [_], _, i, hi => by simp at hi
  | a :: b :: rest, h, i, hi => by
    unfold followAll at h
    cases hab : followsIn r a b with
    | error e => simp [hab, bind, Except.bind] at h
    | ok u =>
      simp only [hab, bind, Except.bind] at h
      cases i with
      | zero => simpa using hab
      | succ i =>
        have := followsIn_of_followAll h i (by simpa using hi)
        simpa using this

/-- A list passes `followAll` exactly when each header follows the one before it. -/
theorem followAll_eq_ok_iff {r : HeaderRequest} :
    ∀ {l : List Item}, followAll r l = .ok () ↔
      ∀ (i : Nat) (hi : i + 1 < l.length), followsIn r l[i] l[i + 1] = .ok ()
  | [] => by simp [followAll, pure, Except.pure]
  | [_] => by simp [followAll, pure, Except.pure]
  | a :: b :: rest => by
    refine ⟨followsIn_of_followAll, fun h => ?_⟩
    have hab := h 0 (by simp)
    have hrest : followAll r (b :: rest) = .ok () :=
      (followAll_eq_ok_iff (l := b :: rest)).mpr fun i hi => by
        have := h (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
        simp only [List.getElem_cons_succ] at this ⊢
        exact this
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hab
    simp [followAll, hab, hrest, bind, Except.bind]

/-- An answer that passes the check holds at most as many headers as asked. -/
theorem length_le_of_checkHeaders {r : HeaderRequest} {headers : List Item}
    (h : checkHeaders r headers = .ok ()) : headers.length ≤ r.limit := by
  unfold checkHeaders at h
  by_cases hlt : r.limit < headers.length
  · simp [hlt, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · omega

/-- An answer that passes the check has each header follow the one before it. -/
theorem followAll_of_checkHeaders {r : HeaderRequest} {headers : List Item}
    (h : checkHeaders r headers = .ok ()) : followAll r headers = .ok () := by
  unfold checkHeaders at h
  by_cases hlt : r.limit < headers.length
  · simp [hlt, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp only [hlt, ↓reduceIte] at h
    cases headers with
    | nil => rfl
    | cons first rest =>
      cases hs : isStart r.start first with
      | error e => simp [hs, bind, Except.bind] at h
      | ok b =>
        cases b
        · simp [hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
        · simpa [hs, bind, Except.bind] using h

/--
In an answer that passes the check, each header is `skip + 1` blocks after the one before it.

When the answer is reversed, it is `skip + 1` blocks before it.
-/
theorem numbers_of_checkHeaders {r : HeaderRequest} {headers : List Item}
    (h : checkHeaders r headers = .ok ()) (i : Nat) (hi : i + 1 < headers.length) :
    ∃ na nb, headerNumber headers[i] = .ok na ∧ headerNumber headers[i + 1] = .ok nb ∧
      r.next na = some nb :=
  numbers_of_followsIn (followsIn_of_followAll (followAll_of_checkHeaders h) i hi)

/-- An answer passes the check of a request exactly when three conditions hold.

It holds at most as many headers as asked, and its first header, if any, is the start block.

Each header follows the one before it.

The conditions do not ask for as many headers as asked, since a peer may send fewer.

They read only the number, the hash and the parent hash of each header, not whether it is valid. -/
theorem checkHeaders_eq_ok_iff {r : HeaderRequest} {headers : List Item} :
    checkHeaders r headers = .ok () ↔
      headers.length ≤ r.limit ∧ (∀ first ∈ headers.head?, isStart r.start first = .ok true) ∧
        followAll r headers = .ok () := by
  constructor
  · intro h
    refine ⟨length_le_of_checkHeaders h, fun first hfirst => ?_, followAll_of_checkHeaders h⟩
    unfold checkHeaders at h
    by_cases hlt : r.limit < headers.length
    · simp [hlt, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    · simp only [hlt, ↓reduceIte] at h
      cases headers with
      | nil => simp at hfirst
      | cons f rest =>
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hfirst
        subst hfirst
        cases hs : isStart r.start f with
        | error e => simp [hs, bind, Except.bind] at h
        | ok b =>
          cases b
          · simp [hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
          · rfl
  · rintro ⟨hle, hstart, hfollow⟩
    unfold checkHeaders
    simp only [Nat.not_lt.mpr hle, ↓reduceIte]
    cases headers with
    | nil => simp [hfollow]
    | cons f rest =>
      have hs := hstart f (by simp)
      simp [hs, hfollow, bind, Except.bind]

/-- The empty answer passes the check of every request. -/
theorem checkHeaders_nil (r : HeaderRequest) : checkHeaders r [] = .ok () := by
  simp [checkHeaders, followAll, pure, Except.pure]

/-- The number of the header of an encoded header is its number. -/
theorem headerNumber_toItem {fork : Fork} (h : Blocks.Header fork) :
    headerNumber (Codec.toItem h) = .ok h.number := by
  rw [Blocks.Header.toItem_eq]
  simp [headerNumber, HEADER_NUMBER_INDEX, Item.toItems, bind, Except.bind]
  exact LawfulCodec.ofItem_toItem _

end EthLib.Execution.Network
