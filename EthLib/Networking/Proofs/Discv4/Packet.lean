module

public import EthLib.Networking.Discv4.Packet
public import EthLib.Networking.Proofs.Rlpx.Handshake
public import EthLib.Serialization.Proofs.Rlp.RoundTrip

/-!
# Proofs: the packets of discv4

Each packet reads back from its bytes, with the signer's public key as its sender.

A packet with its full field list reads back with any list items after it, as EIP-8 asks.

For Ping and Pong the full list ends with the sequence number of EIP-868.

Without that number, the items after the first extra item are ignored.

A packet reads only from its own type and its fields, followed by any items.

A Ping or a Pong reads without a sequence number only when no item follows its fields.

A packet whose hash does not match the bytes after it is rejected.

Every packet that the reader accepts has at most 1280 bytes.

Two errors with one code come from one constructor.
-/

@[expose] public section

namespace EthLib.Networking.Discv4

open EthLib.Cryptography
open EthLib.Cryptography.Secp256k1
open EthLib.Cryptography.Secp256k1.Point
open EthLib.Base (bind_ok_iff)
open EthLib.Serialization.Rlp

/-! ## Packet data -/

instance : LawfulCodec Endpoint where
  ofItem_toItem e := by
    show Endpoint.ofItem (Endpoint.toItem e) = _
    simp only [Endpoint.ofItem, Endpoint.toItem, Item.fields, Item.toItems, List.length_cons,
      List.length_nil, ↓reduceIte, LawfulCodec.ofItem_toItem, bind, Except.bind, pure,
      Except.pure]
  toItem_of_ofItem {item e} h := by
    change Endpoint.ofItem item = .ok e at h
    unfold Endpoint.ofItem at h
    obtain ⟨items, hf, hrest⟩ := bind_ok_iff.mp h
    obtain ⟨rfl, hlen⟩ := Item.fields_eq_ok.mp hf
    rcases items with _ | ⟨ip, _ | ⟨u, _ | ⟨t, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at hlen
    · dsimp only at hrest
      obtain ⟨a, ha, h⟩ := bind_ok_iff.mp hrest
      obtain ⟨b, hb, h⟩ := bind_ok_iff.mp h
      obtain ⟨c, hc, h⟩ := bind_ok_iff.mp h
      cases h
      show Endpoint.toItem _ = _
      simp only [Endpoint.toItem, LawfulCodec.toItem_of_ofItem ha,
        LawfulCodec.toItem_of_ofItem hb, LawfulCodec.toItem_of_ofItem hc]

instance : LawfulCodec Node where
  ofItem_toItem n := by
    show Node.ofItem (Node.toItem n) = _
    simp only [Node.ofItem, Node.toItem, Item.fields, Item.toItems, List.length_cons,
      List.length_nil, ↓reduceIte, LawfulCodec.ofItem_toItem, bind, Except.bind, pure,
      Except.pure]
  toItem_of_ofItem {item n} h := by
    change Node.ofItem item = .ok n at h
    unfold Node.ofItem at h
    obtain ⟨items, hf, hrest⟩ := bind_ok_iff.mp h
    obtain ⟨rfl, hlen⟩ := Item.fields_eq_ok.mp hf
    rcases items with _ | ⟨ip, _ | ⟨u, _ | ⟨t, _ | ⟨id, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at hlen
    · dsimp only at hrest
      obtain ⟨a, ha, h⟩ := bind_ok_iff.mp hrest
      obtain ⟨b, hb, h⟩ := bind_ok_iff.mp h
      obtain ⟨c, hc, h⟩ := bind_ok_iff.mp h
      obtain ⟨d, hd, h⟩ := bind_ok_iff.mp h
      cases h
      show Node.toItem _ = _
      simp only [Node.toItem, LawfulCodec.toItem_of_ofItem ha,
        LawfulCodec.toItem_of_ofItem hb, LawfulCodec.toItem_of_ofItem hc,
        LawfulCodec.toItem_of_ofItem hd]

/-- The sequence number reads back from the items after the fixed fields. -/
theorem Packet.readEnrSeq_enrSeqItems (s : Option UInt64) :
    Packet.readEnrSeq (Packet.enrSeqItems s) = .ok s := by
  cases s <;> simp [Packet.readEnrSeq, Packet.enrSeqItems, LawfulCodec.ofItem_toItem,
    Functor.map, Except.map]

/-- Each packet reads back from its type and the items of its data. -/
theorem Packet.ofItems_fields (p : Packet) : Packet.ofItems p.type p.fields = .ok p := by
  cases p <;>
    simp [Packet.ofItems, Packet.type, Packet.fields, LawfulCodec.ofItem_toItem,
      Packet.readEnrSeq_enrSeqItems, Except.mapError, bind, Except.bind, pure, Except.pure]

/-! ## Further list items -/

/--
A packet with its full field list reads back with any items after it, as EIP-8 asks.

For Ping and Pong the full list ends with the sequence number of EIP-868.
-/
theorem Packet.ofItems_fields_append (p : Packet) (extra : List Item)
    (hping : ∀ v f t e, p ≠ .ping v f t e none) (hpong : ∀ t h e, p ≠ .pong t h e none) :
    Packet.ofItems p.type (p.fields ++ extra) = .ok p := by
  cases p with
  | ping v f t e s =>
    cases s with
    | none => exact absurd rfl (hping v f t e)
    | some s =>
      simp [Packet.ofItems, Packet.type, Packet.fields, Packet.enrSeqItems, Packet.readEnrSeq,
        LawfulCodec.ofItem_toItem, Except.mapError, bind, Except.bind, pure, Except.pure,
        Functor.map, Except.map]
  | pong t h e s =>
    cases s with
    | none => exact absurd rfl (hpong t h e)
    | some s =>
      simp [Packet.ofItems, Packet.type, Packet.fields, Packet.enrSeqItems, Packet.readEnrSeq,
        LawfulCodec.ofItem_toItem, Except.mapError, bind, Except.bind, pure, Except.pure,
        Functor.map, Except.map]
  | _ =>
    simp [Packet.ofItems, Packet.type, Packet.fields, LawfulCodec.ofItem_toItem,
      Except.mapError, bind, Except.bind, pure, Except.pure]

/--
Ping without a sequence number reads the same whatever follows the first item after its fields.

That item is where EIP-868 puts the number, and EIP-8 asks to ignore the rest.
-/
theorem Packet.ofItems_ping_append (v : Nat) (f t : Endpoint) (e : Nat) (x : Item)
    (rest : List Item) :
    Packet.ofItems 0x01 ((ping v f t e none).fields ++ x :: rest) =
      Packet.ofItems 0x01 ((ping v f t e none).fields ++ [x]) := by
  simp [Packet.ofItems, Packet.fields, Packet.enrSeqItems, Packet.readEnrSeq]

/--
Pong without a sequence number reads the same whatever follows the first item after its fields.

That item is where EIP-868 puts the number, and EIP-8 asks to ignore the rest.
-/
theorem Packet.ofItems_pong_append (t : Endpoint) (h : Vector UInt8 32) (e : Nat) (x : Item)
    (rest : List Item) :
    Packet.ofItems 0x02 ((pong t h e none).fields ++ x :: rest) =
      Packet.ofItems 0x02 ((pong t h e none).fields ++ [x]) := by
  simp [Packet.ofItems, Packet.fields, Packet.enrSeqItems, Packet.readEnrSeq]

/-! ## The items that the reader accepts -/

/-- The items after the fixed fields give a sequence number exactly when it is the first of them.

They give none exactly when there are no such items. -/
private theorem Packet.readEnrSeq_eq_ok_iff {rest : List Item} {s : Option UInt64} :
    Packet.readEnrSeq rest = .ok s ↔
      ∃ extra, rest = Packet.enrSeqItems s ++ extra ∧ (s = none → extra = []) := by
  cases rest with
  | nil => cases s <;> simp [Packet.readEnrSeq, Packet.enrSeqItems]
  | cons x rest =>
    cases s with
    | none => simp [Packet.readEnrSeq, Packet.enrSeqItems, EthLib.Base.map_ok_iff]
    | some n =>
      rw [Packet.readEnrSeq, EthLib.Base.map_ok_iff]
      simp [Packet.enrSeqItems, Codec.ofItem_eq_ok_iff]
      exact eq_comm

/--
The reader takes a packet exactly when the type is its type and the items start with its fields.

Any items may follow the fields, as EIP-8 asks.

A Ping or a Pong reads without the sequence number of EIP-868 only when no item follows its fields.
-/
theorem Packet.ofItems_eq_ok_iff {type : UInt8} {items : List Item} {p : Packet} :
    Packet.ofItems type items = .ok p ↔
      type = p.type ∧ ∃ extra, items = p.fields ++ extra ∧
        (∀ v f t e, p = .ping v f t e none → extra = []) ∧
        (∀ t h e, p = .pong t h e none → extra = []) := by
  constructor
  · intro h
    unfold Packet.ofItems at h
    split_ifs at h with h1 h2 h3 h4 h5 h6
    · subst h1
      match items, h with
      | v :: f :: t :: e :: rest, h =>
        simp only [EthLib.Base.mapError_ok_iff, bind_ok_iff, pure, Except.pure,
          Except.ok.injEq] at h
        obtain ⟨v', hv, f', hf, t', ht, e', he, s, hs, rfl⟩ := h
        obtain ⟨extra, rfl, hnone⟩ := Packet.readEnrSeq_eq_ok_iff.mp hs
        refine ⟨rfl, extra, ?_, ?_, ?_⟩
        · simp [Packet.fields, (Codec.ofItem_eq_ok_iff.mp hv).symm,
            (Codec.ofItem_eq_ok_iff.mp hf).symm, (Codec.ofItem_eq_ok_iff.mp ht).symm,
            (Codec.ofItem_eq_ok_iff.mp he).symm]
        · intro _ _ _ _ hp
          cases hp
          exact hnone rfl
        · intro _ _ _ hp
          cases hp
    · subst h2
      match items, h with
      | t :: hh :: e :: rest, h =>
        simp only [EthLib.Base.mapError_ok_iff, bind_ok_iff, pure, Except.pure,
          Except.ok.injEq] at h
        obtain ⟨t', ht, h', hh, e', he, s, hs, rfl⟩ := h
        obtain ⟨extra, rfl, hnone⟩ := Packet.readEnrSeq_eq_ok_iff.mp hs
        refine ⟨rfl, extra, ?_, ?_, ?_⟩
        · simp [Packet.fields, (Codec.ofItem_eq_ok_iff.mp ht).symm,
            (Codec.ofItem_eq_ok_iff.mp hh).symm, (Codec.ofItem_eq_ok_iff.mp he).symm]
        · intro _ _ _ _ hp
          cases hp
        · intro _ _ _ hp
          cases hp
          exact hnone rfl
    · subst h3
      match items, h with
      | t :: e :: extra, h =>
        simp only [EthLib.Base.mapError_ok_iff, bind_ok_iff, pure, Except.pure,
          Except.ok.injEq] at h
        obtain ⟨t', ht, e', he, rfl⟩ := h
        refine ⟨rfl, extra, ?_, by simp, by simp⟩
        simp [Packet.fields, (Codec.ofItem_eq_ok_iff.mp ht).symm,
          (Codec.ofItem_eq_ok_iff.mp he).symm]
    · subst h4
      match items, h with
      | ns :: e :: extra, h =>
        simp only [EthLib.Base.mapError_ok_iff, bind_ok_iff, pure, Except.pure,
          Except.ok.injEq] at h
        obtain ⟨ns', hns, e', he, rfl⟩ := h
        refine ⟨rfl, extra, ?_, by simp, by simp⟩
        simp [Packet.fields, (Codec.ofItem_eq_ok_iff.mp hns).symm,
          (Codec.ofItem_eq_ok_iff.mp he).symm]
    · subst h5
      match items, h with
      | e :: extra, h =>
        simp only [EthLib.Base.mapError_ok_iff, bind_ok_iff, pure, Except.pure,
          Except.ok.injEq] at h
        obtain ⟨e', he, rfl⟩ := h
        refine ⟨rfl, extra, ?_, by simp, by simp⟩
        simp [Packet.fields, (Codec.ofItem_eq_ok_iff.mp he).symm]
    · subst h6
      match items, h with
      | hh :: r :: extra, h =>
        simp only [EthLib.Base.mapError_ok_iff, bind_ok_iff, pure, Except.pure,
          Except.ok.injEq] at h
        obtain ⟨h', hh, rfl⟩ := h
        refine ⟨rfl, extra, ?_, by simp, by simp⟩
        simp [Packet.fields, (Codec.ofItem_eq_ok_iff.mp hh).symm]
  · rintro ⟨rfl, extra, rfl, hping, hpong⟩
    by_cases hextra : extra = []
    · subst hextra
      simpa using Packet.ofItems_fields p
    · exact Packet.ofItems_fields_append p extra (fun v f t e hp => hextra (hping v f t e hp))
        (fun t h e hp => hextra (hpong t h e hp))

/-! ## Packets -/

/-- Every packet that the reader accepts has at most 1280 bytes. -/
theorem size_le_of_decode {packet : ByteArray} {r : Received} (h : decode packet = .ok r) :
    packet.size ≤ MAX_PACKET_SIZE := by
  apply Nat.le_of_not_lt
  intro hc
  unfold decode at h
  simp only [Array.length_toList, ByteArray.size] at hc h
  rw [ite_eq_left hc] at h
  exact nomatch h

/-- The hash that the body reader returns is the hash it was given. -/
theorem hash_of_readBody {hash : Vector UInt8 32} {sig : Vector UInt8 65} {type : UInt8}
    {data : List UInt8} {r : Received} (h : readBody hash sig type data = .ok r) :
    r.hash = hash := by
  unfold readBody at h
  simp only [bind, Except.bind] at h
  split at h
  · exact nomatch h
  split at h
  · exact nomatch h
  split at h
  · exact nomatch h
  split at h
  · exact nomatch h
  cases h
  rfl

/--
The hash of a packet that the reader accepts is its first 32 bytes.

So the hash that a Pong or an ENRResponse echoes is the start of the request as it was sent.
-/
theorem hash_of_decode {packet : ByteArray} {r : Received} (h : decode packet = .ok r) :
    r.hash.toList = packet.data.toList.take 32 := by
  unfold decode at h
  dsimp only at h
  split at h
  · exact nomatch h
  split at h
  · exact nomatch h
  split at h
  · rename_i hhash
    rw [hash_of_readBody h]
    exact hhash.symm
  · exact nomatch h

/--
A packet whose first 32 bytes are not the Keccak-256 hash of the bytes after them is rejected.

The packet must have the size of a packet, so that the hash is the first check that fails.
-/
theorem decode_hashMismatch {packet : ByteArray} (hsize : packet.size ≤ MAX_PACKET_SIZE)
    (hshort : HEADER_SIZE < packet.size)
    (hhash : packet.data.toList.take 32 ≠ (keccak (packet.data.toList.drop 32)).toList) :
    decode packet = .error .hashMismatch := by
  have hlen : packet.data.toList.length = packet.size := Array.length_toList
  unfold decode
  rw [ite_eq_right (by omega)]
  split
  · rename_i hdrop
    have := congrArg List.length hdrop
    simp only [List.length_drop, List.length_nil] at this
    omega
  · rw [ite_eq_right hhash]

/-- The 65 bytes after the hash are the signature. -/
theorem signatureOf_append {hash : List UInt8} (hhash : hash.length = 32) (sig : Vector UInt8 65)
    (rest : List UInt8) : signatureOf (hash ++ (sig.toList ++ rest)) = sig := by
  ext i hi
  simp only [signatureOf, Vector.getElem_ofFn, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), hhash, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by simpa using hi), List.getElem?_eq_getElem (by simpa using hi)]
  simp

/--
Each packet reads back from its bytes.

The sender is the public key of the private key that signed it.
-/
theorem decode_encode {key : Fn} {p : Packet} {packet : ByteArray} (h : encode key p = .ok packet) :
    decode packet = .ok ⟨p, mul key generator, keccak (packet.data.toList.drop 32)⟩ := by
  unfold encode at h
  cases hdata : Serialization.Rlp.encode (.list p.fields) with
  | error e => simp [hdata, Except.mapError, bind, Except.bind] at h
  | ok data =>
  cases hsig : Ecdsa.sign key (keccak (p.type :: data.data.toList)) with
  | error e => simp [hdata, hsig, Except.mapError, bind, Except.bind] at h
  | ok sig =>
  simp only [hdata, hsig, Except.mapError, bind, Except.bind] at h
  split at h
  · exact nomatch h
  rename_i hsize
  cases h
  have hrec := Rlpx.recoverSigner_signatureBytes hsig
  obtain ⟨w, hitem⟩ : ∃ w,
      decodeItem ⟨data.data.toList.toArray⟩ 0 data.data.toList.length
        (by
          change data.data.toList.length ≤ data.data.toList.toArray.size
          rw [List.size_toArray]) =
      .ok (.list p.fields, w) := by
    obtain ⟨hw, h⟩ := decodeItem_encode _ _ hdata (input := data) (pos := 0) (rest := [])
      (Nat.le_refl _) (by simp)
    simp only [Array.toArray_toList, Array.length_toList, ByteArray.size_data]
    exact ⟨_, h⟩
  -- Name the hash and the signature, so that no step computes them.
  generalize Rlpx.signatureBytes sig = S at hrec hsize ⊢
  generalize hK : keccak (S.toList ++ p.type :: data.data.toList) = K at hsize ⊢
  have hk : K.toList.length = 32 := by simp
  have hs : S.toList.length = 65 := by simp
  have hd32 : (K.toList ++ (S.toList ++ p.type :: data.data.toList)).drop 32 =
      S.toList ++ p.type :: data.data.toList := List.drop_left' hk
  have ht32 : (K.toList ++ (S.toList ++ p.type :: data.data.toList)).take 32 = K.toList :=
    List.take_left' hk
  have hd97 : (K.toList ++ (S.toList ++ p.type :: data.data.toList)).drop HEADER_SIZE =
      p.type :: data.data.toList := by
    rw [← List.append_assoc]
    exact List.drop_left' (by simp [hk, hs, HEADER_SIZE])
  unfold decode readBody
  dsimp only
  rw [List.toList_toArray, hd32, ht32, hK, ite_eq_right hsize, hd97]
  dsimp only
  rw [ite_eq_left rfl, signatureOf_append hk]
  simp only [hrec, hitem, Except.mapError, bind, Except.bind, Item.toItems,
    Packet.ofItems_fields, pure, Except.pure]

/-! ## Records -/

/-- A record is signed by a sender exactly when it is a valid "v4" record with the sender's key. -/
theorem recordSignedBy_iff (sender : Point) (record : Item) :
    recordSignedBy sender record = true ↔
      ∃ bytes r, Serialization.Rlp.encode record = .ok bytes ∧ Enr.decode bytes = .ok r ∧
        r.publicKeyV4 = .ok sender ∧ Enr.verifyV4 r = true := by
  unfold recordSignedBy
  constructor
  · intro h
    split at h
    · exact nomatch h
    rename_i bytes hb
    split at h
    · exact nomatch h
    rename_i r hr
    split at h
    · exact nomatch h
    rename_i key hkey
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨bytes, r, hb, hr, h.2 ▸ hkey, h.1⟩
  · rintro ⟨bytes, r, hb, hr, hkey, hv⟩
    simp [hb, hr, hkey, hv]

/-! ## Error codes -/

/-- Two errors with the same code come from the same constructor. -/
theorem Discv4Error.code_injective (e₁ e₂ : Discv4Error) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [Discv4Error.code] at h; exact absurd h (by decide))

end EthLib.Networking.Discv4
