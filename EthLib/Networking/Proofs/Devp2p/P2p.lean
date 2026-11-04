module

public import EthLib.Networking.Devp2p.P2p
public import EthLib.Networking.Proofs.Rlpx.Handshake
public import EthLib.Networking.Proofs.Snappy.Block

/-!
# Proofs: the messages of the "p2p" capability

Each message reads back from its frame data, compressed or not.

The message IDs of the shared capabilities do not overlap, and none is below `0x10`.

Two errors with one code come from one constructor.
-/

@[expose] public section

namespace EthLib.Networking.Devp2p

open EthLib.Serialization.Rlp

/-! ## Messages -/

/-- A capability reads back from its RLP item. -/
theorem Capability.ofItem_toItem (c : Capability) : Codec.ofItem (Codec.toItem c) = .ok c := by
  simp [Codec.toItem, Codec.ofItem, Item.fields, Item.toItems, Item.toBytes, toScalar_scalar,
    bind, Except.bind, pure, Except.pure]

/-- A list of capabilities reads back from its RLP items. -/
theorem mapM_ofItem_capabilities (cs : List Capability) :
    (cs.map Codec.toItem).mapM (Codec.ofItem (α := Capability)) = .ok cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp [List.mapM_cons, Capability.ofItem_toItem, ih, bind, Except.bind, pure, Except.pure]

/-- Hello reads back from its RLP item. -/
theorem Hello.ofItem_toItem (h : Hello) : Codec.ofItem (Codec.toItem h) = .ok h := by
  have hcaps : Codec.ofItem (Codec.toItem h.capabilities) = .ok h.capabilities := by
    show (do (← Item.toItems (.list (h.capabilities.map Codec.toItem))).mapM Codec.ofItem) = _
    simp only [Item.toItems, bind, Except.bind, mapM_ofItem_capabilities]
  show (do
    match ← Rlpx.leadingFields 5 (.list [Codec.toItem h.protocolVersion, .bytes h.clientId,
      Codec.toItem h.capabilities, Codec.toItem h.listenPort, Codec.toItem h.nodeId]) with
    | [v, c, caps, p, n] =>
      return (⟨← Codec.ofItem v, ← Codec.ofItem c, ← Codec.ofItem caps, ← Codec.ofItem p,
        ← Codec.ofItem n⟩ : Hello)
    | items => throw (RlpError.wrongFieldCount 5 items.length)) = _
  have hcid : Codec.ofItem (Item.bytes h.clientId) = .ok h.clientId := rfl
  simp only [Rlpx.leadingFields, Item.toItems, bind, Except.bind, List.length_cons,
    List.length_nil, List.take, Nat.zero_add, Nat.reduceAdd, Nat.le_refl, ↓reduceIte, hcaps, hcid,
    LawfulCodec.ofItem_toItem, pure, Except.pure]

/-- Each message reads back from its ID and its RLP list. -/
theorem Message.ofItem_toItem (m : Message) : Message.ofItem m.id m.toItem = .ok m := by
  cases m with
  | hello h => simp [Message.ofItem, Message.id, Message.toItem, Hello.ofItem_toItem,
      Except.mapError, Functor.map, Except.map]
  | disconnect r =>
    cases r <;> simp [Message.ofItem, Message.id, Message.toItem, Codec.ofItem, Codec.toItem,
      toScalar_scalar, Except.mapError, Functor.map, Except.map]
  | ping => rfl
  | pong => rfl

/--
Each message reads back from its frame data, compressed or not.

The RLP list of the message must be at most 16 MiB, the most a reader decompresses.
-/
theorem decodeMessage_encodeMessage {snappy : Bool} {m : Message} {data frame : ByteArray}
    (hdata : encode m.toItem = .ok data) (hsize : data.size ≤ MAX_MESSAGE_SIZE)
    (h : encodeMessage snappy m = .ok frame) : decodeMessage snappy frame = .ok m := by
  unfold encodeMessage at h
  cases hid : encode (Item.scalar m.id) with
  | error e => simp [hid, Except.mapError, bind, Except.bind] at h
  | ok idE =>
  simp only [hid, hdata, Except.mapError, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at h
  subst h
  have hdec : decode data = .ok m.toItem := decode_encode _ _ hdata
  by_cases hc : (snappy && m.id != 0x00) = true
  · -- A compressed body: the reader checks the declared size, then decompresses.
    have hmax : data.size ≤ Snappy.maxUncompressedLength := by
      simp only [MAX_MESSAGE_SIZE, Snappy.maxUncompressedLength] at hsize ⊢; omega
    obtain ⟨hRest, hd⟩ := decodeItem_encode _ _ hid (Snappy.compressLiteral data).data.toList
    have hpre := Proofs.Snappy.Block.readPreamble_encode
      (if data.data.toList.isEmpty then [] else Snappy.literal data.data.toList)
      (n := data.data.toList.length) (by simpa using hmax)
    have hd' : ((decodeItem (idE ++ Snappy.compressLiteral data).data.toList).map
        fun r => (r.1, r.2.1)) =
          .ok (Item.scalar m.id, (Snappy.compressLiteral data).data.toList) := by
      generalize hL : (idE ++ Snappy.compressLiteral data).data.toList = L
      obtain rfl : L = idE.data.toList ++ (Snappy.compressLiteral data).data.toList := by
        rw [← hL, ByteArray.data_append, Array.toList_append]
      rw [hd]
      rfl
    have hframe : (if (snappy && m.id != 0x00) = true then Snappy.compressLiteral data else data) =
        Snappy.compressLiteral data := by simp [hc]
    rw [hframe]
    unfold decodeMessage
    simp only [hd', Except.mapError, bind, Except.bind, toScalar_scalar, hc, ↓reduceIte]
    have hlist : (Snappy.compressLiteral data).data.toList =
        Encoding.Varint.encodeAux data.data.toList.length Snappy.preambleMaxLength ++
          if data.data.toList.isEmpty = true then [] else Snappy.literal data.data.toList := rfl
    have hlen : ¬ MAX_MESSAGE_SIZE < data.data.toList.length := by
      simp only [Array.length_toList]; exact Nat.not_lt.mpr hsize
    rw [hlist, hpre]
    simp only [hlen, ↓reduceIte, ← hlist, Array.toArray_toList]
    rw [Proofs.Snappy.Block.decompress_compressLiteral hmax]
    simp only [hdec, Message.ofItem_toItem]
  · -- An uncompressed body is the RLP list itself.
    obtain ⟨hRest, hd⟩ := decodeItem_encode _ _ hid data.data.toList
    have hd' : ((decodeItem (idE ++ data).data.toList).map fun r => (r.1, r.2.1)) =
        .ok (Item.scalar m.id, data.data.toList) := by
      generalize hL : (idE ++ data).data.toList = L
      obtain rfl : L = idE.data.toList ++ data.data.toList := by
        rw [← hL, ByteArray.data_append, Array.toList_append]
      rw [hd]
      rfl
    have hframe : (if (snappy && m.id != 0x00) = true then Snappy.compressLiteral data else data) =
        data := by simp [hc]
    rw [hframe]
    unfold decodeMessage
    simp only [hd', Except.mapError, bind, Except.bind, toScalar_scalar, hc, Bool.false_eq_true,
      ↓reduceIte, pure, Except.pure, Array.toArray_toList, hdec, Message.ofItem_toItem]

/-! ## Message IDs of the shared capabilities -/

/-- Every offset is at least the first one. -/
theorem le_of_mem_messageOffsets (length : Capability → Nat) :
    ∀ (cs : List Capability) (start : Nat) (p : Capability × Nat),
      p ∈ messageOffsets length cs start → start ≤ p.2
  | [], _, _, h => by simp [messageOffsets] at h
  | c :: cs, start, p, h => by
    simp only [messageOffsets, List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.le_refl _
    · have := le_of_mem_messageOffsets length cs _ p h
      omega

/--
The ID blocks of the capabilities do not overlap.

Each capability's block `[offset, offset + length)` ends at or before the next one starts.
-/
theorem pairwise_messageOffsets (length : Capability → Nat) :
    ∀ (cs : List Capability) (start : Nat),
      (messageOffsets length cs start).Pairwise fun p q => p.2 + length p.1 ≤ q.2
  | [], _ => by simp [messageOffsets]
  | c :: cs, start => by
    simp only [messageOffsets, List.pairwise_cons]
    exact ⟨fun q hq => le_of_mem_messageOffsets length cs _ q hq,
      pairwise_messageOffsets length cs _⟩

/-- No shared capability takes a message ID of the "p2p" capability, below `0x10`. -/
theorem base_le_of_mem_negotiate {length : Capability → Nat} {ours theirs : List Capability}
    {p : Capability × Nat} (h : p ∈ negotiate length ours theirs) :
    BASE_PROTOCOL_LENGTH ≤ p.2 :=
  le_of_mem_messageOffsets length _ _ p h

/-- The ID blocks of the negotiated capabilities do not overlap. -/
theorem pairwise_negotiate (length : Capability → Nat) (ours theirs : List Capability) :
    (negotiate length ours theirs).Pairwise fun p q => p.2 + length p.1 ≤ q.2 :=
  pairwise_messageOffsets length _ _

/-- Every negotiated capability is in both lists, with the same name and version. -/
theorem mem_sharedCapabilities {ours theirs : List Capability} {c : Capability}
    (h : c ∈ sharedCapabilities ours theirs) : c ∈ ours ∧ c ∈ theirs := by
  simp only [sharedCapabilities, List.mem_mergeSort, List.mem_filter, List.mem_eraseDups] at h
  simpa using h.1

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem P2pError.code_injective (e₁ e₂ : P2pError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [P2pError.code] at h; exact absurd h (by decide))

end EthLib.Networking.Devp2p
