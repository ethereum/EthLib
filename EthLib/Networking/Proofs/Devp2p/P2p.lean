module

public import EthLib.Base.Proofs.List
public import EthLib.Networking.Devp2p.P2p
public import EthLib.Networking.Proofs.Rlpx.Handshake
public import EthLib.Networking.Proofs.Snappy.Compress

/-!
# Proofs: the messages of the "p2p" capability

Each message reads back from its frame data, compressed or not.

A reader of Hello ignores the list items after the five fields it knows, as EIP-8 asks.

With Snappy, a reader rejects a message other than Hello whose preamble declares more than 16 MiB.

A message other than Hello that such a reader accepts decompresses to at most 16 MiB.

Two peers use Snappy exactly when both announce version 5 or more.

The message IDs of the shared capabilities do not overlap, and none is below `0x10`.

The shared capabilities, in alphabetic order, take adjacent blocks of message IDs from `0x10` on.

So the IDs they use are exactly those from `0x10` up to `0x10` plus the number they need in all.

Of the versions of one name that both peers list, only the highest is negotiated.

Both peers negotiate the same capabilities and message IDs, whichever of them asks.

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

/-- Hello reads the same from five or more items, whatever items follow them, as EIP-8 asks. -/
theorem Hello.ofItem_append {fields : List Item} (extra : List Item) (h : 5 ≤ fields.length) :
    (Codec.ofItem (.list (fields ++ extra)) : Except RlpError Hello) =
      Codec.ofItem (.list fields) := by
  simp only [Codec.ofItem, Rlpx.leadingFields_append extra h]

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

/-- The frame data starts with the message ID, and the reader stops right after it. -/
private theorem decodeItem_id_append {id : Nat} {idE : ByteArray}
    (hid : encode (Item.scalar id) = .ok idE) (rest : ByteArray) :
    ((decodeItem (idE ++ rest) 0 (idE ++ rest).size).map fun r => (r.1, r.2.1)) =
      .ok (Item.scalar id, idE.size) := by
  obtain ⟨_, hd⟩ := decodeItem_encode _ _ hid (input := idE ++ rest) (pos := 0)
    (rest := rest.data.toList) (Nat.le_refl _)
    (by rw [ByteArray.extract_zero_size, ByteArray.toList_data_append])
  rw [hd]
  simp [Except.map]

/-- The bytes after the message ID are the rest of the frame data. -/
private theorem extract_id_append (idE rest : ByteArray) :
    (idE ++ rest).extract idE.size (idE ++ rest).size = rest :=
  ByteArray.extract_append_eq_right rfl ByteArray.size_append

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
    have hpre := Proofs.Snappy.Compress.readPreamble_compress hmax
    have hd' := decodeItem_id_append hid (Snappy.compress data)
    have hframe : (if (snappy && m.id != 0x00) = true then Snappy.compress data else data) =
        Snappy.compress data := by simp [hc]
    rw [hframe]
    unfold decodeMessage
    simp only [hd', extract_id_append, Except.mapError, bind, Except.bind, toScalar_scalar, hc,
      ↓reduceIte]
    have hlen : ¬ MAX_MESSAGE_SIZE < data.size := Nat.not_lt.mpr hsize
    rw [hpre]
    simp only [hlen, ↓reduceIte]
    rw [Proofs.Snappy.Compress.decompress_compress hmax]
    simp only [hdec, Message.ofItem_toItem]
  · -- An uncompressed body is the RLP list itself.
    have hd' := decodeItem_id_append hid data
    have hframe : (if (snappy && m.id != 0x00) = true then Snappy.compress data else data) =
        data := by simp [hc]
    rw [hframe]
    unfold decodeMessage
    simp only [hd', extract_id_append, Except.mapError, bind, Except.bind, toScalar_scalar, hc,
      Bool.false_eq_true, ↓reduceIte, pure, Except.pure, hdec, Message.ofItem_toItem]

/--
With Snappy, a message other than Hello whose preamble declares more than 16 MiB is rejected.

The rejection does not depend on the bytes after the preamble.
-/
theorem decodeMessage_tooLarge {id size : Nat} {idE rest : ByteArray} {tail : List UInt8}
    (hid : encode (Item.scalar id) = .ok idE) (hne : id ≠ 0x00)
    (hpre : Snappy.readPreamble rest.data.toList = .ok (size, tail))
    (hsize : MAX_MESSAGE_SIZE < size) :
    decodeMessage true (idE ++ rest) = .error (.tooLarge size) := by
  have hc : (true && id != 0x00) = true := by simpa using hne
  unfold decodeMessage
  simp only [decodeItem_id_append hid, extract_id_append, Except.mapError, bind, Except.bind,
    toScalar_scalar, hc, ↓reduceIte, hpre, hsize]
  rfl

/--
With Snappy, a message other than Hello that a reader accepts decompresses to at most 16 MiB.
-/
theorem size_le_of_decodeMessage {id : Nat} {idE rest : ByteArray} {m : Message}
    (hid : encode (Item.scalar id) = .ok idE) (hne : id ≠ 0x00)
    (h : decodeMessage true (idE ++ rest) = .ok m) :
    ∃ data, Snappy.decompress rest = .ok data ∧ data.size ≤ MAX_MESSAGE_SIZE := by
  have hc : (true && id != 0x00) = true := by simpa using hne
  unfold decodeMessage at h
  simp only [decodeItem_id_append hid, extract_id_append, Except.mapError, bind, Except.bind,
    toScalar_scalar, hc, ↓reduceIte] at h
  cases hpre : Snappy.readPreamble rest.data.toList with
  | error e => simp [hpre] at h
  | ok p =>
  by_cases hsize : MAX_MESSAGE_SIZE < p.1
  · simp [hpre, hsize] at h
  cases hd : Snappy.decompress rest with
  | error e => simp [hpre, hsize, hd] at h
  | ok data =>
  -- The preamble that the reader checked is the length that the block decompresses to.
  obtain ⟨_, hdecl⟩ := Proofs.Snappy.Block.decompress_size_eq_declared hd
  rw [Proofs.Snappy.Block.toList_eq_data_toList, hpre] at hdecl
  have hp : p.1 = data.size := congrArg Prod.fst (Except.ok.inj hdecl)
  exact ⟨data, rfl, hp ▸ Nat.not_lt.mp hsize⟩

/-! ## Snappy -/

/-- Two peers use Snappy exactly when both announce version 5 or more. -/
theorem snappyEnabled_iff {ours theirs : Nat} :
    snappyEnabled ours theirs = true ↔ 5 ≤ ours ∧ 5 ≤ theirs := by
  unfold snappyEnabled SNAPPY_VERSION
  simp only [Bool.and_eq_true, decide_eq_true_eq]

/-- Both peers reach the same answer on Snappy, whichever of them asks. -/
theorem snappyEnabled_comm (ours theirs : Nat) :
    snappyEnabled ours theirs = snappyEnabled theirs ours := by
  simp only [snappyEnabled, Bool.and_comm]

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

/--
The first message ID of each capability is the start plus the IDs of the capabilities before it.

So the blocks follow each other with no gap, in the order of the list.
-/
theorem messageOffsets_eq (length : Capability → Nat) :
    ∀ (cs : List Capability) (start : Nat),
      messageOffsets length cs start =
        cs.mapIdx fun i c => (c, start + ((cs.take i).map length).sum)
  | [], _ => rfl
  | c :: cs, start => by
    simp only [messageOffsets, List.mapIdx_cons, List.take_zero, List.map_nil, List.sum_nil,
      Nat.add_zero, List.take_succ_cons, List.map_cons, List.sum_cons, messageOffsets_eq length cs,
      Nat.add_assoc]

/-- The blocks take exactly the message IDs from the start up to the start plus their total. -/
theorem exists_mem_messageOffsets_iff (length : Capability → Nat) (n : Nat) :
    ∀ (cs : List Capability) (start : Nat),
      (∃ p ∈ messageOffsets length cs start, p.2 ≤ n ∧ n < p.2 + length p.1) ↔
        start ≤ n ∧ n < start + (cs.map length).sum
  | [], _ => by simp [messageOffsets]
  | c :: cs, start => by
    simp only [messageOffsets, List.mem_cons, exists_eq_or_imp,
      exists_mem_messageOffsets_iff length n cs, List.map_cons, List.sum_cons]
    omega

/--
The shared capabilities, in alphabetic order, take the message IDs from `0x10` on.

Each one's first ID is `0x10` plus the number of IDs of the shared capabilities before it.
-/
theorem negotiate_eq (length : Capability → Nat) (ours theirs : List Capability) :
    negotiate length ours theirs =
      (sharedCapabilities ours theirs).mapIdx fun i c =>
        (c, 0x10 + (((sharedCapabilities ours theirs).take i).map length).sum) :=
  messageOffsets_eq length _ _

/-- The capabilities that get message IDs are the shared ones, in alphabetic order. -/
theorem map_fst_negotiate (length : Capability → Nat) (ours theirs : List Capability) :
    (negotiate length ours theirs).map Prod.fst = sharedCapabilities ours theirs := by
  rw [negotiate_eq]
  exact List.ext_getElem (by simp) fun _ _ _ => by simp

/--
The shared capabilities use exactly the message IDs from `0x10` up to `0x10` plus their total.

So no ID in that range is left unused.
-/
theorem exists_mem_negotiate_iff (length : Capability → Nat) (ours theirs : List Capability)
    (n : Nat) :
    (∃ p ∈ negotiate length ours theirs, p.2 ≤ n ∧ n < p.2 + length p.1) ↔
      0x10 ≤ n ∧ n < 0x10 + ((sharedCapabilities ours theirs).map length).sum :=
  exists_mem_messageOffsets_iff length n _ _

/--
A capability is negotiated exactly when both peers list it and share no higher version of its name.
-/
theorem mem_sharedCapabilities_iff {ours theirs : List Capability} {c : Capability} :
    c ∈ sharedCapabilities ours theirs ↔
      c ∈ ours ∧ c ∈ theirs ∧
        ∀ d ∈ ours, d ∈ theirs → d.name = c.name → d.version ≤ c.version := by
  simp only [sharedCapabilities, List.mem_mergeSort, List.mem_filter, List.mem_eraseDups,
    List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true]
  exact ⟨fun ⟨⟨ho, ht⟩, h⟩ => ⟨ho, ht, fun d hd hd' hn => (h d ⟨hd, hd'⟩).resolve_left (· hn)⟩,
    fun ⟨ho, ht, h⟩ => ⟨⟨ho, ht⟩, fun d ⟨hd, hd'⟩ =>
      (em (d.name = c.name)).elim (fun hn => .inr (h d hd hd' hn)) .inl⟩⟩

/-- Every negotiated capability is in both lists, with the same name and version. -/
theorem mem_sharedCapabilities {ours theirs : List Capability} {c : Capability}
    (h : c ∈ sharedCapabilities ours theirs) : c ∈ ours ∧ c ∈ theirs :=
  ⟨(mem_sharedCapabilities_iff.mp h).1, (mem_sharedCapabilities_iff.mp h).2.1⟩

/-- The names of the negotiated capabilities strictly increase, byte by byte. -/
theorem pairwise_sharedCapabilities (ours theirs : List Capability) :
    (sharedCapabilities ours theirs).Pairwise
      fun a b => a.name.data.toList < b.name.data.toList := by
  have sorted : (sharedCapabilities ours theirs).Pairwise (Capability.nameLe · ·) :=
    List.pairwise_mergeSort
      (fun a b c hab hbc => by
        simp only [Capability.nameLe, decide_eq_true_eq] at *
        exact List.le_trans hab hbc)
      (fun a b => by
        simpa [Capability.nameLe] using List.le_total a.name.data.toList b.name.data.toList) _
  have nodup : (sharedCapabilities ours theirs).Nodup :=
    ((Base.nodup_eraseDups _).filter _).perm (List.mergeSort_perm _ _).symm
  refine (sorted.and nodup).imp_of_mem fun {a b} ha hb ⟨hle, hne⟩ => ?_
  simp only [Capability.nameLe, decide_eq_true_eq] at hle
  refine (List.le_iff_lt_or_eq.mp hle).resolve_right fun heq => hne ?_
  -- Two negotiated capabilities of one name both have the highest version, so they are one.
  have hname : a.name = b.name := ByteArray.ext (Array.ext' heq)
  have ha := mem_sharedCapabilities_iff.mp ha
  have hb := mem_sharedCapabilities_iff.mp hb
  have hversion := Nat.le_antisymm (hb.2.2 a ha.1 ha.2.1 hname) (ha.2.2 b hb.1 hb.2.1 hname.symm)
  cases a
  cases b
  simp only at hname hversion
  rw [hname, hversion]

/-- Both peers negotiate the same capabilities in the same order, whichever of them asks. -/
theorem sharedCapabilities_comm (ours theirs : List Capability) :
    sharedCapabilities ours theirs = sharedCapabilities theirs ours := by
  have lt := pairwise_sharedCapabilities ours theirs
  have lt' := pairwise_sharedCapabilities theirs ours
  have ne : ∀ {a b : Capability}, a.name.data.toList < b.name.data.toList → a ≠ b :=
    fun hab e => List.lt_irrefl _ (e ▸ hab)
  refine List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => absurd hba (List.lt_asymm hab)) lt lt' ?_
  refine (List.perm_ext_iff_of_nodup (lt.imp ne) (lt'.imp ne)).mpr fun c => ?_
  simp only [mem_sharedCapabilities_iff]
  exact ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₂, h₁, fun d hd hd' => h₃ d hd' hd⟩,
    fun ⟨h₁, h₂, h₃⟩ => ⟨h₂, h₁, fun d hd hd' => h₃ d hd' hd⟩⟩

/-- Both peers give each shared capability the same message IDs, whichever of them asks. -/
theorem negotiate_comm (length : Capability → Nat) (ours theirs : List Capability) :
    negotiate length ours theirs = negotiate length theirs ours := by
  rw [negotiate, negotiate, sharedCapabilities_comm]

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem P2pError.code_injective (e₁ e₂ : P2pError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [P2pError.code] at h; exact absurd h (by decide))

end EthLib.Networking.Devp2p
