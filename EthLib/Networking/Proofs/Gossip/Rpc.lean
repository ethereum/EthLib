module

public import EthLib.Base.Proofs.MapM
public import EthLib.Networking.Gossip.Rpc
public import EthLib.Networking.Proofs.Encoding.Protobuf

/-!
# Proofs: the gossip RPC

- Decoding the encoding of an RPC returns it, for an encoding shorter than `2^64` bytes.
  This covers the fields of the partial message extension.
- A subscription change, a control message or an RPC without an extension field has its default.
- A peer that asks for partial messages can send them, and an unsubscription does neither.
- A message whose records parse is rejected for signing exactly when it holds a forbidden field.
- An RPC that publishes such a message is rejected.
- For each forbidden field, a message with that field written first is rejected, even empty.
- Two errors with one code come from one constructor.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Gossip.Rpc

open EthLib.Base
open EthLib.Networking.Encoding.Protobuf
open EthLib.Networking.Gossip
open EthLib.Networking.Proofs.Encoding.Protobuf

/-! ## Helpers -/

variable {α : Type}

/-- Records that parse are the records of the message. -/
private theorem recordsOf_ok {bytes : ByteArray} {rs : List Record}
    (h : records bytes.data.toList = .ok rs) : recordsOf bytes = .ok rs := by
  simp [recordsOf, h, Except.mapError]

/-- The records of a serialized message are its records, for fields in range. -/
private theorem recordsOf_serialize {rs : List Record}
    (hf : ∀ r ∈ rs, 0 < r.field ∧ r.field ≤ maxField) (h : (serialize rs).size < 2 ^ 64) :
    recordsOf (serialize rs) = .ok rs :=
  recordsOf_ok (records_serialize hf h)

/-- A string written in UTF-8 reads back as itself. -/
private theorem stringOf_toUTF8 (n : Nat) (s : String) :
    stringOf n (.len s.toByteArray) = .ok s := by
  simp [stringOf, bytesOf, String.fromUTF8?, String.fromUTF8, s.isValidUTF8, bind,
    Except.bind, pure, Except.pure]

/-- Length-delimited records of one field give their values to that field alone. -/
private theorem valuesOf_map (l : List ByteArray) (n m : Nat) :
    valuesOf (l.map (lenRecord n)) m = if n = m then l.map .len else [] := by
  induction l with
  | nil => simp [valuesOf]
  | cons x l ih => by_cases hnm : n = m <;> simp_all [valuesOf, lenRecord]

/-- The same, for records that encode each item of a list. -/
private theorem valuesOf_map_comp (l : List α) (f : α → ByteArray) (n m : Nat) :
    valuesOf (l.map (lenRecord n ∘ f)) m = if n = m then (l.map f).map .len else [] := by
  rw [← List.map_map, valuesOf_map]

/-- The byte strings of length-delimited records of one field read back as themselves. -/
private theorem repeated_bytesOf (l : List ByteArray) (n : Nat) :
    repeated bytesOf (l.map (lenRecord n)) n = .ok l := by
  simp only [repeated, valuesOf_map, ↓reduceIte, List.mapM_map]
  exact (mapM_eq_ok_map (g := id) fun _ _ => rfl).trans (by rw [List.map_id])

/-- The byte strings that encode each item of a list read back as themselves. -/
private theorem mapM_bytesOf_len (l : List α) (f : α → ByteArray) (n : Nat) :
    l.mapM (bytesOf n ∘ Value.len ∘ f) = .ok (l.map f) :=
  mapM_eq_ok_map fun _ _ => rfl

/-- The record of an item lies among the records of the list. -/
private theorem mem_map_comp {l : List α} {x : α} (hx : x ∈ l) (n : Nat) (g : α → ByteArray) :
    lenRecord n (g x) ∈ l.map (lenRecord n ∘ g) :=
  List.mem_map_of_mem (f := lenRecord n ∘ g) hx

/-- Decoding the encoding of an IWANT message returns it. -/
private theorem decodeIWant_encode (m : IWant) (h : m.encode.size < 2 ^ 64) :
    decodeIWant m.encode = .ok m := by
  unfold IWant.encode at h ⊢
  rw [decodeIWant, recordsOf_serialize (by simp [lenRecord, maxField]) h]
  simp [repeated_bytesOf, bind, Except.bind, pure, Except.pure]

/-- Decoding the encoding of an IDONTWANT message returns it. -/
private theorem decodeIDontWant_encode (m : IDontWant) (h : m.encode.size < 2 ^ 64) :
    decodeIDontWant m.encode = .ok m := by
  unfold IDontWant.encode at h ⊢
  rw [decodeIDontWant, recordsOf_serialize (by simp [lenRecord, maxField]) h]
  simp [repeated_bytesOf, bind, Except.bind, pure, Except.pure]

/-- Decoding the encoding of a GRAFT message returns it. -/
private theorem decodeGraft_encode (m : Graft) (h : m.encode.size < 2 ^ 64) :
    decodeGraft m.encode = .ok m := by
  unfold Graft.encode at h ⊢
  rw [decodeGraft, recordsOf_serialize (by simp [stringRecord, lenRecord, maxField]) h]
  simp [singular, repeated, valuesOf, stringRecord, lenRecord, stringOf_toUTF8, bind,
    Except.bind, pure, Except.pure]

/-- Decoding the encoding of an IHAVE message returns it. -/
private theorem decodeIHave_encode (m : IHave) (h : m.encode.size < 2 ^ 64) :
    decodeIHave m.encode = .ok m := by
  unfold IHave.encode at h ⊢
  rw [decodeIHave, recordsOf_serialize (by simp [stringRecord, lenRecord, maxField]) h]
  have ids : m.messageIds.mapM (bytesOf 2 ∘ Value.len) = .ok (m.messageIds.map id) :=
    mapM_eq_ok_map fun _ _ => rfl
  simp [singular, repeated, valuesOf_cons, valuesOf_map, stringRecord, lenRecord,
    stringOf_toUTF8, ids, bind, Except.bind, pure, Except.pure]

/-- Decoding the encoding of a peer offered in a PRUNE returns it. -/
private theorem decodePeerInfo_encode (p : PeerInfo) (h : p.encode.size < 2 ^ 64) :
    decodePeerInfo p.encode = .ok p := by
  unfold PeerInfo.encode at h ⊢
  rw [decodePeerInfo, recordsOf_serialize (by simp [lenRecord, maxField]) h]
  simp [singular, repeated, valuesOf, lenRecord, bytesOf, bind, Except.bind, pure, Except.pure]

/-- Decoding the encoding of a PRUNE message returns it. -/
private theorem decodePrune_encode (m : Prune) (h : m.encode.size < 2 ^ 64) :
    decodePrune m.encode = .ok m := by
  unfold Prune.encode at h ⊢
  have hp : m.peers.mapM (decodePeerInfo ∘ PeerInfo.encode) = .ok (m.peers.map id) :=
    mapM_eq_ok_map fun p hp => decodePeerInfo_encode p <| size_lt_of_mem (n := 2)
      (List.mem_cons_of_mem _ (List.mem_append_left _ (mem_map_comp hp 2 _))) h
  rw [decodePrune, recordsOf_serialize ?_ h]
  · simp [singular, repeated, valuesOf_cons, valuesOf_append, valuesOf_map_comp, valuesOf_nil,
      stringRecord, lenRecord, stringOf_toUTF8, uint64Of, mapM_bytesOf_len, hp, bind,
      Except.bind, pure, Except.pure]
  · simp [stringRecord, lenRecord, maxField, or_imp, forall_and]

/-- Decoding the encoding of the extensions of a control message returns them. -/
private theorem decodeControlExtensions_encode (e : ControlExtensions)
    (h : e.encode.size < 2 ^ 64) : decodeControlExtensions e.encode = .ok e := by
  unfold ControlExtensions.encode at h ⊢
  obtain ⟨b⟩ := e
  cases b <;>
  · rw [decodeControlExtensions, recordsOf_serialize (by simp [maxField]) h]
    simp [singular, repeated, valuesOf, uint64Of, bind, Except.bind, pure, Except.pure]

/-- Decoding the encoding of a partial message returns it. -/
private theorem decodePartial_encode (m : PartialMessagesExtension)
    (h : m.encode.size < 2 ^ 64) : decodePartial m.encode = .ok m := by
  unfold PartialMessagesExtension.encode at h ⊢
  rw [decodePartial, recordsOf_serialize ?_ h]
  · obtain ⟨t, g, p, q⟩ := m
    cases p <;> cases q <;> simp [singular, repeated, valuesOf, lenRecord, bytesOf, bind,
      Except.bind, pure, Except.pure]
  · simp [lenRecord, maxField, or_imp, forall_and]

/-- Merging empty control messages with others returns the others. -/
private theorem merge_empty_left (c : Control) : Control.merge {} c = c := by
  cases c; simp [Control.merge]

/-- A field without records has no values. -/
private theorem valuesOf_eq_nil {rs : List Record} {n : Nat} (h : ∀ r ∈ rs, r.field ≠ n) :
    valuesOf rs n = [] := by
  simp only [valuesOf, List.filterMap_eq_nil_iff]
  intro r hr
  simp [h r hr]

/-- A singular field without records has its default. -/
private theorem singular_of_nil {read : Nat → Value → Except RpcError α} {d : α}
    {rs : List Record} {n : Nat} (h : ∀ r ∈ rs, r.field ≠ n) : singular read d rs n = .ok d := by
  simp [singular, repeated, valuesOf_eq_nil h, bind, Except.bind, pure, Except.pure]

/-- The last item of the list of an optional value is that value. -/
private theorem getLast?_toList (o : Option α) : o.toList.getLast? = o := by
  cases o <;> rfl

/-- An optional field without records is missing. -/
private theorem lastMessage_of_nil {decode : ByteArray → Except RpcError α} {rs : List Record}
    {n : Nat} (h : ∀ r ∈ rs, r.field ≠ n) : lastMessage decode rs n = .ok none := by
  simp [lastMessage, repeated, valuesOf_eq_nil h, bind, Except.bind, pure, Except.pure]

/-! ## Round trips -/

/-- Decoding the encoding of a subscription change returns it. -/
theorem decodeSubOpts_encode (s : SubOpts) (h : s.encode.size < 2 ^ 64) :
    decodeSubOpts s.encode = .ok s := by
  unfold SubOpts.encode at h ⊢
  rw [decodeSubOpts, recordsOf_serialize (by simp [stringRecord, lenRecord, maxField]; grind) h]
  obtain ⟨sub, t, rp, sp⟩ := s
  cases sub <;> cases rp <;> cases sp <;> simp [singular, repeated, valuesOf, stringRecord,
    lenRecord, stringOf_toUTF8, uint64Of, bind, Except.bind, pure, Except.pure]

/-- Decoding the encoding of a message returns it. -/
theorem decodeMessage_encode (m : Message) (h : m.encode.size < 2 ^ 64) :
    decodeMessage m.encode = .ok m := by
  unfold Message.encode at h ⊢
  rw [decodeMessage, recordsOf_serialize (by simp [stringRecord, lenRecord, maxField]) h]
  simp [signedFields, singular, repeated, valuesOf, stringRecord, lenRecord, stringOf_toUTF8,
    bytesOf, bind, Except.bind, pure, Except.pure]

/-- Decoding the encoding of the control messages returns them. -/
theorem decodeControl_encode (c : Control) (h : c.encode.size < 2 ^ 64) :
    decodeControl c.encode = .ok c := by
  unfold Control.encode at h ⊢
  have h1 : c.ihave.mapM (decodeIHave ∘ IHave.encode) = .ok (c.ihave.map id) :=
    mapM_eq_ok_map fun x hx => decodeIHave_encode x <| size_lt_of_mem
      (List.mem_append_left _ <| List.mem_append_left _ <| List.mem_append_left _ <|
        List.mem_append_left _ <| List.mem_append_left _ <| mem_map_comp hx 1 _) h
  have h2 : c.iwant.mapM (decodeIWant ∘ IWant.encode) = .ok (c.iwant.map id) :=
    mapM_eq_ok_map fun x hx => decodeIWant_encode x <| size_lt_of_mem
      (List.mem_append_left _ <| List.mem_append_left _ <| List.mem_append_left _ <|
        List.mem_append_left _ <| List.mem_append_right _ <| mem_map_comp hx 2 _) h
  have h3 : c.graft.mapM (decodeGraft ∘ Graft.encode) = .ok (c.graft.map id) :=
    mapM_eq_ok_map fun x hx => decodeGraft_encode x <| size_lt_of_mem
      (List.mem_append_left _ <| List.mem_append_left _ <| List.mem_append_left _ <|
        List.mem_append_right _ <| mem_map_comp hx 3 _) h
  have h4 : c.prune.mapM (decodePrune ∘ Prune.encode) = .ok (c.prune.map id) :=
    mapM_eq_ok_map fun x hx => decodePrune_encode x <| size_lt_of_mem
      (List.mem_append_left _ <| List.mem_append_left _ <| List.mem_append_right _ <|
        mem_map_comp hx 4 _) h
  have h5 : c.idontwant.mapM (decodeIDontWant ∘ IDontWant.encode) = .ok (c.idontwant.map id) :=
    mapM_eq_ok_map fun x hx => decodeIDontWant_encode x <| size_lt_of_mem
      (List.mem_append_left _ <| List.mem_append_right _ <| mem_map_comp hx 5 _) h
  have h6 : c.extensions.toList.mapM (decodeControlExtensions ∘ ControlExtensions.encode) =
      .ok (c.extensions.toList.map id) :=
    mapM_eq_ok_map fun x hx => decodeControlExtensions_encode x <| size_lt_of_mem (n := 6)
      (List.mem_append_right _ <| mem_map_comp hx 6 _) h
  rw [decodeControl, recordsOf_serialize ?_ h]
  · simp [lastMessage, getLast?_toList, repeated, valuesOf_append, valuesOf_map_comp,
      mapM_bytesOf_len, h1, h2, h3, h4, h5, h6, bind, Except.bind, pure, Except.pure]
  · simp [lenRecord, maxField, or_imp, forall_and]

/-- Decoding the encoding of an RPC returns it. -/
theorem decodeRpc_encode (rpc : Rpc) (h : rpc.encode.size < 2 ^ 64) :
    decodeRpc rpc.encode = .ok rpc := by
  obtain ⟨subs, pub, c, part⟩ := rpc
  unfold Rpc.encode at h ⊢
  have h1 : subs.mapM (decodeSubOpts ∘ SubOpts.encode) = .ok (subs.map id) :=
    mapM_eq_ok_map fun x hx => decodeSubOpts_encode x <| size_lt_of_mem
      (List.mem_append_left _ <| List.mem_append_left _ <| List.mem_append_left _ <|
        mem_map_comp hx 1 _) h
  have h2 : pub.mapM (decodeMessage ∘ Message.encode) = .ok (pub.map id) :=
    mapM_eq_ok_map fun x hx => decodeMessage_encode x <| size_lt_of_mem
      (List.mem_append_left _ <| List.mem_append_left _ <| List.mem_append_right _ <|
        mem_map_comp hx 2 _) h
  have h4 : part.toList.mapM (decodePartial ∘ PartialMessagesExtension.encode) =
      .ok (part.toList.map id) :=
    mapM_eq_ok_map fun x hx => decodePartial_encode x <| size_lt_of_mem (n := 10)
      (List.mem_append_right _ <| mem_map_comp hx 10 _) h
  by_cases hc : c = {}
  · subst hc
    simp only [ite_true] at h ⊢
    rw [decodeRpc, recordsOf_serialize ?_ h]
    · simp [lastMessage, getLast?_toList, repeated, valuesOf_append, valuesOf_map_comp,
        mapM_bytesOf_len, h1, h2, h4, bind, Except.bind, pure, Except.pure]
    · simp [lenRecord, maxField, or_imp, forall_and]
  · have h3 : decodeControl c.encode = .ok c :=
      decodeControl_encode c <| size_lt_of_mem (n := 3)
        (List.mem_append_left _ <| List.mem_append_right _ <| by simp [hc]) h
    simp only [hc, ite_false] at h ⊢
    rw [decodeRpc, recordsOf_serialize ?_ h]
    · simp [lastMessage, getLast?_toList, repeated, valuesOf_append, valuesOf_map_comp,
        valuesOf_cons, lenRecord, mapM_bytesOf_len, h1, h2, h3, h4, bytesOf, bind, Except.bind,
        pure, Except.pure,
        merge_empty_left]
    · simp [lenRecord, maxField, or_imp, forall_and]

/-! ## Messages without the extension fields -/

/-- A subscription change without the fields of the partial message extension has both false. -/
theorem decodeSubOpts_no_partial {bytes : ByteArray} {rs : List Record} {s : SubOpts}
    (hr : recordsOf bytes = .ok rs) (hf : ∀ r ∈ rs, r.field ≠ 3 ∧ r.field ≠ 4)
    (h : decodeSubOpts bytes = .ok s) :
    s.requestsPartial = false ∧ s.supportsSendingPartial = false := by
  have h3 : singular uint64Of 0 rs 3 = .ok 0 := singular_of_nil fun r hr => (hf r hr).1
  have h4 : singular uint64Of 0 rs 4 = .ok 0 := singular_of_nil fun r hr => (hf r hr).2
  simp only [decodeSubOpts, hr, h3, h4, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (injection h with h; subst h; simp) | nomatch h

/-- A control message without the field of the extensions has none. -/
theorem decodeControl_no_extensions {bytes : ByteArray} {rs : List Record} {c : Control}
    (hr : recordsOf bytes = .ok rs) (hf : ∀ r ∈ rs, r.field ≠ 6)
    (h : decodeControl bytes = .ok c) : c.extensions = none := by
  have h6 : lastMessage decodeControlExtensions rs 6 = .ok none := lastMessage_of_nil hf
  simp only [decodeControl, hr, h6, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (injection h with h; subst h; simp) | nomatch h

/-- An RPC without the field of the partial message extension carries no partial message. -/
theorem decodeRpc_no_partial {bytes : ByteArray} {rs : List Record} {rpc : Rpc}
    (hr : recordsOf bytes = .ok rs) (hf : ∀ r ∈ rs, r.field ≠ 10)
    (h : decodeRpc bytes = .ok rpc) : rpc.partialMessage = none := by
  have h10 : lastMessage decodePartial rs 10 = .ok none := lastMessage_of_nil hf
  simp only [decodeRpc, hr, h10, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (injection h with h; subst h; simp) | nomatch h

/-! ## Partial flags -/

/-- A peer that asks for partial messages can send them. -/
theorem SubOpts.sendsPartial_of_asksPartial {s : SubOpts} (h : s.asksPartial = true) :
    s.sendsPartial = true := by
  cases s with
  | mk sub t req sup => cases sub <;> cases req <;> cases sup <;> simp_all [SubOpts.asksPartial,
      SubOpts.sendsPartial]

/-- An unsubscription neither asks for partial messages nor can send them. -/
theorem SubOpts.partial_of_unsubscribe {s : SubOpts} (h : s.subscribe = false) :
    s.asksPartial = false ∧ s.sendsPartial = false := by
  simp [SubOpts.asksPartial, SubOpts.sendsPartial, h]

/-! ## `StrictNoSign` -/

/-- A message whose records hold a forbidden field is rejected with the number of one. -/
theorem decodeMessage_signed {bytes : ByteArray} {rs : List Record}
    (h : records bytes.data.toList = .ok rs) (hs : ∃ r ∈ rs, r.field ∈ signedFields) :
    ∃ r ∈ rs, r.field ∈ signedFields ∧ decodeMessage bytes = .error (.signed r.field) := by
  obtain ⟨r, hr, hf⟩ := hs
  cases hfind : rs.find? (·.field ∈ signedFields) with
  | none =>
    rw [List.find?_eq_none] at hfind
    exact absurd (by simpa using hf) (hfind r hr)
  | some r' =>
    refine ⟨r', List.mem_of_find?_eq_some hfind, by simpa using List.find?_some hfind, ?_⟩
    simp [decodeMessage, recordsOf_ok h, hfind, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw]

/-- Reading the bytes of a value never fails for signing. -/
private theorem bytesOf_ne_signed {field n : Nat} {v : Value} {e : RpcError}
    (h : bytesOf field v = .error e) : e ≠ .signed n := by
  cases v <;> simp [bytesOf] at h <;> subst h <;> simp

/-- Reading a string never fails for signing. -/
private theorem stringOf_ne_signed {field n : Nat} {v : Value} {e : RpcError}
    (h : stringOf field v = .error e) : e ≠ .signed n := by
  unfold stringOf at h
  cases hb : bytesOf field v with
  | error e' =>
    simp only [hb, bind, Except.bind] at h
    cases h
    exact bytesOf_ne_signed hb
  | ok b =>
    simp only [hb, bind, Except.bind] at h
    split at h <;> simp [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    subst h; simp

/-- A repeated field never fails for signing when reading one of its values never does. -/
private theorem repeated_ne_signed {read : Nat → Value → Except RpcError α}
    (hread : ∀ field v e n, read field v = .error e → e ≠ .signed n) {rs : List Record}
    {field n : Nat} {e : RpcError} (h : repeated read rs field = .error e) : e ≠ .signed n := by
  obtain ⟨i, hi, hv, -⟩ := mapM_error h
  exact hread field _ e n hv

/-- A parsed message is rejected for signing exactly when it holds a forbidden field. -/
theorem decodeMessage_signed_iff {bytes : ByteArray} {rs : List Record}
    (h : records bytes.data.toList = .ok rs) :
    (∃ n, decodeMessage bytes = .error (.signed n)) ↔ ∃ r ∈ rs, r.field ∈ signedFields := by
  refine ⟨fun ⟨n, hn⟩ => ?_, fun hs => ?_⟩
  · refine Classical.byContradiction fun hno => ?_
    have hfind : rs.find? (·.field ∈ signedFields) = none := by
      rw [List.find?_eq_none]
      intro r hr hf
      exact hno ⟨r, hr, by simpa using hf⟩
    have hb : ∀ field v e n, bytesOf field v = .error e → e ≠ .signed n :=
      fun _ _ _ _ h => bytesOf_ne_signed h
    have hs : ∀ field v e n, stringOf field v = .error e → e ≠ .signed n :=
      fun _ _ _ _ h => stringOf_ne_signed h
    simp only [decodeMessage, recordsOf_ok h, hfind, singular, bind, Except.bind] at hn
    cases hd : repeated bytesOf rs 2 with
    | error e => simp only [hd] at hn; exact repeated_ne_signed hb hd (Except.error.inj hn)
    | ok ds =>
      cases ht : repeated stringOf rs 4 with
      | error e => simp [hd, ht, pure, Except.pure] at hn; exact repeated_ne_signed hs ht hn
      | ok ts =>
        simp only [hd, ht, pure, Except.pure] at hn
        split at hn <;> simp [throw, throwThe, MonadExceptOf.throw] at hn
  · obtain ⟨r, -, -, hr⟩ := decodeMessage_signed h hs
    exact ⟨_, hr⟩

/-- An RPC that publishes a message holding a forbidden field is rejected. -/
theorem decodeRpc_signed {frame message : ByteArray} {rs ms : List Record}
    (hframe : records frame.data.toList = .ok rs) (hm : lenRecord 2 message ∈ rs)
    (hms : records message.data.toList = .ok ms) (hs : ∃ r ∈ ms, r.field ∈ signedFields) :
    ∀ rpc, decodeRpc frame ≠ .ok rpc := by
  intro rpc
  obtain ⟨n, -, -, hn⟩ := decodeMessage_signed hms hs
  have hv : Value.len message ∈ valuesOf rs 2 :=
    List.mem_filterMap.mpr ⟨_, hm, by simp [lenRecord]⟩
  intro heq
  simp only [decodeRpc, recordsOf_ok hframe, bind, Except.bind] at heq
  cases h2 : repeated bytesOf rs 2 with
  | error e => split at heq <;> (try split at heq) <;> simp_all
  | ok L =>
    obtain ⟨y, hy, hby⟩ := exists_mem_of_mapM_ok h2 hv
    cases hby
    cases hL : L.mapM decodeMessage with
    | error e => split at heq <;> (try split at heq) <;> simp_all
    | ok ps =>
      obtain ⟨p, -, hp⟩ := exists_mem_of_mapM_ok hL hy
      rw [hn] at hp
      nomatch hp

/-- The records of a message with a given field written first, then its data and its topic. -/
def signedRecords (n : Nat) (value : ByteArray) (m : Message) : List Record :=
  [lenRecord n value, lenRecord 2 m.data, stringRecord 4 m.topic]

/-- The records of such a message have their field numbers in range. -/
private theorem fields_signedRecords {n : Nat} (hn : n ∈ signedFields) (value : ByteArray)
    (m : Message) : ∀ r ∈ signedRecords n value m, 0 < r.field ∧ r.field ≤ maxField := by
  simp only [signedFields, List.mem_cons, List.mem_nil_iff, or_false] at hn
  simp only [signedRecords, stringRecord, List.mem_cons, List.mem_nil_iff, or_false]
  rintro r (rfl | rfl | rfl) <;> simp [lenRecord, maxField] <;> omega

/-- A message with a forbidden field written first is rejected, even when that field is empty. -/
theorem decodeMessage_signedRecords (m : Message) {n : Nat} (hn : n ∈ signedFields)
    (value : ByteArray) (h : (serialize (signedRecords n value m)).size < 2 ^ 64) :
    decodeMessage (serialize (signedRecords n value m)) = .error (.signed n) := by
  rw [decodeMessage, recordsOf_serialize (fields_signedRecords hn value m) h]
  simp [signedRecords, lenRecord, hn, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- An RPC that publishes such a message is rejected. -/
theorem decodeRpc_signedRecords (m : Message) {n : Nat} (hn : n ∈ signedFields)
    (value : ByteArray)
    (h : (serialize [lenRecord 2 (serialize (signedRecords n value m))]).size < 2 ^ 64) :
    ∀ rpc,
      decodeRpc (serialize [lenRecord 2 (serialize (signedRecords n value m))]) ≠ .ok rpc := by
  intro rpc
  have hframe := records_serialize (by simp [lenRecord, maxField]) h
  have hms := records_serialize (fields_signedRecords hn value m)
    (size_lt_of_mem (List.mem_singleton_self _) h)
  exact decodeRpc_signed hframe (List.mem_singleton_self _) hms
    ⟨_, List.mem_cons_self .., hn⟩ rpc

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Networking.Gossip.RpcError.code_injective
    (e₁ e₂ : RpcError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [RpcError.code] at h; exact absurd h (by decide))

end EthLib.Networking.Proofs.Gossip.Rpc
