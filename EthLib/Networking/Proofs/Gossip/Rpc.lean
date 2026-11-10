module

public import EthLib.Networking.Gossip.Rpc
public import EthLib.Networking.Proofs.Encoding.Protobuf

/-!
# Proofs: the gossip RPC

- Decoding the encoding of an RPC returns it, for an encoding shorter than `2^64` bytes.
- A message whose records parse is rejected for signing exactly when it holds a forbidden field.
- So is every RPC that publishes such a message.
- Such messages exist for each forbidden field: any message with that field written first.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Gossip.Rpc

open EthLib.Networking.Encoding.Protobuf
open EthLib.Networking.Gossip.Rpc
open EthLib.Networking.Proofs.Encoding.Protobuf

/-! ## Helpers -/

variable {α β γ ε : Type}

private theorem toList_serialize (rs : List Record) :
    (serialize rs).data.toList = encodeRecords rs := by
  simp [serialize]

private theorem size_serialize (rs : List Record) :
    (serialize rs).size = (encodeRecords rs).length := by
  simp [serialize, ByteArray.size]

private theorem size_le_of_mem {rs : List Record} {n : Nat} {b : ByteArray}
    (h : (⟨n, .len b⟩ : Record) ∈ rs) : b.size ≤ (encodeRecords rs).length := by
  induction rs with
  | nil => simp at h
  | cons r rs ih =>
    simp only [encodeRecords, List.flatMap_cons, List.length_append] at ih ⊢
    rcases List.mem_cons.mp h with rfl | h
    · simp only [encodeRecord, encodeValue, List.length_append, Array.length_toList]
      have : b.data.size = b.size := rfl
      omega
    · have := ih h; omega

private theorem records_serialize {rs : List Record}
    (hf : ∀ r ∈ rs, 0 < r.field ∧ r.field ≤ maxField) (h : (serialize rs).size < 2 ^ 64) :
    records (serialize rs).data.toList = .ok rs := by
  have hw : ∀ r ∈ rs, r.WellFormed := by
    intro ⟨n, v⟩ hr
    refine ⟨(hf _ hr).1, (hf _ hr).2, ?_⟩
    cases v with
    | len b => have := size_le_of_mem hr; rw [size_serialize] at h; simp only; omega
    | _ => trivial
  rw [toList_serialize, records_encodeRecords hw]

private theorem recordsOf_ok {bytes : ByteArray} {rs : List Record}
    (h : records bytes.data.toList = .ok rs) : recordsOf bytes = .ok rs := by
  simp [recordsOf, h, Except.mapError]

private theorem recordsOf_serialize {rs : List Record}
    (hf : ∀ r ∈ rs, 0 < r.field ∧ r.field ≤ maxField) (h : (serialize rs).size < 2 ^ 64) :
    recordsOf (serialize rs) = .ok rs :=
  recordsOf_ok (records_serialize hf h)

private theorem mapM_ok_mem {f : α → Except ε β} :
    ∀ {l : List α} {ys : List β}, l.mapM f = .ok ys → ∀ x ∈ l, ∃ y ∈ ys, f x = .ok y
  | [], _, _, x, hx => by simp at hx
  | a :: l, ys, h, x, hx => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | error e => simp [ha, bind, Except.bind] at h
    | ok b =>
      cases hl : l.mapM f with
      | error e => simp [ha, hl, bind, Except.bind] at h
      | ok bs =>
        simp only [ha, hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨b, by simp, ha⟩
        · obtain ⟨y, hy, hfy⟩ := mapM_ok_mem hl x hx
          exact ⟨y, by simp [hy], hfy⟩

private theorem stringOf_toUTF8 (n : Nat) (s : String) :
    stringOf n (.len s.toByteArray) = .ok s := by
  simp [stringOf, bytesOf, String.fromUTF8?, String.fromUTF8, s.isValidUTF8, bind,
    Except.bind, pure, Except.pure]

private theorem mapM_map_ok {f : β → Except ε γ} {g : α → β} {k : α → γ} :
    ∀ l : List α, (∀ x ∈ l, f (g x) = .ok (k x)) → (l.map g).mapM f = .ok (l.map k)
  | [], _ => rfl
  | x :: l, h => by
    simp [List.mapM_cons, h x (by simp), mapM_map_ok l (fun y hy => h y (by simp [hy])), bind,
      Except.bind, pure, Except.pure]

private theorem mapM_map_eq {f : β → Except ε α} {g : α → β} (l : List α)
    (h : ∀ x ∈ l, f (g x) = .ok x) : (l.map g).mapM f = .ok l := by
  simpa using mapM_map_ok (k := id) l h

private theorem mapM_bytesOf (l : List α) (f : α → ByteArray) (n : Nat) :
    (l.map fun x => Value.len (f x)).mapM (bytesOf n) = .ok (l.map f) :=
  mapM_map_ok l fun _ _ => rfl

private theorem valuesOf_map (l : List ByteArray) (n m : Nat) :
    valuesOf (l.map (lenRecord n)) m = if n = m then l.map .len else [] := by
  induction l with
  | nil => simp [valuesOf]
  | cons x l ih => by_cases hnm : n = m <;> simp_all [valuesOf, lenRecord]

private theorem valuesOf_map_comp (l : List α) (f : α → ByteArray) (n m : Nat) :
    valuesOf (l.map (lenRecord n ∘ f)) m = if n = m then (l.map f).map .len else [] := by
  rw [← List.map_map, valuesOf_map]

private theorem repeated_bytesOf (l : List ByteArray) (n : Nat) :
    repeated bytesOf (l.map (lenRecord n)) n = .ok l := by
  simp only [repeated, valuesOf_map, ↓reduceIte]
  simpa using mapM_bytesOf l id n

private theorem lenRecord_field (n : Nat) (b : ByteArray) : (lenRecord n b).field = n := rfl

private theorem lenRecord_value (n : Nat) (b : ByteArray) : (lenRecord n b).value = .len b := rfl

private theorem valuesOf_nil (m : Nat) : valuesOf [] m = [] := rfl

private theorem valuesOf_cons (r : Record) (rs : List Record) (m : Nat) :
    valuesOf (r :: rs) m = if r.field = m then r.value :: valuesOf rs m else valuesOf rs m := by
  by_cases h : r.field = m <;> simp [valuesOf, h]

private theorem valuesOf_append (rs rs' : List Record) (m : Nat) :
    valuesOf (rs ++ rs') m = valuesOf rs m ++ valuesOf rs' m := by
  simp [valuesOf]

private theorem mapM_len (l : List ByteArray) (n : Nat) :
    (l.map .len).mapM (bytesOf n) = .ok l := by
  simpa using mapM_bytesOf l id n

private theorem mapM_comp_len (l : List ByteArray) (n : Nat) :
    l.mapM (bytesOf n ∘ Value.len) = .ok l := by
  simpa using mapM_len l n

private theorem mapM_comp_len_comp (l : List α) (f : α → ByteArray) (n : Nat) :
    l.mapM (bytesOf n ∘ Value.len ∘ f) = .ok (l.map f) := by
  simpa using mapM_map_ok (f := bytesOf n ∘ Value.len ∘ f) (g := id) (k := f) l fun _ _ => rfl

private theorem mapM_comp_eq {f : β → Except ε α} {g : α → β} (l : List α)
    (h : ∀ x ∈ l, f (g x) = .ok x) : l.mapM (f ∘ g) = .ok l := by
  simpa using mapM_map_eq l h

private theorem mem_map_comp {l : List α} {x : α} (hx : x ∈ l) (n : Nat) (g : α → ByteArray) :
    lenRecord n (g x) ∈ l.map (lenRecord n ∘ g) :=
  List.mem_map_of_mem (f := lenRecord n ∘ g) hx

private theorem size_lt_of_mem {rs : List Record} {n : Nat} {b : ByteArray}
    (hm : lenRecord n b ∈ rs) (h : (serialize rs).size < 2 ^ 64) : b.size < 2 ^ 64 := by
  have := size_le_of_mem hm
  rw [size_serialize] at h
  omega

private theorem decodeIWant_encode (m : IWant) (h : m.encode.size < 2 ^ 64) :
    decodeIWant m.encode = .ok m := by
  unfold IWant.encode at h ⊢
  rw [decodeIWant, recordsOf_serialize (by simp [lenRecord, maxField]) h]
  simp [repeated_bytesOf, bind, Except.bind, pure, Except.pure]


private theorem decodeIDontWant_encode (m : IDontWant) (h : m.encode.size < 2 ^ 64) :
    decodeIDontWant m.encode = .ok m := by
  unfold IDontWant.encode at h ⊢
  rw [decodeIDontWant, recordsOf_serialize (by simp [lenRecord, maxField]) h]
  simp [repeated_bytesOf, bind, Except.bind, pure, Except.pure]

private theorem decodeGraft_encode (m : Graft) (h : m.encode.size < 2 ^ 64) :
    decodeGraft m.encode = .ok m := by
  unfold Graft.encode at h ⊢
  rw [decodeGraft, recordsOf_serialize (by simp [stringRecord, lenRecord, maxField]) h]
  simp [singular, repeated, valuesOf, stringRecord, lenRecord, stringOf_toUTF8, bind,
    Except.bind, pure, Except.pure]

private theorem decodeIHave_encode (m : IHave) (h : m.encode.size < 2 ^ 64) :
    decodeIHave m.encode = .ok m := by
  unfold IHave.encode at h ⊢
  rw [decodeIHave, recordsOf_serialize (by simp [stringRecord, lenRecord, maxField]) h]
  simp [singular, repeated, valuesOf_cons, valuesOf_map, stringRecord, lenRecord_field,
    lenRecord_value, stringOf_toUTF8, mapM_comp_len, bind, Except.bind, pure, Except.pure]

private theorem decodePeerInfo_encode (p : PeerInfo) (h : p.encode.size < 2 ^ 64) :
    decodePeerInfo p.encode = .ok p := by
  unfold PeerInfo.encode at h ⊢
  rw [decodePeerInfo, recordsOf_serialize (by simp [lenRecord, maxField]) h]
  simp [singular, repeated, valuesOf, lenRecord, bytesOf, bind, Except.bind, pure, Except.pure]

private theorem decodePrune_encode (m : Prune) (h : m.encode.size < 2 ^ 64) :
    decodePrune m.encode = .ok m := by
  unfold Prune.encode at h ⊢
  have hp : m.peers.mapM (decodePeerInfo ∘ PeerInfo.encode) = .ok m.peers :=
    mapM_comp_eq _ fun p hp => decodePeerInfo_encode p <| size_lt_of_mem (n := 2)
      (List.mem_cons_of_mem _ (List.mem_append_left _ (mem_map_comp hp 2 _))) h
  rw [decodePrune, recordsOf_serialize ?_ h]
  · simp [singular, repeated, valuesOf_cons, valuesOf_append, valuesOf_map_comp, valuesOf_nil,
      stringRecord, lenRecord_field, lenRecord_value, stringOf_toUTF8, uint64Of,
      mapM_comp_len_comp, hp, bind, Except.bind, pure, Except.pure]
  · simp [stringRecord, lenRecord, maxField, or_imp, forall_and]

/-! ## Round trips -/

/-- Decoding the encoding of a subscription change returns it. -/
theorem decodeSubOpts_encode (s : SubOpts) (h : s.encode.size < 2 ^ 64) :
    decodeSubOpts s.encode = .ok s := by
  unfold SubOpts.encode at h ⊢
  rw [decodeSubOpts, recordsOf_serialize (by simp [stringRecord, lenRecord, maxField]) h]
  obtain ⟨sub, t⟩ := s
  cases sub <;> simp [singular, repeated, valuesOf, stringRecord, lenRecord, stringOf_toUTF8,
    uint64Of, bind, Except.bind, pure, Except.pure]

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
  have h1 : c.ihave.mapM (decodeIHave ∘ IHave.encode) = .ok c.ihave :=
    mapM_comp_eq _ fun x hx => decodeIHave_encode x <| size_lt_of_mem
      (List.mem_append_left _ <| List.mem_append_left _ <| List.mem_append_left _ <|
        List.mem_append_left _ <| mem_map_comp hx 1 _) h
  have h2 : c.iwant.mapM (decodeIWant ∘ IWant.encode) = .ok c.iwant :=
    mapM_comp_eq _ fun x hx => decodeIWant_encode x <| size_lt_of_mem
      (List.mem_append_left _ <| List.mem_append_left _ <| List.mem_append_left _ <|
        List.mem_append_right _ <| mem_map_comp hx 2 _) h
  have h3 : c.graft.mapM (decodeGraft ∘ Graft.encode) = .ok c.graft :=
    mapM_comp_eq _ fun x hx => decodeGraft_encode x <| size_lt_of_mem
      (List.mem_append_left _ <| List.mem_append_left _ <| List.mem_append_right _ <|
        mem_map_comp hx 3 _) h
  have h4 : c.prune.mapM (decodePrune ∘ Prune.encode) = .ok c.prune :=
    mapM_comp_eq _ fun x hx => decodePrune_encode x <| size_lt_of_mem
      (List.mem_append_left _ <| List.mem_append_right _ <| mem_map_comp hx 4 _) h
  have h5 : c.idontwant.mapM (decodeIDontWant ∘ IDontWant.encode) = .ok c.idontwant :=
    mapM_comp_eq _ fun x hx => decodeIDontWant_encode x <| size_lt_of_mem
      (List.mem_append_right _ <| mem_map_comp hx 5 _) h
  rw [decodeControl, recordsOf_serialize ?_ h]
  · simp [repeated, valuesOf_append, valuesOf_map_comp, mapM_comp_len_comp, h1, h2, h3, h4, h5,
      bind, Except.bind, pure, Except.pure]
  · simp [lenRecord, maxField, or_imp, forall_and]

private theorem merge_empty_left (c : Control) : Control.merge {} c = c := by
  cases c; simp [Control.merge]

/-- Decoding the encoding of an RPC returns it. -/
theorem decodeRpc_encode (rpc : Rpc) (h : rpc.encode.size < 2 ^ 64) :
    decodeRpc rpc.encode = .ok rpc := by
  obtain ⟨subs, pub, c⟩ := rpc
  unfold Rpc.encode at h ⊢
  have h1 : subs.mapM (decodeSubOpts ∘ SubOpts.encode) = .ok subs :=
    mapM_comp_eq _ fun x hx => decodeSubOpts_encode x <| size_lt_of_mem
      (List.mem_append_left _ <| List.mem_append_left _ <| mem_map_comp hx 1 _) h
  have h2 : pub.mapM (decodeMessage ∘ Message.encode) = .ok pub :=
    mapM_comp_eq _ fun x hx => decodeMessage_encode x <| size_lt_of_mem
      (List.mem_append_left _ <| List.mem_append_right _ <| mem_map_comp hx 2 _) h
  by_cases hc : c = {}
  · subst hc
    simp only [ite_true] at h ⊢
    rw [decodeRpc, recordsOf_serialize ?_ h]
    · simp [repeated, valuesOf_append, valuesOf_map_comp, mapM_comp_len_comp, h1, h2, bind,
        Except.bind, pure, Except.pure]
    · simp [lenRecord, maxField, or_imp, forall_and]
  · have h3 : decodeControl c.encode = .ok c :=
      decodeControl_encode c <| size_lt_of_mem (n := 3) (List.mem_append_right _ <| by simp [hc]) h
    simp only [hc, ite_false] at h ⊢
    rw [decodeRpc, recordsOf_serialize ?_ h]
    · simp [repeated, valuesOf_append, valuesOf_map_comp, valuesOf_cons, valuesOf_nil,
        mapM_comp_len_comp, lenRecord_field, lenRecord_value, h1, h2, h3, bytesOf, bind,
        Except.bind, pure, Except.pure, merge_empty_left]
    · simp [lenRecord, maxField, or_imp, forall_and]

/-! ## `StrictNoSign` -/

/-- A message whose records hold a forbidden field is rejected, naming one of its records. -/
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

private theorem mapM_error {f : α → Except ε β} :
    ∀ {l : List α} {e : ε}, l.mapM f = .error e → ∃ x ∈ l, f x = .error e
  | [], _, h => by simp [pure, Except.pure] at h
  | a :: l, e, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | error e' =>
      simp only [ha, bind, Except.bind] at h
      cases h
      exact ⟨a, by simp, ha⟩
    | ok b =>
      cases hl : l.mapM f with
      | error e' =>
        simp only [ha, hl, bind, Except.bind] at h
        cases h
        obtain ⟨x, hx, hfx⟩ := mapM_error hl
        exact ⟨x, by simp [hx], hfx⟩
      | ok bs => simp [ha, hl, bind, Except.bind, pure, Except.pure] at h

private theorem bytesOf_ne_signed {field n : Nat} {v : Value} {e : RpcError}
    (h : bytesOf field v = .error e) : e ≠ .signed n := by
  cases v <;> simp [bytesOf] at h <;> subst h <;> simp

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

private theorem repeated_ne_signed {read : Nat → Value → Except RpcError α}
    (hread : ∀ field v e n, read field v = .error e → e ≠ .signed n) {rs : List Record}
    {field n : Nat} {e : RpcError} (h : repeated read rs field = .error e) : e ≠ .signed n := by
  obtain ⟨v, -, hv⟩ := mapM_error h
  exact hread field v e n hv

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
    (hms : records message.data.toList = .ok ms) (hs : ∃ r ∈ ms, r.field ∈ signedFields)
    (rpc : Rpc) : decodeRpc frame ≠ .ok rpc := by
  obtain ⟨n, -, -, hn⟩ := decodeMessage_signed hms hs
  have hv : Value.len message ∈ valuesOf rs 2 :=
    List.mem_filterMap.mpr ⟨_, hm, by simp [lenRecord]⟩
  intro heq
  simp only [decodeRpc, recordsOf_ok hframe, bind, Except.bind] at heq
  cases h2 : repeated bytesOf rs 2 with
  | error e => split at heq <;> (try split at heq) <;> simp_all
  | ok L =>
    obtain ⟨y, hy, hby⟩ := mapM_ok_mem h2 _ hv
    cases hby
    cases hL : L.mapM decodeMessage with
    | error e => split at heq <;> (try split at heq) <;> simp_all
    | ok ps =>
      obtain ⟨p, -, hp⟩ := mapM_ok_mem hL _ hy
      rw [hn] at hp
      nomatch hp

/-- The records of a message with a forbidden field written first, even an empty one. -/
def signedRecords (n : Nat) (value : ByteArray) (m : Message) : List Record :=
  [lenRecord n value, lenRecord 2 m.data, stringRecord 4 m.topic]

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
  simp [signedRecords, lenRecord_field, hn, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw]

/-- An RPC that publishes such a message is rejected. -/
theorem decodeRpc_signedRecords (m : Message) {n : Nat} (hn : n ∈ signedFields)
    (value : ByteArray)
    (h : (serialize [lenRecord 2 (serialize (signedRecords n value m))]).size < 2 ^ 64)
    (rpc : Rpc) :
    decodeRpc (serialize [lenRecord 2 (serialize (signedRecords n value m))]) ≠ .ok rpc := by
  have hframe := records_serialize (by simp [lenRecord, maxField]) h
  have hms := records_serialize (fields_signedRecords hn value m)
    (size_lt_of_mem (List.mem_singleton_self _) h)
  exact decodeRpc_signed hframe (List.mem_singleton_self _) hms
    ⟨_, List.mem_cons_self .., hn⟩ rpc

end EthLib.Networking.Proofs.Gossip.Rpc
