module

public import EthLib.Networking.Noise.Identity
public import EthLib.Networking.Proofs.Noise
public import EthLib.Networking.Proofs.Libp2p.PeerId
public import EthLib.Networking.Proofs.Encoding.Protobuf

/-!
# Proofs: libp2p Noise authentication

Reading message 2 or 3 accepts only a payload signed over the static key the message carries.

The state then keeps that remote, so completion only returns it with the transport ciphers.

Completion checks that the remote has the remote static key of the handshake.

In a state that the libp2p functions produce, the stored remote has that key.

Its signature verifies on that key, held by the handshake state that gives the transport ciphers.

Such a state at step 3 always holds a remote, so completion succeeds.
-/

public section

namespace EthLib.Networking.Noise

open EthLib.Cryptography.Secp256k1 (Fn)

/-- Successful authentication keeps the static key, and the fields of the decoded payload.

The signature verifies on that static key, and the public key decodes to the stored point. -/
theorem authenticatePayload_ok {staticKey : Key} {bytes : ByteArray} {remote : Remote}
    (h : authenticatePayload staticKey bytes = .ok remote) :
    remote.staticKey = staticKey ∧
      decodePayload bytes = .ok ⟨remote.publicKey, remote.signature, remote.extensions⟩ ∧
      Libp2p.verify remote.publicKey (signedStatic staticKey) remote.signature = true ∧
      Libp2p.decodePublicKey remote.publicKey = .ok remote.key := by
  unfold authenticatePayload at h
  cases hd : decodePayload bytes with
  | error error => simp [hd, bind, Except.bind] at h
  | ok p =>
    simp only [hd] at h
    dsimp only [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
    split at h
    · rename_i hv
      split at h
      · rename_i key hk
        cases h
        have hpk : Remote.publicKey ⟨staticKey, key, p.signature, p.extensions⟩ = p.publicKey :=
          Proofs.Libp2p.PeerId.encodePublicKey_of_decodePublicKey hk
        refine ⟨rfl, ?_, ?_, ?_⟩
        · rw [hpk]
        · rw [hpk]; exact hv
        · rw [hpk]; exact hk
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- Completion returns the stored remote and the transport ciphers of the same state.

The remote has the remote static key of that state's handshake. -/
theorem complete_ok {s : Libp2pState} {remote : Remote} {send receive : CipherState}
    (h : complete s = .ok (remote, send, receive)) :
    s.remote = some remote ∧ s.handshake.remoteStatic = some remote.staticKey ∧
      transport s.handshake = .ok (send, receive) := by
  unfold complete at h
  cases ht : transport s.handshake with
  | error e => simp [ht, bind, Except.bind] at h
  | ok p =>
    obtain ⟨a, b⟩ := p
    cases hr : s.remote with
    | none => simp [ht, hr, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    | some r =>
      by_cases hk : s.handshake.remoteStatic = some r.staticKey
      · simp [ht, hr, hk, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, hk, rfl⟩
      · simp [ht, hr, hk, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-- Reading message 2 or 3 accepts only a payload signed over the static key the message carries.

The new state keeps the remote of that payload. -/
theorem readLibp2p_authenticates {s next : Libp2pState} {message : ByteArray}
    (h : readLibp2p s message = .ok next) (hstep : next.handshake.step ≠ 1) :
    ∃ payload remote,
      readMessage s.handshake message = .ok (next.handshake, payload) ∧
      next.remote = some remote ∧
      next.handshake.remoteStatic = some remote.staticKey ∧
      decodePayload payload = .ok ⟨remote.publicKey, remote.signature, remote.extensions⟩ ∧
      Libp2p.verify remote.publicKey (signedStatic remote.staticKey) remote.signature = true ∧
      Libp2p.decodePublicKey remote.publicKey = .ok remote.key := by
  unfold readLibp2p at h
  cases hr : readMessage s.handshake message with
  | error error => simp [hr, bind, Except.bind] at h
  | ok result =>
    obtain ⟨handshake, payload⟩ := result
    simp only [hr] at h
    dsimp only [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
    split at h
    · rename_i hone
      cases hd : decodePayload payload with
      | error error => simp [hd] at h
      | ok first =>
        simp only [hd] at h
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · cases h
          exact absurd hone hstep
    · cases hs : handshake.remoteStatic with
      | none => simp [hs, requireKey] at h
      | some staticKey =>
        simp only [hs, requireKey] at h
        cases ha : authenticatePayload staticKey payload with
        | error error => simp [ha] at h
        | ok remote =>
          simp only [ha] at h
          cases h
          obtain ⟨hkey, hdecode, hverify, hpoint⟩ := authenticatePayload_ok ha
          subst hkey
          exact ⟨payload, remote, rfl, rfl, hs, hdecode, hverify, hpoint⟩

/-- Writing a libp2p message writes an XX message and keeps the remote. -/
theorem writeLibp2p_ok {s next : Libp2pState} {identitySecret : Fn}
    {extensions : Option ByteArray} {message : ByteArray}
    (h : writeLibp2p s identitySecret extensions = .ok (next, message)) :
    ∃ payload handshake, writeMessage s.handshake payload = .ok (handshake, message) ∧
      next = { s with handshake := handshake } := by
  unfold writeLibp2p at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first
    | (rename_i hw; cases h; exact ⟨_, _, hw, rfl⟩)
    | cases h

/-- Reading a libp2p message reads an XX message, and message 1 leaves no remote. -/
theorem readLibp2p_ok {s next : Libp2pState} {message : ByteArray}
    (h : readLibp2p s message = .ok next) :
    (∃ payload, readMessage s.handshake message = .ok (next.handshake, payload)) ∧
      (next.handshake.step = 1 → next.remote = none) := by
  unfold readLibp2p at h
  cases hr : readMessage s.handshake message with
  | error error => simp [hr, bind, Except.bind] at h
  | ok result =>
    obtain ⟨handshake, payload⟩ := result
    simp only [hr] at h
    dsimp only [Bind.bind, Pure.pure, Except.bind, Except.pure] at h
    split at h
    · cases hd : decodePayload payload with
      | error error => simp [hd] at h
      | ok first =>
        simp only [hd] at h
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · cases h
          exact ⟨⟨payload, rfl⟩, fun _ => rfl⟩
    · rename_i hone
      cases hs : handshake.remoteStatic with
      | none => simp [hs, requireKey] at h
      | some staticKey =>
        simp only [hs, requireKey] at h
        cases ha : authenticatePayload staticKey payload with
        | error error => simp [ha] at h
        | ok remote =>
          simp only [ha] at h
          cases h
          exact ⟨⟨payload, rfl⟩, fun hstep => absurd hstep hone⟩

/-- A state that the libp2p functions produce from an initial state. -/
inductive Produced : Libp2pState → Prop where
  /-- An initial state. -/
  | init (initiator : Bool) (staticKey ephemeralKey : Key) :
    Produced (initializeLibp2p initiator staticKey ephemeralKey)
  /-- The state after a successful write. -/
  | write {s next : Libp2pState} {identitySecret : Fn} {extensions : Option ByteArray}
    {message : ByteArray} (hs : Produced s)
    (h : writeLibp2p s identitySecret extensions = .ok (next, message)) : Produced next
  /-- The state after a successful read. -/
  | read {s next : Libp2pState} {message : ByteArray} (hs : Produced s)
    (h : readLibp2p s message = .ok next) : Produced next

/-- In a produced state, the remote has the static key of the handshake.

Its signature verifies on that key, and its public key decodes to its point. -/
theorem Produced.remote_ok {s : Libp2pState} {remote : Remote} (hs : Produced s)
    (h : s.remote = some remote) :
    s.handshake.remoteStatic = some remote.staticKey ∧
      Libp2p.verify remote.publicKey (signedStatic remote.staticKey) remote.signature = true ∧
      Libp2p.decodePublicKey remote.publicKey = .ok remote.key := by
  induction hs generalizing remote with
  | init => simp [initializeLibp2p] at h
  | write _ hw ih =>
    obtain ⟨payload, handshake, hwm, rfl⟩ := writeLibp2p_ok hw
    obtain ⟨-, -, hstatic, -⟩ := writeMessage_ok hwm
    obtain ⟨h1, h2, h3⟩ := ih h
    exact ⟨hstatic.trans h1, h2, h3⟩
  | @read _ next _ _ hr _ =>
    by_cases hone : next.handshake.step = 1
    · simp [(readLibp2p_ok hr).2 hone] at h
    · obtain ⟨_, r, -, hrem, hstatic, -, hverify, hpoint⟩ := readLibp2p_authenticates hr hone
      rw [hrem] at h
      cases h
      exact ⟨hstatic, hverify, hpoint⟩

/-- A produced state holds a remote once the handshake has read the remote's static key.

The initiator reads it in message 2, and the responder in message 3. -/
theorem Produced.remote_isSome {s : Libp2pState} (hs : Produced s)
    (hstep : s.handshake.initiator = true ∧ 2 ≤ s.handshake.step ∨
      s.handshake.initiator = false ∧ s.handshake.step = 3) :
    s.remote.isSome := by
  induction hs with
  | init => simp [initializeLibp2p, initializeHandshake] at hstep
  | write _ hw ih =>
    obtain ⟨payload, handshake, hwm, rfl⟩ := writeLibp2p_ok hw
    obtain ⟨hi, hst, -, hphase⟩ := writeMessage_ok hwm
    simp only [hi, hst] at hstep
    apply ih
    rcases hphase with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2] at hstep ⊢
  | @read _ next _ _ hr _ =>
    have hone : next.handshake.step ≠ 1 := by omega
    obtain ⟨_, r, -, hrem, -⟩ := readLibp2p_authenticates hr hone
    simp [hrem]

/-- Completion of a produced state after message 3 succeeds. -/
theorem Produced.complete_isOk {s : Libp2pState} (hs : Produced s) (hstep : s.handshake.step = 3) :
    (complete s).isOk := by
  have hsome := hs.remote_isSome (by cases s.handshake.initiator <;> simp [hstep])
  obtain ⟨remote, hr⟩ := Option.isSome_iff_exists.mp hsome
  simp [complete, transport, hstep, hr, (hs.remote_ok hr).1, bind, Except.bind, pure, Except.pure,
    Except.isOk, Except.toBool]

/-- Completion of a produced state returns the transport ciphers of its handshake.

The returned remote has the remote static key of that handshake.

Its signature verifies on that static key, and its public key decodes to its point. -/
theorem Produced.complete_authenticates {s : Libp2pState} {remote : Remote}
    {send receive : CipherState} (hs : Produced s)
    (h : complete s = .ok (remote, send, receive)) :
    transport s.handshake = .ok (send, receive) ∧
      s.handshake.remoteStatic = some remote.staticKey ∧
      Libp2p.verify remote.publicKey (signedStatic remote.staticKey) remote.signature = true ∧
      Libp2p.decodePublicKey remote.publicKey = .ok remote.key := by
  obtain ⟨hrem, -, ht⟩ := complete_ok h
  obtain ⟨h1, h2, h3⟩ := hs.remote_ok hrem
  exact ⟨ht, h1, h2, h3⟩


/-! ## The handshake payload

The payload of noise-libp2p "The libp2p Handshake Payload" is a protobuf message.

Field 1 holds the identity key, field 2 its signature, and field 4 the extension message.

A reader keeps the last value of a singular field, and merges an embedded message by concatenation.

So the reader is not strict: many byte strings decode to one payload.
-/

open EthLib.Networking.Encoding.Protobuf (Record Value valuesOf records)
open EthLib.Networking.Proofs.Encoding.Protobuf (valuesOf_append records_serialize)

/-- The length-delimited values of one field, in the order of the records. -/
def lenValues (rs : List Record) (field : Nat) : List ByteArray :=
  (valuesOf rs field).filterMap fun
    | .len bytes => some bytes
    | _ => none

/-- A record added at the end adds its values at the end. -/
private theorem lenValues_append_singleton (rs : List Record) (r : Record) (field : Nat) :
    lenValues (rs ++ [r]) field = lenValues rs field ++ lenValues [r] field := by
  simp [lenValues, valuesOf_append]

/-- A length-delimited record of the field has its one value. -/
private theorem lenValues_singleton_self (n : Nat) (b : ByteArray) :
    lenValues [⟨n, .len b⟩] n = [b] := by
  simp [lenValues, valuesOf]

/-- A record of another field has no value. -/
private theorem lenValues_singleton_of_ne {f n : Nat} (v : Value) (h : f ≠ n) :
    lenValues [⟨f, v⟩] n = [] := by
  simp [lenValues, valuesOf, h]

/-- The fold of the decoder keeps the last key and signature and joins the extensions. -/
private theorem foldl_payload (rs : List Record) :
    rs.foldl (init := ({} : Payload)) (fun payload record =>
      match record with
      | ⟨1, .len value⟩ => { payload with publicKey := value }
      | ⟨2, .len value⟩ => { payload with signature := value }
      | ⟨4, .len value⟩ =>
        { payload with extensions := some (payload.extensions.getD .empty ++ value) }
      | _ => payload) =
    ⟨(lenValues rs 1).getLast?.getD .empty, (lenValues rs 2).getLast?.getD .empty,
      if lenValues rs 4 = [] then none else some ((lenValues rs 4).foldl (· ++ ·) .empty)⟩ := by
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih =>
    rw [List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, lenValues_append_singleton]
    have hgetD : (if lenValues rs 4 = [] then none
        else some ((lenValues rs 4).foldl (· ++ ·) ByteArray.empty)).getD ByteArray.empty =
        (lenValues rs 4).foldl (· ++ ·) ByteArray.empty := by
      by_cases h : lenValues rs 4 = [] <;> simp [h]
    rcases r with ⟨f, v⟩
    split
    · rename_i heq; simp only [Record.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
      simp [lenValues_singleton_self, lenValues_singleton_of_ne]
    · rename_i heq; simp only [Record.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
      simp [lenValues_singleton_self, lenValues_singleton_of_ne]
    · rename_i heq; simp only [Record.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
      simp [lenValues_singleton_self, lenValues_singleton_of_ne, hgetD]
    · rename_i h1 h2 h4
      have hn : ∀ n, (∀ b, (⟨f, v⟩ : Record) ≠ ⟨n, .len b⟩) → lenValues [⟨f, v⟩] n = [] := by
        intro n hn
        cases v with
        | len b => exact lenValues_singleton_of_ne _ (fun h => hn b (by rw [h]))
        | _ => simp [lenValues, valuesOf]
      rw [hn 1 h1, hn 2 h2, hn 4 h4]
      simp

/-- The decoder accepts exactly the protobuf messages of at most 65535 bytes.

The identity key and the signature are the last length-delimited values of fields 1 and 2.

Each is empty when its field has no such value.

With no such value in field 4 there are no extensions.

Otherwise the extensions are the values of field 4 joined in wire order. -/
theorem decodePayload_eq_ok_iff {bytes : ByteArray} {p : Payload} :
    decodePayload bytes = .ok p ↔ bytes.size ≤ 65535 ∧ ∃ rs, records bytes.data.toList = .ok rs ∧
      p = ⟨(lenValues rs 1).getLast?.getD .empty, (lenValues rs 2).getLast?.getD .empty,
        if lenValues rs 4 = [] then none else some ((lenValues rs 4).foldl (· ++ ·) .empty)⟩ := by
  by_cases hs : 65535 < bytes.size
  · simp [decodePayload, hs, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · cases hr : records bytes.data.toList with
    | error e => simp [decodePayload, hs, hr, bind, Except.bind, Except.mapError]
    | ok rs =>
      have key : decodePayload bytes = .ok ⟨(lenValues rs 1).getLast?.getD .empty,
          (lenValues rs 2).getLast?.getD .empty, if lenValues rs 4 = [] then none
            else some ((lenValues rs 4).foldl (· ++ ·) .empty)⟩ := by
        simp only [decodePayload, hs, hr, ite_false, bind, Except.bind, Except.mapError, pure,
          Except.pure]
        exact congrArg Except.ok (foldl_payload rs)
      rw [key]
      constructor
      · intro h; cases h; exact ⟨by omega, rs, rfl, rfl⟩
      · rintro ⟨-, rs', h, rfl⟩; cases h; rfl

/-- The encoding is the three fields in field order: key, length and bytes for each.

Fields 1 and 2 are always written, and field 4 only when there are extensions.

An encoding longer than 65535 bytes is refused. -/
theorem encodePayload_eq_ok_iff {p : Payload} {bytes : ByteArray} :
    encodePayload p = .ok bytes ↔
      bytes.data.toList =
        0x0a :: Encoding.Varint.encode (UInt64.ofNat p.publicKey.size) ++ p.publicKey.data.toList ++
          0x12 :: Encoding.Varint.encode (UInt64.ofNat p.signature.size) ++
          p.signature.data.toList ++
          p.extensions.toList.flatMap (fun e =>
            0x22 :: Encoding.Varint.encode (UInt64.ofNat e.size) ++ e.data.toList) ∧
        bytes.size ≤ 65535 := by
  have k1 : Encoding.Protobuf.encodeKey 1 2 = [0x0a] := by decide
  have k2 : Encoding.Protobuf.encodeKey 2 2 = [0x12] := by decide
  have k4 : Encoding.Protobuf.encodeKey 4 2 = [0x22] := by decide
  have hb : ∀ l : List UInt8, (Except.ok (⟨l.toArray⟩ : ByteArray) = (.ok bytes :
      Except NoiseError ByteArray)) ↔ bytes.data.toList = l := by
    intro l
    constructor
    · intro h; injection h with h; subst h; rfl
    · intro h; rcases bytes with ⟨d⟩; simp only at h; subst h; rfl
  have hs : bytes.size = bytes.data.toList.length := by rw [Array.length_toList]; rfl
  rcases p with ⟨pk, sig, _ | e⟩
  all_goals
    simp only [encodePayload, Encoding.Protobuf.serialize, Encoding.Protobuf.encodeRecords,
      Encoding.Protobuf.encodeRecord, Encoding.Protobuf.encodeValue,
      Encoding.Protobuf.Value.wireType, List.flatMap_cons, List.flatMap_nil, k1, k2, k4,
      Option.toList, Option.map, Option.getD,
      List.append_nil, List.append_assoc, List.cons_append, List.nil_append]
    split
    · rename_i h1
      simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, reduceCtorEq,
        false_iff, not_and]
      intro h; rw [hs, h]
      simp only [List.length_cons, List.length_append, ByteArray.size, Array.length_toList] at h1 ⊢
      omega
    split
    · rename_i h2
      simp only [pure, Except.pure, hb]
      constructor
      · intro h; refine ⟨h, ?_⟩; rw [hs, h]
        simp only [ByteArray.size, List.size_toArray] at h2; exact h2
      · exact fun h => h.1
    · rename_i h2
      simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq, false_iff, not_and]
      intro h; rw [hs, h]
      simp only [ByteArray.size, List.size_toArray] at h2; exact h2

/-- Decoding an encoded payload returns that payload. -/
theorem decodePayload_encodePayload {p : Payload} {bytes : ByteArray}
    (h : encodePayload p = .ok bytes) : decodePayload bytes = .ok p := by
  rcases p with ⟨pk, sig, _ | e⟩
  all_goals
    simp only [encodePayload] at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    split at h
    · rename_i hs
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      refine decodePayload_eq_ok_iff.mpr ⟨hs, _, records_serialize ?_ (by omega), ?_⟩
      · simp [Encoding.Protobuf.maxField]
      · simp [lenValues, valuesOf]
    · simp [throw, throwThe, MonadExceptOf.throw] at h

end EthLib.Networking.Noise
