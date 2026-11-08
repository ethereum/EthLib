module

public import EthLib.Networking.Rlpx.Handshake
public import EthLib.Networking.Proofs.Rlpx.Ecies
public import EthLib.Cryptography.Proofs.Secp256k1.Sign
public import EthLib.Serialization.Proofs.Rlp.Codec

/-!
# Proofs: the RLPx handshake

An honest initiator and an honest recipient derive the same secrets.

Each reading step accepts only public keys on the curve other than `O`.

A reader of `auth` or `ack` ignores the list items after the fields it knows, as EIP-8 asks.

Each side's egress MAC state is the other side's ingress MAC state.

Two errors with one code come from one constructor.
-/

@[expose] public section

namespace EthLib.Networking.Rlpx

open EthLib.Base (xorBytes)
open EthLib.Cryptography
open EthLib.Cryptography.Secp256k1
open EthLib.Cryptography.Secp256k1.Point
open EthLib.Serialization.Rlp

/-! ## Keys and signatures -/

/-- The 64 bytes of a public key decode to the key. -/
theorem decodePublicKey_encodePublicKey {p : Point} (hp : p.isOnCurve = true)
    (hinf : p ≠ .infinity) : decodePublicKey (encodePublicKey p) = .ok p := by
  cases p with
  | infinity => exact absurd rfl hinf
  | affine x y =>
    have h := decode_encodeUncompressed hp hinf
    simp only [decodePublicKey, encodePublicKey, Except.mapError]
    simp only [encodeUncompressed] at h
    have he : (⟨#[0x04] ++ (x.toBytes ++ y.toBytes).toArray⟩ : ByteArray) =
        ⟨(0x04 :: x.toBytes ++ y.toBytes).toArray⟩ := by
      simp
    rw [he, h]

/-- 64 bytes decode to a key exactly when it is on the curve, not `O`, and has those bytes. -/
theorem decodePublicKey_eq_ok_iff {bytes : Vector UInt8 64} {p : Point} :
    decodePublicKey bytes = .ok p ↔
      p.isOnCurve = true ∧ p ≠ .infinity ∧ encodePublicKey p = bytes := by
  constructor
  · intro h
    unfold decodePublicKey at h
    cases hd : Point.decode ⟨#[0x04] ++ bytes.toArray⟩ with
    | error e => simp [hd, Except.mapError] at h
    | ok q =>
      simp only [hd, Except.mapError, Except.ok.injEq] at h
      subst h
      obtain ⟨hon, hinf, hform⟩ := (Point.decode_eq_ok_iff _ _).mp hd
      refine ⟨hon, hinf, ?_⟩
      cases q with
      | infinity => exact absurd rfl hinf
      | affine x y =>
        rcases hform with hcomp | hunc
        · have hsize := congrArg ByteArray.size hcomp
          rw [size_encodeCompressed] at hsize
          simp [ByteArray.size] at hsize
        · have hlist := congrArg (fun b : ByteArray => b.data.toList) hunc
          simp only [encodeUncompressed, Array.toList_append] at hlist
          have htail : bytes.toList = x.toBytes ++ y.toBytes := List.cons.inj hlist |>.2
          exact Vector.toList_inj.mp (by simpa [encodePublicKey] using htail.symm)
  · rintro ⟨hon, hinf, rfl⟩
    exact decodePublicKey_encodePublicKey hon hinf

/-- A recovered signer key lies on the curve and is not `O`. -/
theorem isOnCurve_of_recoverSigner {hash : Vector UInt8 32} {sig : Vector UInt8 65} {p : Point}
    (h : recoverSigner hash sig = .ok p) :
    p.isOnCurve = true ∧ p ≠ .infinity := by
  unfold recoverSigner at h
  dsimp only at h
  split at h
  · rename_i hv
    cases hr : Ecdsa.recover hash (Base.bytesToNat (sig.toList.take 32))
        (Base.bytesToNat ((sig.toList.drop 32).take 32)) ⟨sig[64].toNat, hv⟩ with
    | error e => simp [hr, Except.mapError] at h
    | ok q =>
      simp only [hr, Except.mapError, Except.ok.injEq] at h
      subst h
      exact Ecdsa.recover_valid hr
  · cases h

/-- Recovery from the bytes of a signature from signing returns the signer's key. -/
theorem recoverSigner_signatureBytes {sk : Fn} {hash : Vector UInt8 32} {sig : Fn × Fn × Bool}
    (h : Ecdsa.sign sk hash = .ok sig) :
    recoverSigner hash (signatureBytes sig) = .ok (mul sk generator) := by
  obtain ⟨r, s, odd⟩ := sig
  have hrec := Ecdsa.recover_sign_rfc6979 h
  have hlr := Base.natToBytes_length 32 r.val
  have hls := Base.natToBytes_length 32 s.val
  have hmod (x : Fn) : x.val % 256 ^ 32 = x.val :=
    Nat.mod_eq_of_lt (lt_trans x.isLt (by decide : Fn.modulus < 256 ^ 32))
  unfold recoverSigner signatureBytes
  cases odd <;>
    simp only [Vector.toList, List.take_left' hlr, List.append_assoc,
      List.drop_left' hlr, List.take_left' hls, Base.bytesToNat_natToBytes, hmod] <;>
    (simp only [Bool.false_eq_true, ite_false, ite_true] at hrec
     simp [hlr, hls, Except.mapError, hrec])

/-! ## Packets -/

/-- The recipient of a packet opens it to the body and the padding. -/
theorem openPacket_sealPacket {key r : Fn} {iv : Aes.Block} {body padding packet : ByteArray}
    (h : sealPacket (mul key generator) r iv body padding = .ok packet) :
    openPacket key packet = .ok (body ++ padding) := by
  unfold sealPacket at h
  by_cases hsize : 65536 ≤ body.size + padding.size + Ecies.OVERHEAD
  · simp [hsize, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · cases hc : Ecies.encrypt (mul key generator) r iv
        (sizeBytes (body.size + padding.size + Ecies.OVERHEAD)) (body ++ padding) with
    | error e => simp [hsize, hc, Except.mapError, bind, Except.bind] at h
    | ok c =>
      simp only [hsize, hc, Except.mapError, bind, Except.bind, pure, Except.pure, ite_false,
        Except.ok.injEq] at h
      subst h
      have hlen := Ecies.size_encrypt hc
      rw [ByteArray.size_append] at hlen
      generalize hn : body.size + padding.size + Ecies.OVERHEAD = n at hsize hc hlen
      -- The two bytes of the size read back as the size.
      have hread : n / 256 % 256 * 256 + n % 256 = n := by omega
      have hrest : c.data.toList.length = n := hlen
      have hopen : openPacket key (sizeBytes n ++ c) =
          (Ecies.decrypt key (sizeBytes n) c).mapError .ecies := by
        simp only [openPacket, sizeBytes, ByteArray.data_append, Array.toList_append]
        simp [hread, hrest]
      rw [hopen, Ecies.decrypt_encrypt hc]
      rfl

/-- An opened packet starts, after its size, with an uncompressed key `R` on the curve, not `O`. -/
theorem ephemeral_of_openPacket {key : Fn} {packet body : ByteArray}
    (h : openPacket key packet = .ok body) :
    key ≠ 0 ∧ ∃ R : Point,
      Point.decode ⟨((packet.data.toList.drop 2).take Ecies.EPHEMERAL_KEY_SIZE).toArray⟩ = .ok R ∧
      R.isOnCurve = true ∧ R ≠ .infinity ∧
      ⟨((packet.data.toList.drop 2).take Ecies.EPHEMERAL_KEY_SIZE).toArray⟩ =
        R.encodeUncompressed := by
  unfold openPacket at h
  cases hl : packet.data.toList with
  | nil => rw [hl] at h; cases h
  | cons hi tail =>
    cases tail with
    | nil => rw [hl] at h; cases h
    | cons lo rest =>
      rw [hl] at h
      dsimp only at h
      split at h
      · cases hd : Ecies.decrypt key ⟨#[hi, lo]⟩ ⟨rest.toArray⟩ with
        | error e => simp [hd, Except.mapError] at h
        | ok plain =>
          simpa using Ecies.ephemeral_of_decrypt_eq_ok hd
      · cases h

/-! ## Messages -/

/-- A message decodes from the start of a body, whatever padding follows it. -/
theorem decodeBody_encode {α : Type} [Codec α] {m : α}
    (hm : Codec.ofItem (Codec.toItem m) = .ok m) {body : ByteArray} (h : Codec.encode m = .ok body)
    (padding : ByteArray) : decodeBody (body ++ padding) = .ok m := by
  obtain ⟨hNext, hd⟩ := decodeItem_encode _ _ h (input := body ++ padding) (pos := 0)
    (rest := padding.data.toList) (Nat.le_refl _)
    (by rw [ByteArray.extract_zero_size, ByteArray.toList_data_append])
  unfold decodeBody
  simp only [bind, Except.bind, hd, hm, Except.mapError]

/-- `auth` reads back from its RLP item. -/
theorem AuthMessage.ofItem_toItem (m : AuthMessage) :
    Codec.ofItem (Codec.toItem m) = .ok m := by
  simp [Codec.toItem, Codec.ofItem, leadingFields, Item.toItems, Item.toBytes, ByteArray.size,
    toScalar_scalar, bind, Except.bind, pure, Except.pure]

/-- `ack` reads back from its RLP item. -/
theorem AckMessage.ofItem_toItem (m : AckMessage) :
    Codec.ofItem (Codec.toItem m) = .ok m := by
  simp [Codec.toItem, Codec.ofItem, leadingFields, Item.toItems, Item.toBytes, ByteArray.size,
    toScalar_scalar, bind, Except.bind, pure, Except.pure]

/-! ## Further list items -/

/-- A list of at least `count` items gives the same leading fields, whatever items follow. -/
theorem leadingFields_append {count : Nat} {fields : List Item} (extra : List Item)
    (h : count ≤ fields.length) :
    leadingFields count (.list (fields ++ extra)) = leadingFields count (.list fields) := by
  simp [leadingFields, Item.toItems, bind, Except.bind, h, Nat.le_add_right_of_le h,
    List.take_append_of_le_length h]

/-- `auth` reads the same from four or more items, whatever items follow them, as EIP-8 asks. -/
theorem AuthMessage.ofItem_append {fields : List Item} (extra : List Item)
    (h : 4 ≤ fields.length) :
    (Codec.ofItem (.list (fields ++ extra)) : Except RlpError AuthMessage) =
      Codec.ofItem (.list fields) := by
  simp only [Codec.ofItem, leadingFields_append extra h]

/-- `ack` reads the same from three or more items, whatever items follow them, as EIP-8 asks. -/
theorem AckMessage.ofItem_append {fields : List Item} (extra : List Item)
    (h : 3 ≤ fields.length) :
    (Codec.ofItem (.list (fields ++ extra)) : Except RlpError AckMessage) =
      Codec.ofItem (.list fields) := by
  simp only [Codec.ofItem, leadingFields_append extra h]

/-! ## The two sides -/

/-- An `auth` that the initiator made: its signature, its body and its packet. -/
theorem makeAuth_eq_ok {keys : Keys} {recipient : Point} {sealing : Sealing} {auth : ByteArray}
    (h : makeAuth keys recipient sealing = .ok auth) :
    ∃ shared sig body, ecdh keys.staticKey recipient = .ok shared ∧
      Ecdsa.sign keys.ephemeralKey (xorBytes shared keys.nonce) = .ok sig ∧
      Codec.encode (⟨signatureBytes sig, encodePublicKey (mul keys.staticKey generator), keys.nonce,
        HANDSHAKE_VERSION⟩ : AuthMessage) = .ok body ∧
      sealPacket recipient sealing.r sealing.iv body sealing.padding = .ok auth := by
  unfold makeAuth at h
  cases hs : ecdh keys.staticKey recipient with
  | error e => simp [hs, Except.mapError, bind, Except.bind] at h
  | ok shared =>
  cases hg : Ecdsa.sign keys.ephemeralKey (xorBytes shared keys.nonce) with
  | error e => simp [hs, hg, Except.mapError, bind, Except.bind] at h
  | ok sig =>
  cases hb : Codec.encode (⟨signatureBytes sig, encodePublicKey (mul keys.staticKey generator),
      keys.nonce, HANDSHAKE_VERSION⟩ : AuthMessage) with
  | error e => simp [hs, hg, hb, Except.mapError, bind, Except.bind] at h
  | ok body =>
  simp only [hs, hg, hb, Except.mapError, bind, Except.bind] at h
  exact ⟨shared, sig, body, rfl, hg, hb, h⟩

/-- An `ack` that the recipient made: its body and its packet. -/
theorem makeAck_eq_ok {keys : Keys} {initiator : Point} {sealing : Sealing} {ack : ByteArray}
    (h : makeAck keys initiator sealing = .ok ack) :
    ∃ body, Codec.encode (⟨encodePublicKey (mul keys.ephemeralKey generator), keys.nonce,
        HANDSHAKE_VERSION⟩ : AckMessage) = .ok body ∧
      sealPacket initiator sealing.r sealing.iv body sealing.padding = .ok ack := by
  unfold makeAck at h
  cases hb : Codec.encode (⟨encodePublicKey (mul keys.ephemeralKey generator), keys.nonce,
      HANDSHAKE_VERSION⟩ : AckMessage) with
  | error e => simp [hb, Except.mapError, bind, Except.bind] at h
  | ok body =>
  simp only [hb, Except.mapError, bind, Except.bind] at h
  exact ⟨body, rfl, h⟩

/--
The recipient reads an honest `auth`.

It learns the initiator's static key, and the ephemeral key that the signature names.
-/
theorem readAuth_makeAuth {keys : Keys} {staticKey : Fn} {sealing : Sealing} {auth : ByteArray}
    (h : makeAuth keys (mul staticKey generator) sealing = .ok auth) :
    ∃ msg, msg.initiatorNonce = keys.nonce ∧ readAuth staticKey auth =
      .ok (msg, mul keys.staticKey generator, mul keys.ephemeralKey generator) := by
  obtain ⟨shared, sig, body, hs, hg, hb, hp⟩ := makeAuth_eq_ok h
  have hG := isOnCurve_generator
  refine ⟨⟨signatureBytes sig, encodePublicKey (mul keys.staticKey generator), keys.nonce,
    HANDSHAKE_VERSION⟩, rfl, ?_⟩
  unfold readAuth
  rw [openPacket_sealPacket hp]
  simp only [bind, Except.bind]
  rw [decodeBody_encode (AuthMessage.ofItem_toItem _) hb]
  simp only
  rw [decodePublicKey_encodePublicKey (isOnCurve_mul _ hG)
    (Ecies.ephemeral_ne_infinity hs)]
  simp only [ecdh_comm staticKey keys.staticKey, hs, Except.mapError]
  rw [recoverSigner_signatureBytes hg]
  rfl

/--
An honest initiator and an honest recipient derive the same secrets.

The initiator's secrets are the recipient's, with the two MAC states swapped.

So each side's egress MAC state is the other side's ingress MAC state.
-/
theorem finish_respond {initiator recipient : Keys} {sealingI sealingR : Sealing}
    {auth ack : ByteArray} {secrets : Secrets}
    (hauth : makeAuth initiator (mul recipient.staticKey generator) sealingI = .ok auth)
    (hresp : respond recipient sealingR auth = .ok (ack, secrets)) :
    finish initiator auth ack =
      .ok { secrets with egressMac := secrets.ingressMac, ingressMac := secrets.egressMac } := by
  have hG := isOnCurve_generator
  obtain ⟨msg, hnonce, hread⟩ := readAuth_makeAuth hauth
  unfold respond at hresp
  rw [hread] at hresp
  simp only [bind, Except.bind] at hresp
  cases hk : makeAck recipient (mul initiator.staticKey generator) sealingR with
  | error e => simp [hk] at hresp
  | ok ack' =>
  cases he : ecdh recipient.ephemeralKey (mul initiator.ephemeralKey generator) with
  | error e => simp [hk, he, Except.mapError] at hresp
  | ok shared =>
  simp only [hk, he, Except.mapError, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hresp
  obtain ⟨rfl, rfl⟩ := hresp
  obtain ⟨body, hb, hp⟩ := makeAck_eq_ok hk
  unfold finish readAck
  rw [openPacket_sealPacket hp]
  simp only [bind, Except.bind]
  rw [decodeBody_encode (AckMessage.ofItem_toItem _) hb]
  simp only
  rw [decodePublicKey_encodePublicKey (isOnCurve_mul _ hG)
    (Ecies.ephemeral_ne_infinity he)]
  simp only [ecdh_comm initiator.ephemeralKey recipient.ephemeralKey, he, Except.mapError, pure,
    Except.pure, hnonce]
  rfl

/-- Reading `auth` returns two initiator keys on the curve other than `O`. -/
theorem isOnCurve_of_readAuth {staticKey : Fn} {packet : ByteArray}
    {auth : AuthMessage} {remoteStatic remoteEphemeral : Point}
    (h : readAuth staticKey packet = .ok (auth, remoteStatic, remoteEphemeral)) :
    remoteStatic.isOnCurve = true ∧ remoteStatic ≠ .infinity ∧
      remoteEphemeral.isOnCurve = true ∧ remoteEphemeral ≠ .infinity := by
  unfold readAuth at h
  cases ho : openPacket staticKey packet with
  | error e => simp [ho, bind, Except.bind] at h
  | ok body =>
  cases hb : (decodeBody body : Except HandshakeError AuthMessage) with
  | error e => simp [ho, hb, bind, Except.bind] at h
  | ok msg =>
  cases hk : decodePublicKey msg.initiatorPubkey with
  | error e => simp [ho, hb, hk, bind, Except.bind] at h
  | ok staticPt =>
  cases hs : ecdh staticKey staticPt with
  | error e => simp [ho, hb, hk, hs, Except.mapError, bind, Except.bind] at h
  | ok shared =>
  cases hr : recoverSigner (xorBytes shared msg.initiatorNonce) msg.signature with
  | error e => simp [ho, hb, hk, hs, hr, Except.mapError, bind, Except.bind] at h
  | ok ephPt =>
  simp only [ho, hb, hk, hs, hr, Except.mapError, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  obtain ⟨hsOn, hsInf, -⟩ := decodePublicKey_eq_ok_iff.mp hk
  obtain ⟨heOn, heInf⟩ := isOnCurve_of_recoverSigner hr
  exact ⟨hsOn, hsInf, heOn, heInf⟩

/-- Reading `ack` returns a recipient ephemeral key on the curve other than `O`. -/
theorem isOnCurve_of_readAck {staticKey : Fn} {packet : ByteArray}
    {ack : AckMessage} {remoteEphemeral : Point}
    (h : readAck staticKey packet = .ok (ack, remoteEphemeral)) :
    remoteEphemeral.isOnCurve = true ∧ remoteEphemeral ≠ .infinity := by
  unfold readAck at h
  cases ho : openPacket staticKey packet with
  | error e => simp [ho, bind, Except.bind] at h
  | ok body =>
  cases hb : (decodeBody body : Except HandshakeError AckMessage) with
  | error e => simp [ho, hb, bind, Except.bind] at h
  | ok msg =>
  cases hk : decodePublicKey msg.ephemeralPubkey with
  | error e => simp [ho, hb, hk, bind, Except.bind] at h
  | ok ephPt =>
  simp only [ho, hb, hk, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨heOn, heInf, -⟩ := decodePublicKey_eq_ok_iff.mp hk
  exact ⟨heOn, heInf⟩

/-- Answering `auth` reads an `auth` with both initiator keys on the curve other than `O`. -/
theorem exists_readAuth_of_respond {keys : Keys} {sealing : Sealing} {auth ack : ByteArray}
    {secrets : Secrets} (h : respond keys sealing auth = .ok (ack, secrets)) :
    ∃ msg remoteStatic remoteEphemeral,
      readAuth keys.staticKey auth = .ok (msg, remoteStatic, remoteEphemeral) ∧
      remoteStatic.isOnCurve = true ∧ remoteStatic ≠ .infinity ∧
      remoteEphemeral.isOnCurve = true ∧ remoteEphemeral ≠ .infinity := by
  unfold respond at h
  cases hr : readAuth keys.staticKey auth with
  | error e => simp [hr, bind, Except.bind] at h
  | ok triple =>
    rcases triple with ⟨msg, remoteStatic, remoteEphemeral⟩
    obtain ⟨hsOn, hsInf, heOn, heInf⟩ := isOnCurve_of_readAuth hr
    exact ⟨msg, remoteStatic, remoteEphemeral, rfl, hsOn, hsInf, heOn, heInf⟩

/-- Finishing the handshake reads an `ack` with an ephemeral key on the curve other than `O`. -/
theorem exists_readAck_of_finish {keys : Keys} {auth ack : ByteArray} {secrets : Secrets}
    (h : finish keys auth ack = .ok secrets) :
    ∃ msg remoteEphemeral,
      readAck keys.staticKey ack = .ok (msg, remoteEphemeral) ∧
      remoteEphemeral.isOnCurve = true ∧ remoteEphemeral ≠ .infinity := by
  unfold finish at h
  cases hr : readAck keys.staticKey ack with
  | error e => simp [hr, bind, Except.bind] at h
  | ok pair =>
    rcases pair with ⟨msg, remoteEphemeral⟩
    obtain ⟨heOn, heInf⟩ := isOnCurve_of_readAck hr
    exact ⟨msg, remoteEphemeral, rfl, heOn, heInf⟩

/-! ## Error codes -/

/-- An ECIES error never has a code above 5. -/
private theorem ecies_code_ne (e : Ecies.EciesError) (n : UInt32) (hn : 5 < n.toNat) :
    e.code ≠ n := by
  intro h
  have := (Ecies.EciesError.code_le e).2
  rw [h] at this
  omega

/-- Two errors with one code come from one constructor. -/
theorem HandshakeError.code_injective (e₁ e₂ : HandshakeError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- The codes from 101 are distinct literals, and an ECIES code is at most 5.
  cases e₁ <;> cases e₂ <;> simp only [HandshakeError.code] at h <;> first
    | rfl
    | exact absurd h (by decide)
    | exact absurd h (ecies_code_ne _ _ (by decide))
    | exact absurd h.symm (ecies_code_ne _ _ (by decide))

end EthLib.Networking.Rlpx
