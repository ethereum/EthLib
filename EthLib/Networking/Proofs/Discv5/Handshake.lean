module

public import EthLib.Base.Proofs.MapM
public import EthLib.Cryptography.Proofs.Secp256k1.Ecdh
public import EthLib.Cryptography.Proofs.Secp256k1.Encoding
public import EthLib.Networking.Discv5.Handshake
public import EthLib.Networking.Proofs.Discv5.Identity
public import EthLib.Networking.Proofs.Discv5.Packet

/-!
# `Networking.Proofs.Discv5.Handshake`

Node B accepts what node A sends in a handshake, and both sides derive the same session keys.

- The ECDH of the discv5 handshake is symmetric between two multiples of `G`.
- When step 3 succeeds for node A, step 4 succeeds for node B with the keys of node A.
- Step 4 succeeds exactly when the ID signature, the compressed key and the ECDH pass.
- The session keys convert to AES keys byte for byte.
- Node B reads node A's handshake message packet back: the ID, the record, the message, the keys.
- Node B reads a handshake packet exactly when it decodes, step 4 succeeds and the message opens.
- Two errors with one code come from one constructor.

The theorem that step 4 follows step 3 assumes only that step 3 succeeded.

That success already holds the key agreement, the key derivation and the ID signature.

The sealing fails on a packet of more than 1280 bytes, which the decoder rejects.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Discv5.Handshake

open EthLib.Networking.Discv5
open EthLib.Cryptography.Secp256k1
open EthLib.Cryptography.Secp256k1.Point
open EthLib.Networking.Proofs.Discv5.Identity
open EthLib.Networking.Proofs.Discv5.Packet

/-! ## Key agreement -/

/-- A key whose agreement with a multiple of `G` succeeds is not zero. -/
theorem ne_zero_of_ecdh_eq_ok {e b : Fn} {secret : ByteArray}
    (h : Discv5.ecdh e (mul b generator) = .ok secret) : e ≠ 0 := by
  rintro rfl
  -- The multiple `0 P` is `O`, and the agreement rejects it.
  have hzero := EthLib.Cryptography.Secp256k1.mul_zero_left (isOnCurve_mul b isOnCurve_generator)
  unfold Discv5.ecdh at h
  split at h
  · cases h
  split at h
  · cases h
  rw [hzero] at h
  cases h

/-- The agreement of `e` with `b G` gives the secret of `b` with `e G`. -/
theorem ecdh_mul_generator_symm {e b : Fn} {secret : ByteArray}
    (h : Discv5.ecdh e (mul b generator) = .ok secret) :
    Discv5.ecdh b (mul e generator) = .ok secret := by
  have hG := isOnCurve_generator
  have he := Ecdsa.mul_generator_ne_infinity (ne_zero_of_ecdh_eq_ok h)
  unfold Discv5.ecdh at h ⊢
  split at h
  · cases h
  -- Both points are multiples of `G` other than `O`, so only `e (b G) = b (e G)` is left.
  simp only [he, isOnCurve_mul _ hG, Bool.not_true, Bool.false_eq_true, ite_false] at h ⊢
  rw [mul_mul_generator_comm b e]
  exact h

/-! ## The two sides -/

/-- When step 3 succeeds for node A, step 4 succeeds for node B with the same session keys.

Node A has the static key `a`, and node B the static key `b`.

Each side knows the public key of the other, `a G` or `b G`. -/
theorem acceptHandshake_initiateHandshake {e a b : Fn} {challengeData : ByteArray}
    {nodeIdA nodeIdB : NodeId} {init : HandshakeInit}
    (h : initiateHandshake e a challengeData nodeIdA nodeIdB (mul b generator) = .ok init) :
    acceptHandshake b challengeData nodeIdA nodeIdB (mul a generator) init.ephemeralPubkey
      init.idSignature = .ok init.keys := by
  unfold initiateHandshake at h
  cases hs : Discv5.ecdh e (mul b generator) with
  | error err => simp [hs, Except.mapError, bind, Except.bind] at h
  | ok secret =>
    cases hk : deriveKeys secret challengeData nodeIdA nodeIdB with
    | error err => simp [hs, hk, Except.mapError, bind, Except.bind] at h
    | ok keys =>
      cases hsig : idSign a challengeData (mul e generator).encodeCompressed nodeIdB with
      | error err => simp [hs, hk, hsig, Except.mapError, bind, Except.bind] at h
      | ok signature =>
        simp only [hs, hk, hsig, Except.mapError, bind, Except.bind, pure, Except.pure,
          Except.ok.injEq] at h
        subst h
        -- The ephemeral point is a multiple of `G` other than `O`, so it has 33 bytes.
        have hG := isOnCurve_generator
        have hon := isOnCurve_mul e hG
        have hne := Ecdsa.mul_generator_ne_infinity (ne_zero_of_ecdh_eq_ok hs)
        have hsize : (mul e generator).encodeCompressed.size = 33 := by
          cases hm : mul e generator with
          | infinity => exact absurd hm hne
          | affine x y => exact size_encodeCompressed x y
        simp only [acceptHandshake, idVerify_idSign hsig, hsize, decode_encodeCompressed hon hne,
          ecdh_mul_generator_symm hs, hk, Except.mapError, bind, Except.bind, ite_true]

/-! ## What node B accepts -/

/-- When the key agreement with a point succeeds, the point is on the curve and is not `O`. -/
theorem isOnCurve_and_ne_infinity_of_ecdh_eq_ok {sk : Fn} {q : Point} {secret : ByteArray}
    (h : Discv5.ecdh sk q = .ok secret) : q.isOnCurve = true ∧ q ≠ infinity := by
  unfold Discv5.ecdh at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hinf hon
  exact ⟨by simpa using hon, hinf⟩

/-- Step 4 gives node B the keys `keys` exactly when three things hold.

The ID signature verifies under the public key of node A.

The ephemeral public key is the 33-byte compressed encoding of a point `q`.

The agreement of node B's static key with `q` gives a secret, and the keys derive from it. -/
theorem acceptHandshake_eq_ok_iff {sk : Fn} {challengeData : ByteArray}
    {nodeIdA nodeIdB : NodeId} {srcPubkey : Point} {ephemeralPubkey idSignature : ByteArray}
    {keys : SessionKeys} :
    acceptHandshake sk challengeData nodeIdA nodeIdB srcPubkey ephemeralPubkey idSignature =
        .ok keys ↔
      idVerify srcPubkey challengeData ephemeralPubkey nodeIdB idSignature = true ∧
        ∃ q secret, ephemeralPubkey = q.encodeCompressed ∧ Discv5.ecdh sk q = .ok secret ∧
          deriveKeys secret challengeData nodeIdA nodeIdB = .ok keys := by
  by_cases hv : idVerify srcPubkey challengeData ephemeralPubkey nodeIdB idSignature = true
  · by_cases hs : ephemeralPubkey.size = 33
    · simp only [acceptHandshake, hv, hs, true_and, ite_true, EthLib.Base.bind_ok_iff,
        EthLib.Base.mapError_ok_iff]
      constructor
      · rintro ⟨q, hq, secret, he, hk⟩
        -- The 65-byte uncompressed encoding does not have the 33 bytes that the check asks for.
        obtain ⟨-, hinf, hc | hu⟩ := (decode_eq_ok_iff _ _).mp hq
        · exact ⟨q, secret, hc, he, hk⟩
        · cases q with
          | infinity => exact absurd rfl hinf
          | affine x y => rw [hu, size_encodeUncompressed] at hs; cases hs
      · rintro ⟨q, secret, rfl, he, hk⟩
        obtain ⟨hon, hinf⟩ := isOnCurve_and_ne_infinity_of_ecdh_eq_ok he
        exact ⟨q, decode_encodeCompressed hon hinf, secret, he, hk⟩
    · -- A compressed encoding of a point other than `O` has 33 bytes.
      simp only [acceptHandshake, hv, hs, true_and, ite_true, ite_false, throw, throwThe,
        MonadExceptOf.throw, bind, Except.bind, reduceCtorEq, false_iff, not_exists, not_and]
      rintro q secret rfl he -
      cases q with
      | infinity => exact absurd rfl (isOnCurve_and_ne_infinity_of_ecdh_eq_ok he).2
      | affine x y => exact hs (size_encodeCompressed x y)
  · simp [acceptHandshake, hv, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- Node B reads `r` from a handshake message packet exactly when five things hold.

The bytes decode, at node B's ID, to a handshake message packet from `r`'s source ID and record.

Its ID signature verifies under the public key of node A.

Its ephemeral public key is the 33-byte compressed encoding of a point `q`.

The agreement of node B's static key with `q` gives a secret, and `r`'s keys derive from it.

The initiator key of `r` opens the message of the packet to `r`'s plaintext. -/
theorem openHandshake_eq_ok_iff {sk : Fn} {challengeData : ByteArray} {nodeIdB : NodeId}
    {srcPubkey : Point} {bytes : ByteArray} {r : HandshakeReceived} :
    openHandshake sk challengeData nodeIdB srcPubkey bytes = .ok r ↔
      ∃ packet idSignature q secret, Packet.decode nodeIdB bytes = .ok packet ∧
        packet.header.authdata = .handshake r.srcId idSignature q.encodeCompressed r.record ∧
        idVerify srcPubkey challengeData q.encodeCompressed nodeIdB idSignature = true ∧
        Discv5.ecdh sk q = .ok secret ∧
        deriveKeys secret challengeData r.srcId nodeIdB = .ok r.keys ∧
        openPacket HandshakeError.packet HandshakeError.decryption (sessionKey r.keys.initiatorKey)
          packet = .ok r.message := by
  constructor
  · intro h
    simp only [openHandshake, EthLib.Base.bind_ok_iff, EthLib.Base.mapError_ok_iff] at h
    obtain ⟨packet, hp, h⟩ := h
    cases ha : packet.header.authdata with
    | message _ => simp [ha, throw, throwThe, MonadExceptOf.throw] at h
    | whoareyou _ _ => simp [ha, throw, throwThe, MonadExceptOf.throw] at h
    | handshake srcId idSignature ephemeralPubkey record =>
      simp only [ha, EthLib.Base.bind_ok_iff, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨keys, hk, message, ho, rfl⟩ := h
      obtain ⟨hv, q, secret, rfl, he, hd⟩ := acceptHandshake_eq_ok_iff.mp hk
      exact ⟨packet, idSignature, q, secret, hp, ha, hv, he, hd, ho⟩
  · rintro ⟨packet, idSignature, q, secret, hp, ha, hv, he, hd, ho⟩
    have hk := acceptHandshake_eq_ok_iff.mpr ⟨hv, q, secret, rfl, he, hd⟩
    cases r
    simp only [openHandshake, hp, ha, hk, ho, Except.mapError, bind, Except.bind, pure,
      Except.pure]

/-! ## The handshake message packet -/

/-- A key of 16 bytes converts to the AES key of those bytes. -/
theorem toArray_sessionKey {key : ByteArray} (h : key.size = 16) :
    (sessionKey key).toArray = key.data := by
  apply Array.ext
  · simp only [sessionKey, Vector.toArray_ofFn, Array.size_ofFn]
    exact h.symm
  · intro i h₁ h₂
    simp only [sessionKey, Vector.toArray_ofFn, Array.getElem_ofFn, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem h₂, Option.getD_some]

/-- The two session keys that the derivation gives convert to AES keys byte for byte. -/
theorem toArray_sessionKey_of_deriveKeys {secret challengeData : ByteArray}
    {nodeIdA nodeIdB : NodeId} {keys : SessionKeys}
    (h : deriveKeys secret challengeData nodeIdA nodeIdB = .ok keys) :
    (sessionKey keys.initiatorKey).toArray = keys.initiatorKey.data ∧
      (sessionKey keys.recipientKey).toArray = keys.recipientKey.data := by
  obtain ⟨keys', hk, hi, hr⟩ := deriveKeys_ok secret challengeData nodeIdA nodeIdB
  rw [h, Except.ok.injEq] at hk
  subst hk
  exact ⟨toArray_sessionKey hi, toArray_sessionKey hr⟩

/-- Node B reads node A's handshake message packet back.

It gets the node ID and the record of node A, the plaintext, and the session keys of node A.

The record is any byte string, empty when node A leaves it out.

The theorem does not authenticate the record: node B takes the public key of node A as an input. -/
theorem openHandshake_sealHandshake {e a b : Fn} {challengeData : ByteArray}
    {nodeIdA nodeIdB : NodeId} {maskingIv : Vector UInt8 16} {nonce : Vector UInt8 12}
    {record plaintext bytes : ByteArray} {keys : SessionKeys}
    (h : sealHandshake e a challengeData nodeIdA nodeIdB (mul b generator) maskingIv nonce record
      plaintext = .ok (bytes, keys)) :
    openHandshake b challengeData nodeIdB (mul a generator) bytes =
      .ok ⟨nodeIdA, record, plaintext, keys⟩ := by
  unfold sealHandshake at h
  cases hi : initiateHandshake e a challengeData nodeIdA nodeIdB (mul b generator) with
  | error err => simp [hi, bind, Except.bind] at h
  | ok init =>
    simp only [hi, bind, Except.bind] at h
    cases hs : sealPacket HandshakeError.packet HandshakeError.encryption
      (sessionKey init.keys.initiatorKey) nodeIdB maskingIv
      ⟨nonce, .handshake nodeIdA init.idSignature init.ephemeralPubkey record⟩ plaintext with
    | error err => simp [hs] at h
    | ok packetBytes =>
      simp only [hs, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      -- The packet decodes back, since its flag is 2 and not that of WHOAREYOU.
      obtain ⟨message, hdec, hopen⟩ := openPacket_sealPacket
        (decryptionError := HandshakeError.decryption) hs (by simp [Authdata.flag])
      simp only [openHandshake, hdec, acceptHandshake_initiateHandshake hi, hopen,
        Except.mapError, bind, Except.bind, pure, Except.pure]

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Networking.Discv5.HandshakeError.code_injective
    (e₁ e₂ : HandshakeError) (h : e₁.code = e₂.code) : e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [HandshakeError.code] at h; exact absurd h (by decide))

end EthLib.Networking.Proofs.Discv5.Handshake
