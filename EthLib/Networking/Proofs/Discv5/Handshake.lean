module

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
- The session keys convert to AES keys byte for byte.
- Node B reads node A's handshake message packet back: the ID, the record, the message, the keys.
- Two errors with one code come from one constructor.

The theorem on step 4 assumes only that step 3 succeeded.

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
    generalize hheader : (⟨nonce, .handshake nodeIdA init.idSignature init.ephemeralPubkey
      record⟩ : Header) = header at h
    cases ha : Packet.messageAd ⟨maskingIv, header, .empty⟩ with
    | error err => simp [ha, Except.mapError] at h
    | ok ad =>
      simp only [ha, Except.mapError] at h
      cases hm : encryptMessage (sessionKey init.keys.initiatorKey) nonce plaintext ad with
      | error err => simp [hm] at h
      | ok message =>
        simp only [hm] at h
        cases hb : Packet.encode nodeIdB ⟨maskingIv, header, message⟩ with
        | error err => simp [hb] at h
        | ok packetBytes =>
          simp only [hb, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          -- The packet decodes back, since its flag is 2 and not that of WHOAREYOU.
          have hdec := Packet.decode_encode hb (by
            intro hflag
            rw [← hheader] at hflag
            simp [Authdata.flag] at hflag)
          -- The additional data depends only on the masking IV and the header.
          have had : Packet.messageAd ⟨maskingIv, header, message⟩ = .ok ad := by
            simpa [Packet.messageAd] using ha
          subst hheader
          simp only [openHandshake, hdec, acceptHandshake_initiateHandshake hi, had,
            decryptMessage_encryptMessage hm, Except.mapError, bind, Except.bind, pure,
            Except.pure]

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Networking.Discv5.HandshakeError.code_injective
    (e₁ e₂ : HandshakeError) (h : e₁.code = e₂.code) : e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [HandshakeError.code] at h; exact absurd h (by decide))

end EthLib.Networking.Proofs.Discv5.Handshake
