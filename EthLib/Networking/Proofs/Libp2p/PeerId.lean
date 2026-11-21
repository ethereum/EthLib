module

public import EthLib.Base.Proofs.BigEndian
public import EthLib.Serialization.Proofs.Der
public import EthLib.Networking.Libp2p.PeerId
public import EthLib.Cryptography.Proofs.Secp256k1.Encoding
public import EthLib.Cryptography.Proofs.Secp256k1.Sign

/-!
# Proofs: libp2p secp256k1 public keys, peer IDs and DER signatures

- A point of the curve, other than infinity, encodes to a key protobuf that decodes back to it.
- A peer ID decodes back to its key, and the decoder accepts only peer IDs of keys.
- Two different points of the curve have two different peer IDs.
- A decoded key's peer ID is the two bytes `00 25`, then the key protobuf.
- The signature decoder accepts exactly the encodings of r and low s in range, and returns them.
- A signature that the identity secret makes verifies under the key protobuf of that secret.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Libp2p.PeerId

open EthLib.Base
open EthLib.Cryptography.Secp256k1
open EthLib.Networking.Libp2p
open EthLib.Serialization.Der
open EthLib.Serialization.Proofs.Der

/-- A point of the curve, other than infinity, encodes to a key protobuf that decodes back to it. -/
theorem decodePublicKey_encodePublicKey {point : Point} (hcurve : point.isOnCurve = true)
    (hinf : point ≠ .infinity) : decodePublicKey (encodePublicKey point) = .ok point := by
  cases point with
  | infinity => exact absurd rfl hinf
  | affine x y =>
    have hsize : (encodePublicKey (.affine x y)).size = 37 := by
      simp [encodePublicKey, ByteArray.size_append, Point.size_encodeCompressed]
      rfl
    have hext :
        (encodePublicKey (.affine x y)).extract 4 37 = (Point.affine x y).encodeCompressed :=
      ByteArray.extract_append_eq_right (by rfl) (by rw [← hsize]; rfl)
    simp [decodePublicKey, hsize, hext, Point.decode_encodeCompressed hcurve hinf,
      Except.mapError, bind, Except.bind, pure, Except.pure]

/-- A decoded key protobuf is the encoding of the point it decodes to. -/
theorem encodePublicKey_of_decodePublicKey {key : ByteArray} {point : Point}
    (h : decodePublicKey key = .ok point) : encodePublicKey point = key := by
  unfold decodePublicKey at h
  by_cases hs : (key.size != 37) = true
  · simp [hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · cases hd : Point.decode (key.extract 4 37) with
    | error e => simp [hs, hd, Except.mapError, bind, Except.bind] at h
    | ok q =>
      by_cases he : encodePublicKey q = key
      · simp [hs, hd, he, Except.mapError, bind, Except.bind, pure, Except.pure] at h
        subst h; exact he
      · simp [hs, hd, he, Except.mapError, bind, Except.bind] at h

/-- The peer ID of a point of the curve, other than infinity, decodes back to that point. -/
theorem decodePeerId_peerId {point : Point} (hcurve : point.isOnCurve = true)
    (hinf : point ≠ .infinity) : decodePeerId (peerId point) = .ok point := by
  simp [peerId, decodePeerId, ByteArray.data_append, Array.toList_append,
    decodePublicKey_encodePublicKey hcurve hinf]

/-- A peer ID that decodes is the peer ID of the point it decodes to. -/
theorem peerId_of_decodePeerId {id : ByteArray} {point : Point}
    (h : decodePeerId id = .ok point) : peerId point = id := by
  unfold decodePeerId at h
  split at h
  · rename_i key hl
    have hk := encodePublicKey_of_decodePublicKey h
    rw [peerId, hk]
    apply ByteArray.ext
    simp [ByteArray.data_append]
    apply Array.ext'
    simp [hl]
  · simp at h

/-- Two points of the curve with one peer ID are one point.

Infinity has a shorter peer ID than any other point, and the others decode back. -/
theorem peerId_injective {p q : Point} (hp : p.isOnCurve = true) (hq : q.isOnCurve = true)
    (h : peerId p = peerId q) : p = q := by
  rcases p with _ | ⟨x, y⟩ <;> rcases q with _ | ⟨x', y'⟩
  · rfl
  · have := congrArg ByteArray.size h
    simp [peerId, encodePublicKey, ByteArray.size_append, Point.size_encodeCompressed] at this
    exact absurd this (by decide)
  · have := congrArg ByteArray.size h
    simp [peerId, encodePublicKey, ByteArray.size_append, Point.size_encodeCompressed] at this
    exact absurd this (by decide)
  · have hd := decodePeerId_peerId hp (by simp)
    rw [h, decodePeerId_peerId hq (by simp)] at hd
    exact (Except.ok.inj hd).symm

/-- The peer ID of a decoded key is the two bytes `00 25`, then the key protobuf. -/
theorem peerId_of_decodePublicKey {key : ByteArray} {point : Point}
    (h : decodePublicKey key = .ok point) : peerId point = ⟨#[0x00, 0x25]⟩ ++ key := by
  rw [peerId, encodePublicKey_of_decodePublicKey h]

/-- The decoder accepts exactly the encodings of r in [1, N) and s in [1, N/2], BIP 62.

Here N is the order of the secp256k1 group, and N/2 rounds down.

The decoder returns those r and s, so each accepted pair has exactly one byte encoding. -/
theorem decodeSignature_eq_ok_iff {signature : ByteArray} {r s : Nat} :
    decodeSignature signature = .ok (r, s) ↔
      0 < r ∧ r < Fn.modulus ∧ 0 < s ∧ s ≤ Fn.modulus / 2 ∧
        encodeEcdsaSignature r s = signature := by
  have hN : Fn.modulus < 2 ^ 256 := by decide
  unfold decodeSignature
  constructor
  · intro h
    split at h
    · rename_i r' s' hd
      obtain ⟨hr, -, hs, -, he⟩ := decodeEcdsaScalars_eq_some_iff.mp hd
      split at h
      · rename_i hc
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hr, hc.1, hs, hc.2, he⟩
      · simp at h
    · simp at h
  · rintro ⟨hr, hrn, hs, hsn, he⟩
    have hd := decodeEcdsaScalars_eq_some_iff.mpr ⟨hr, by omega, hs, by omega, he⟩
    simp [hd, hrn, hsn]

/-- A signature that a secret makes verifies under the key protobuf of that secret.

Signing returns a low s, so the strict DER decoder accepts the signature it encodes. -/
theorem verify_sign {k : Fn} {message signature : ByteArray} (h : sign k message = .ok signature) :
    verify (encodePublicKey (Point.mul k .generator)) message signature = true := by
  have hk : k ≠ 0 := by
    rintro rfl
    simp [sign, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  unfold sign at h
  simp only [hk, ite_false] at h
  generalize hs : Ecdsa.sign k (EthLib.Cryptography.Hash.Sha256.hash32 message) = w at h
  match w, h with
  | .ok (r, s, odd), h =>
    simp only [Except.mapError, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at h
    subst h
    have hv := Ecdsa.verify_sign_rfc6979 hs
    obtain ⟨-, hr, hs0⟩ := Ecdsa.sign_ne_zero hs
    have hlow := Ecdsa.isLowS_sign hs
    have hcurve := Point.isOnCurve_mul k Point.isOnCurve_generator
    have hdec := decodeSignature_eq_ok_iff (signature := encodeEcdsaSignature r.val s.val)
      (r := r.val) (s := s.val)
    have hr0 : 0 < r.val := Nat.pos_of_ne_zero fun h0 => hr (Fin.ext h0)
    have hs00 : 0 < s.val := Nat.pos_of_ne_zero fun h0 => hs0 (Fin.ext h0)
    have hlow' : s.val ≤ Fn.modulus / 2 := by
      simpa [Ecdsa.isLowS] using hlow
    have hd := hdec.mpr ⟨hr0, r.isLt, hs00, hlow', rfl⟩
    simp [verify, decodePublicKey_encodePublicKey hcurve (Ecdsa.mul_generator_ne_infinity hk),
      hd, hv]

end EthLib.Networking.Proofs.Libp2p.PeerId
