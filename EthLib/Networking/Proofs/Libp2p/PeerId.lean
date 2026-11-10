module

public import EthLib.Networking.Libp2p.PeerId
public import EthLib.Cryptography.Proofs.Secp256k1.Encoding

/-!
# Proofs: libp2p secp256k1 public keys and peer IDs

- A point of the curve, other than infinity, encodes to a key protobuf that decodes back to it.
- A peer ID decodes back to its key, and the decoder accepts only peer IDs of keys.
- Two different points of the curve have two different peer IDs.
- A decoded key's peer ID is the two bytes `00 25`, then the key protobuf.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Libp2p.PeerId

open EthLib.Cryptography.Secp256k1
open EthLib.Networking.Libp2p

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

end EthLib.Networking.Proofs.Libp2p.PeerId
