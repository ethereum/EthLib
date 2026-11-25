module

public import EthLib.Cryptography.Secp256r1.Encoding
public import EthLib.Base.Proofs.ByteOrder
public import EthLib.Cryptography.Proofs.ShortWeierstrass.Encoding

/-!
# Proofs: the uncompressed encoding of secp256r1

The decoder follows the uncompressed case of SEC 1 v2 §2.3.4, and no other.

It accepts exactly the uncompressed encodings of §2.3.3.

Those are the bytes `04 ‖ x ‖ y` of the affine points `(x, y)` on the curve.

So the octet `00` of `O` is refused.

It also refuses another prefix or length, a coordinate of `p` or more, and a pair off the curve.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256r1

open Base

/-- The decoder accepts exactly the uncompressed encodings of the affine points on the curve.

The encoding is the prefix `04`, then `x`, then `y`.

Each coordinate takes 32 big-endian bytes, by SEC 1 v2 §2.3.5.

It returns the point `(x, y)` of every such encoding. -/
theorem decodeUncompressed_eq_some_iff {bytes : List UInt8} {point : Point} :
    decodeUncompressed bytes = some point ↔
      ∃ x y : Fp, point = .affine x y ∧ point.isOnCurve = true ∧
        bytes = encodeUncompressed x y := by
  constructor
  · intro h
    unfold decodeUncompressed at h
    split at h
    · rename_i coords
      split at h <;> rename_i hlen
      · split at h
        · rename_i x y hx hy
          dsimp only at h
          split at h <;> rename_i hc
          · cases h
            refine ⟨_, _, rfl, hc, ?_⟩
            -- Each half of the 64 bytes is the 32-byte form of the coordinate it holds.
            simp only [encodeUncompressed, ShortWeierstrass.encodeUncompressed,
              ShortWeierstrass.coordinateToBytes_of_coordinateOfBytes? (by simp [hlen]) hx,
              ShortWeierstrass.coordinateToBytes_of_coordinateOfBytes? (by simp [hlen]) hy,
              List.take_append_drop]
          · cases h
        · cases h
      · cases h
    · cases h
  · rintro ⟨x, y, rfl, hc, rfl⟩
    -- The decoder splits the 64 bytes back into the two coordinates, each below `p`.
    have hl (z : Fp) : z.toBytes.length = 32 := ShortWeierstrass.length_coordinateToBytes z
    have hlen : (x.toBytes ++ y.toBytes).length = 64 := by simp [hl]
    have htake : (x.toBytes ++ y.toBytes).take 32 = x.toBytes := by
      rw [List.take_append_of_le_length (Nat.le_of_eq (hl x).symm),
        List.take_of_length_le (Nat.le_of_eq (hl x))]
    have hdrop : (x.toBytes ++ y.toBytes).drop 32 = y.toBytes := by
      rw [List.drop_append_of_le_length (Nat.le_of_eq (hl x).symm),
        List.drop_of_length_le (Nat.le_of_eq (hl x)), List.nil_append]
    have hp : Fp.modulus ≤ 2 ^ 256 := by decide
    simp only [decodeUncompressed, encodeUncompressed, ShortWeierstrass.encodeUncompressed, hlen,
      htake, hdrop, ShortWeierstrass.coordinateOfBytes?_coordinateToBytes hp, hc, ite_true]

end EthLib.Cryptography.Secp256r1
