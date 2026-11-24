module

public import EthLib.Cryptography.Secp256r1.Encoding
public import EthLib.Base.Proofs.ByteOrder

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

/-- The encoding of a coordinate has 32 bytes. -/
private theorem Fp.length_toBytes (x : Fp) : x.toBytes.length
    = 32 := ByteOrder.length_toList_toBE 32 x.val

/-- The 32 bytes of a coordinate hold its value. -/
private theorem Fp.ofBE_toBytes (x : Fp) : ByteOrder.ofBE x.toBytes = x.val :=
  ByteOrder.ofBE_toBE_of_lt (Nat.lt_trans x.isLt (by decide))

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
      · dsimp only at h
        split at h <;> rename_i hx
        · split at h <;> rename_i hy
          · split at h <;> rename_i hc
            · cases h
              refine ⟨_, _, rfl, hc, ?_⟩
              -- Each half of the 64 bytes is the 32-byte form of the value it holds.
              have hx' : (ByteOrder.toBE 32 (ByteOrder.ofBE (coords.take 32))).toList
                  = coords.take 32 := by
                exact ByteOrder.toList_toBE_ofBE_of_length (by simp [hlen])
              have hy' : (ByteOrder.toBE 32 (ByteOrder.ofBE (coords.drop 32))).toList
                  = coords.drop 32 := by
                exact ByteOrder.toList_toBE_ofBE_of_length (by simp [hlen])
              simp only [encodeUncompressed, Fp.toBytes]
              rw [hx', hy', List.take_append_drop]
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · rintro ⟨x, y, rfl, hc, rfl⟩
    -- The decoder splits the 64 bytes back into the two coordinates, each below `p`.
    have hlen : (x.toBytes ++ y.toBytes).length = 64 := by simp [Fp.length_toBytes]
    have htake : (x.toBytes ++ y.toBytes).take 32 = x.toBytes := by
      rw [List.take_append_of_le_length (Nat.le_of_eq (Fp.length_toBytes x).symm),
        List.take_of_length_le (Nat.le_of_eq (Fp.length_toBytes x))]
    have hdrop : (x.toBytes ++ y.toBytes).drop 32 = y.toBytes := by
      rw [List.drop_append_of_le_length (Nat.le_of_eq (Fp.length_toBytes x).symm),
        List.drop_of_length_le (Nat.le_of_eq (Fp.length_toBytes x)), List.nil_append]
    simp only [decodeUncompressed, encodeUncompressed, hlen, htake, hdrop, Fp.ofBE_toBytes,
      x.isLt, y.isLt, Fin.eta, hc, dite_true, ite_true]

end EthLib.Cryptography.Secp256r1
