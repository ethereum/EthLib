import EthLib.Cryptography.Vrf.Serialization
import EthLib.Cryptography.Proofs.Vrf.Verify

/-!
# Proofs: `Vrf.Serialization`

The encoding is a bijection between openings and 1056-byte strings.

- Decoding an encoding returns the opening.
- Every 1056-byte string is an encoding.
- Every string of another length is rejected.

Verification over bytes rejects malformed input, and agrees with typed verification on the rest.
-/

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants

/-! ## Sizes -/

/-- An opening encodes to 1056 bytes. -/
@[simp] theorem size_encodeOpening (o : Opening) : (encodeOpening o).size = VRF_OPENING_SIZE := by
  simp only [encodeOpening, ByteArray.size_append, size_packBytes]
  rfl

/-! ## Decoding inverts encoding -/

/-- Reading an object back out of its own bytes returns it. -/
private theorem readBytes_pack {m n : Nat} (s : Vector UInt8 m) (p : Vector (Vector UInt8 m) n)
    (h : 0 + m ≤ (packBytes s ++ packBytes p.flatten).size) :
    readBytes (packBytes s ++ packBytes p.flatten) 0 m h = s := by
  apply Vector.ext
  intro k hk
  simp only [readBytes, Vector.getElem_ofFn, Nat.zero_add, ByteArray.data_append, packBytes]
  rw [Array.getElem_append_left (by simpa using hk)]
  simp

/-- Reading item `l` of a flattened list back out of its bytes returns it. -/
private theorem readBytes_pack_flatten {m n : Nat} (s : Vector UInt8 m)
    (p : Vector (Vector UInt8 m) n) (l : Nat) (hl : l < n)
    (h : m + m * l + m ≤ (packBytes s ++ packBytes p.flatten).size) :
    readBytes (packBytes s ++ packBytes p.flatten) (m + m * l) m h = p[l] := by
  apply Vector.ext
  intro k hk
  simp only [readBytes, Vector.getElem_ofFn, ByteArray.data_append, packBytes]
  rw [Array.getElem_append_right (by simp; omega)]
  -- Position `m + m l + k` is byte `k` of item `l`.
  have hq : (m + m * l + k - m) / m = l := by
    rw [show m + m * l + k - m = k + m * l by omega, Nat.add_mul_div_left _ _ (by omega),
      Nat.div_eq_of_lt hk, Nat.zero_add]
  have hr : (m + m * l + k - m) % m = k := by
    rw [show m + m * l + k - m = k + m * l by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hk]
  simp [hq, hr]

/-- Decoding an encoding returns the opening. -/
@[simp] theorem decodeOpening_encodeOpening (o : Opening) :
    decodeOpening (encodeOpening o) = some o := by
  unfold decodeOpening
  rw [dite_eq_left_of_eq_true (eq_true (size_encodeOpening o))]
  cases o with
  | mk s p =>
    simp only [encodeOpening, Option.some.injEq, Opening.mk.injEq]
    -- Bytes 0 to 31 are the secret, and bytes `32 + 32 l` to `63 + 32 l` are sibling `l`.
    exact ⟨readBytes_pack s p (by simp),
      Vector.ext fun l hl => by
        simp only [Vector.getElem_ofFn]
        exact readBytes_pack_flatten s p l hl (by
          have := size_encodeOpening ⟨s, p⟩
          simp only [encodeOpening, VRF_OPENING_SIZE] at this
          simp only [this, VRF_HASH_SIZE, VRF_TREE_HEIGHT] at *
          omega)⟩

/-- A buffer of `m + m n` bytes is its first `m` bytes, then `n` items of `m` bytes. -/
private theorem pack_readBytes {m n : Nat} (b : ByteArray) (hb : b.size = m + m * n) :
    packBytes (readBytes b 0 m (by omega)) ++ packBytes (Vector.flatten (Vector.ofFn fun l : Fin n =>
      readBytes b (m + m * l.val) m (by
        have := Nat.mul_le_mul_left m (Nat.succ_le_of_lt l.isLt)
        rw [hb, Nat.mul_succ] at *
        omega))) = b := by
  cases b with
  | mk data =>
    simp only [ByteArray.size] at hb
    apply ByteArray.ext
    simp only [packBytes, ByteArray.data_append]
    apply Array.ext
    · simp [hb, Nat.mul_comm]
    · intro k hk _
      by_cases hkm : k < m
      · rw [Array.getElem_append_left (by simpa using hkm)]
        simp [readBytes]
      · rw [Array.getElem_append_right (by simp; omega)]
        simp [readBytes]
        congr 1
        -- Byte `k - m` of the items is byte `(k - m) % m` of item `(k - m) / m`.
        have := Nat.div_add_mod (k - m) m
        omega

/-- Every string that decodes is the encoding of what it decodes to. -/
theorem encodeOpening_of_decodeOpening {bytes : ByteArray} {o : Opening}
    (h : decodeOpening bytes = some o) : encodeOpening o = bytes := by
  unfold decodeOpening at h
  split at h
  · rename_i hsize
    simp only [Option.some.injEq] at h
    subst h
    exact pack_readBytes (m := VRF_HASH_SIZE) (n := VRF_TREE_HEIGHT) bytes hsize
  · simp at h

/-- A string decodes exactly when it is 1056 bytes long. -/
theorem decodeOpening_isSome_iff (bytes : ByteArray) :
    (decodeOpening bytes).isSome ↔ bytes.size = VRF_OPENING_SIZE := by
  unfold decodeOpening
  split <;> simp_all

/-! ## Verification over bytes -/

/-- A root that is not 32 bytes is rejected. -/
theorem verifyBytes_badRoot {root opening : ByteArray} {index : Nat}
    (h : root.size ≠ VRF_HASH_SIZE) : verifyBytes root index opening = none := by
  simp [verifyBytes, h]

/-- An index outside `[0, 2^32)` is rejected. -/
theorem verifyBytes_badIndex {root opening : ByteArray} {index : Nat}
    (h : 2 ^ VRF_TREE_HEIGHT ≤ index) : verifyBytes root index opening = none := by
  simp [verifyBytes, Nat.not_lt.mpr h]

/-- An opening that is not 1056 bytes is rejected. -/
theorem verifyBytes_badOpening {root opening : ByteArray} {index : Nat}
    (h : opening.size ≠ VRF_OPENING_SIZE) : verifyBytes root index opening = none := by
  have hnone : decodeOpening opening = none := by
    unfold decodeOpening
    simp [h]
  unfold verifyBytes
  split
  · split
    · simp [hnone]
    · rfl
  · rfl

/-- On encoded inputs, verification over bytes is typed verification. -/
theorem verifyBytes_encode (root : Digest) (i : UInt32) (o : Opening) :
    verifyBytes (packBytes root) i.toNat (encodeOpening o) = verify root i o := by
  have hroot : readBytes (packBytes root) 0 VRF_HASH_SIZE (by simp) = root := by
    apply Vector.ext
    intro k hk
    simp [readBytes, packBytes]
  have hi : i.toNat < 2 ^ VRF_TREE_HEIGHT := i.toNat_lt
  simp [verifyBytes, hi, hroot]

end EthLib.Cryptography.Vrf
