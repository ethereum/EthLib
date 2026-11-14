module

public import EthLib.Cryptography.Proofs.Hash.Sha256
public import EthLib.Cryptography.Hash.Hmac

/-!
# Proofs: HMAC-SHA-256

Every HMAC-SHA-256 tag is 32 bytes long.

The key block follows step (1) of [RFC 2104 §2](https://www.rfc-editor.org/rfc/rfc2104#section-2).

A key of at most `B = 64` bytes is padded with zero bytes to `B` bytes.

A longer key is hashed first, and its 32-byte hash is padded the same way.

So zero bytes appended to a short key do not change the tag.

The pads act byte by byte, as steps (2) and (5) of the RFC XOR the key block with `ipad` and `opad`.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Hmac

/-- Every tag is 32 bytes long, whatever the key and the message. -/
@[simp] theorem hmac_size (key message : ByteArray) : (hmac key message).size = 32 :=
  Sha256.hash_size _

/-! ## The key block -/

/-- A key of at most `B` bytes is padded with zero bytes to `B` bytes. -/
theorem blockKey_of_le {key : ByteArray} (h : key.size ≤ BLOCK_SIZE) :
    blockKey key = key ++ ⟨Array.replicate (BLOCK_SIZE - key.size) 0⟩ := by
  rw [blockKey, ite_eq_right (Nat.not_lt.mpr h)]

/-- A key longer than `B` bytes is hashed, and its hash is padded with zero bytes to `B` bytes. -/
theorem blockKey_of_lt {key : ByteArray} (h : BLOCK_SIZE < key.size) :
    blockKey key = Sha256.hash key ++ ⟨Array.replicate (BLOCK_SIZE - 32) 0⟩ := by
  rw [blockKey, ite_eq_left h, Sha256.hash_size]

/-- The key block has `B = 64` bytes. -/
theorem blockKey_size (key : ByteArray) : (blockKey key).size = BLOCK_SIZE := by
  by_cases h : BLOCK_SIZE < key.size
  · rw [blockKey_of_lt h, ByteArray.size_append, Sha256.hash_size]
    rfl
  · have h := Nat.not_lt.mp h
    rw [blockKey_of_le h, ByteArray.size_append]
    simp only [ByteArray.size, Array.size_replicate] at h ⊢
    omega

/-- Zero bytes appended to a key of at most `B` bytes leave the key block unchanged. -/
theorem blockKey_append_zeros {key : ByteArray} {n : Nat} (h : key.size + n ≤ BLOCK_SIZE) :
    blockKey (key ++ ⟨Array.replicate n 0⟩) = blockKey key := by
  have h' : (key ++ ⟨Array.replicate n 0⟩).size ≤ BLOCK_SIZE := by
    rw [ByteArray.size_append]
    simp only [ByteArray.size, Array.size_replicate] at h ⊢
    omega
  rw [blockKey_of_le h', blockKey_of_le (by omega), ByteArray.append_assoc]
  congr 1
  apply ByteArray.ext
  simp only [ByteArray.data_append, ByteArray.size_append]
  simp only [ByteArray.size, Array.size_replicate] at h ⊢
  rw [Array.replicate_append_replicate]
  congr 1
  omega

/-- Zero bytes appended to a key of at most `B` bytes leave the tag unchanged. -/
theorem hmac_append_zeros {key : ByteArray} {n : Nat} (h : key.size + n ≤ BLOCK_SIZE)
    (message : ByteArray) : hmac (key ++ ⟨Array.replicate n 0⟩) message = hmac key message := by
  unfold hmac
  rw [blockKey_append_zeros h]

/-! ## The pads -/

/-- XOR with a pad keeps the length. -/
theorem xorPad_size (block : ByteArray) (pad : UInt8) : (xorPad block pad).size = block.size :=
  Array.size_map ..

/-- XOR with a pad acts byte by byte. -/
theorem xorPad_getElem {block : ByteArray} {pad : UInt8} {i : Nat} (h : i < block.size) :
    (xorPad block pad)[i]'(by rw [xorPad_size]; exact h) = block[i] ^^^ pad :=
  Array.getElem_map ..

end EthLib.Cryptography.Hash.Hmac
