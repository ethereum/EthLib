module

public import EthLib.Cryptography.Hash.Padding

/-!
# Proofs: Merkle-Damgård padding of 64-byte blocks

A padded message is whole blocks, with the fewest zeros that make it so.

It keeps the message, then holds the byte `0x80`, the zeros and the length bytes.

The facts on its size and on its last bytes hold for any length bytes of size 8.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Padding

/-- Padding adds the `0x80` byte, the zeros, and the length bytes. -/
theorem size_pad (lengthBytes : Nat → ByteArray) (message : ByteArray) :
    (pad lengthBytes message).size =
      message.size + 1 + paddingZeros message.size + (lengthBytes message.size).size := by
  simp only [pad, ByteArray.size_append, ByteArray.size_push]
  simp only [ByteArray.size, Array.size_replicate]

/-- Padding adds the `0x80` byte, the zeros, and the eight length bytes. -/
theorem pad_size {lengthBytes : Nat → ByteArray} (eight : ∀ n, (lengthBytes n).size = 8)
    (message : ByteArray) :
    (pad lengthBytes message).size = message.size + 1 + paddingZeros message.size + 8 := by
  rw [size_pad, eight]

/-- Padding adds fewer than a block of zeros. -/
theorem paddingZeros_lt (size : Nat) : paddingZeros size < 64 := Nat.mod_lt _ (by decide)

/-- A padded message is whole blocks. -/
theorem pad_size_mod {lengthBytes : Nat → ByteArray} (eight : ∀ n, (lengthBytes n).size = 8)
    (message : ByteArray) : (pad lengthBytes message).size % 64 = 0 := by
  rw [pad_size eight]
  unfold paddingZeros
  omega

/-- No fewer zeros would fill whole blocks. -/
theorem paddingZeros_minimal (size zeros : Nat) (complete : (size + 1 + zeros + 8) % 64 = 0) :
    paddingZeros size ≤ zeros := by
  unfold paddingZeros
  omega

/-- Padding keeps every byte of the message where it was. -/
theorem pad_prefix (lengthBytes : Nat → ByteArray) (message : ByteArray) (i : Nat)
    (within : i < message.size) :
    (pad lengthBytes message)[i]'(by rw [size_pad]; omega) = message[i] := by
  -- Name the bound, so it unfolds together with the padded message.
  have bound : i < (pad lengthBytes message).size := by rw [size_pad]; omega
  change (pad lengthBytes message)[i]'bound = message[i]
  unfold pad at bound ⊢
  rw [ByteArray.getElem_append_left (by simp; omega),
    ByteArray.getElem_append_left (by simp; omega)]
  exact Array.getElem_push_lt within

/-- The byte after the message is `0x80`. -/
theorem pad_delimiter (lengthBytes : Nat → ByteArray) (message : ByteArray) :
    (pad lengthBytes message)[message.size]'(by rw [size_pad]; omega) = 0x80 := by
  -- Name the bound, so it unfolds together with the padded message.
  have bound : message.size < (pad lengthBytes message).size := by rw [size_pad]; omega
  change (pad lengthBytes message)[message.size]'bound = 0x80
  unfold pad at bound ⊢
  rw [ByteArray.getElem_append_left (by simp; omega), ByteArray.getElem_append_left (by simp)]
  exact Array.getElem_push_eq

/-- Every byte between `0x80` and the length is zero. -/
theorem pad_zero (lengthBytes : Nat → ByteArray) (message : ByteArray) (i : Nat)
    (within : i < paddingZeros message.size) :
    (pad lengthBytes message)[message.size + 1 + i]'(by rw [size_pad]; omega) = 0 := by
  have zeroSize : (ByteArray.mk (Array.replicate (paddingZeros message.size) 0)).size =
      paddingZeros message.size := Array.size_replicate
  -- Name the bound, so it unfolds together with the padded message.
  have bound : message.size + 1 + i < (pad lengthBytes message).size := by
    rw [size_pad]; omega
  change (pad lengthBytes message)[message.size + 1 + i]'bound = 0
  unfold pad at bound ⊢
  rw [ByteArray.getElem_append_left
    (by simp only [ByteArray.size_append, ByteArray.size_push, zeroSize]; omega)]
  rw [ByteArray.getElem_append_right (by simp)]
  exact Array.getElem_replicate _

/-- The last eight bytes are the length. -/
theorem pad_length_suffix {lengthBytes : Nat → ByteArray} (eight : ∀ n, (lengthBytes n).size = 8)
    (message : ByteArray) :
    (pad lengthBytes message).extract ((pad lengthBytes message).size - 8)
      (pad lengthBytes message).size = lengthBytes message.size := by
  have zeroSize : (ByteArray.mk (Array.replicate (paddingZeros message.size) 0)).size =
      paddingZeros message.size := Array.size_replicate
  rw [pad_size eight]
  unfold pad
  apply ByteArray.extract_append_eq_right
  · simp only [ByteArray.size_append, ByteArray.size_push, zeroSize]
    omega
  · simp only [ByteArray.size_append, ByteArray.size_push, eight, zeroSize]

end EthLib.Cryptography.Hash.Padding
