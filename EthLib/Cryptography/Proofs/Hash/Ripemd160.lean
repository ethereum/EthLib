module

public import EthLib.Cryptography.Hash.Ripemd160

/-!
# Proofs: `Hash.Ripemd160`

What is proved about RIPEMD-160:

- The added constants are the ones the authors derive from square and cube roots.
- Each group of sixteen steps of `r` and `r'` lists sixteen indices that include every message word, so it reads each once.
- Padding fills whole blocks, with the least zeros that do, and keeps the message and the `0x80` byte in place.
- Every digest is 20 bytes.

This does not prove that the hash equals a second, independent model of the algorithm.

The Python tests of the bindings check the hash against the published test vectors.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Ripemd160

/-! ## The constants -/

/-- The largest number below 4 whose square is at most the given one. -/
def wholeSquareRoot (value : Nat) : Nat :=
  (List.range 4).foldl (fun best candidate => if candidate * candidate ≤ value then candidate else best) 0

/-- The largest number below 3 whose cube is at most the given one. -/
def wholeCubeRoot (value : Nat) : Nat :=
  (List.range 3).foldl (fun best candidate => if candidate ^ 3 ≤ value then candidate else best) 0

/--
Whether a word is `int(2^30 * sqrt(prime))`.

It is exactly when `word^2 ≤ prime * 2^60 < (word + 1)^2`.
-/
def isSquareRootTimes2Pow30 (prime word : Nat) : Bool :=
  word ^ 2 ≤ prime * 2 ^ 60 && prime * 2 ^ 60 < (word + 1) ^ 2

/--
Whether a word is `int(2^30 * cbrt(prime))`.

It is exactly when `word^3 ≤ prime * 2^90 < (word + 1)^3`.
-/
def isCubeRootTimes2Pow30 (prime word : Nat) : Bool :=
  word ^ 3 ≤ prime * 2 ^ 90 && prime * 2 ^ 90 < (word + 1) ^ 3

/-- The constants of the left line are `int(2^30 * sqrt(p))` for p = 2, 3, 5, 7, as in `rmd160.txt`. -/
theorem K_from_square_roots :
    ([2, 3, 5, 7].zip ((K.toList.drop 1).map UInt32.toNat)).all
      (fun pair => isSquareRootTimes2Pow30 pair.1 pair.2) = true ∧
    K[0] = 0 := by
  decide +kernel

/-- The constants of the right line are `int(2^30 * cbrt(p))` for p = 2, 3, 5, 7, as in `rmd160.txt`. -/
theorem K'_from_cube_roots :
    ([2, 3, 5, 7].zip ((K'.toList.take 4).map UInt32.toNat)).all
      (fun pair => isCubeRootTimes2Pow30 pair.1 pair.2) = true ∧
    K'[4] = 0 := by
  decide +kernel

/-! ## The word order

Each group of sixteen steps reads every message word exactly once, in both lines.
-/

/-- The sixteen indices of one group of an index table. -/
def group (table : Vector (Fin 16) 80) (g : Nat) : List Nat :=
  (List.range 16).map fun i => (table[16 * g + i]!).val

/-- Every group of `r` is a permutation of the sixteen words. -/
theorem r_groups_permute :
    (List.range 5).all (fun g => (group r g).length == 16 && (List.range 16).all (group r g).contains) = true := by
  decide +kernel

/-- Every group of `r'` is a permutation of the sixteen words. -/
theorem r'_groups_permute :
    (List.range 5).all (fun g => (group r' g).length == 16 && (List.range 16).all (group r' g).contains) = true := by
  decide +kernel

/-! ## Padding -/

/-- The length takes eight bytes. -/
@[simp] theorem lengthBytes_size (size : Nat) : (lengthBytes size).size = 8 := by
  simp only [lengthBytes, ByteArray.size, Array.size_ofFn]

/-- Padding adds the `0x80` byte, the zeros, and the eight length bytes. -/
theorem pad_size (message : ByteArray) :
    (pad message).size = message.size + 1 + paddingZeros message.size + 8 := by
  simp only [pad, ByteArray.size_append, ByteArray.size_push, lengthBytes_size]
  simp only [ByteArray.size, Array.size_replicate]

/-- Padding adds fewer than a block of zeros. -/
theorem paddingZeros_lt (size : Nat) : paddingZeros size < 64 := Nat.mod_lt _ (by decide)

/-- A padded message is whole blocks. -/
theorem pad_size_mod (message : ByteArray) : (pad message).size % 64 = 0 := by
  rw [pad_size]
  unfold paddingZeros
  omega

/-- No fewer zeros would fill whole blocks. -/
theorem paddingZeros_minimal (size zeros : Nat) (complete : (size + 1 + zeros + 8) % 64 = 0) :
    paddingZeros size ≤ zeros := by
  unfold paddingZeros
  omega

/-- Padding keeps every byte of the message where it was. -/
theorem pad_prefix (message : ByteArray) (i : Nat) (within : i < message.size) :
    (pad message)[i]'(by rw [pad_size]; omega) = message[i] := by
  -- Name the bound, so it unfolds together with the padded message.
  have bound : i < (pad message).size := by rw [pad_size]; omega
  change (pad message)[i]'bound = message[i]
  unfold pad at bound ⊢
  rw [ByteArray.getElem_append_left (by simp; omega), ByteArray.getElem_append_left (by simp; omega)]
  exact Array.getElem_push_lt within

/-- The byte after the message is `0x80`. -/
theorem pad_delimiter (message : ByteArray) :
    (pad message)[message.size]'(by rw [pad_size]; omega) = 0x80 := by
  -- Name the bound, so it unfolds together with the padded message.
  have bound : message.size < (pad message).size := by rw [pad_size]; omega
  change (pad message)[message.size]'bound = 0x80
  unfold pad at bound ⊢
  rw [ByteArray.getElem_append_left (by simp; omega), ByteArray.getElem_append_left (by simp)]
  exact Array.getElem_push_eq

/-- Every byte between `0x80` and the length is zero. -/
theorem pad_zero (message : ByteArray) (i : Nat) (within : i < paddingZeros message.size) :
    (pad message)[message.size + 1 + i]'(by rw [pad_size]; omega) = 0 := by
  have zeroSize : (ByteArray.mk (Array.replicate (paddingZeros message.size) 0)).size =
      paddingZeros message.size := Array.size_replicate
  -- Name the bound, so it unfolds together with the padded message.
  have bound : message.size + 1 + i < (pad message).size := by rw [pad_size]; omega
  change (pad message)[message.size + 1 + i]'bound = 0
  unfold pad at bound ⊢
  rw [ByteArray.getElem_append_left (by simp only [ByteArray.size_append, ByteArray.size_push, zeroSize]; omega)]
  rw [ByteArray.getElem_append_right (by simp)]
  exact Array.getElem_replicate _

/-- The last eight bytes are the length. -/
theorem pad_length_suffix (message : ByteArray) :
    (pad message).extract ((pad message).size - 8) (pad message).size = lengthBytes message.size := by
  have zeroSize : (ByteArray.mk (Array.replicate (paddingZeros message.size) 0)).size =
      paddingZeros message.size := Array.size_replicate
  rw [pad_size]
  unfold pad
  apply ByteArray.extract_append_eq_right
  · simp only [ByteArray.size_append, ByteArray.size_push, zeroSize]
    omega
  · simp only [ByteArray.size_append, ByteArray.size_push, lengthBytes_size, zeroSize]

/-! ## The hash -/

/-- Every digest is 20 bytes long, whatever the message. -/
@[simp] theorem hash_size (message : ByteArray) : (hash message).size = 20 := by
  simp only [hash, digest, ByteArray.size, Array.size_ofFn]

end EthLib.Cryptography.Hash.Ripemd160
