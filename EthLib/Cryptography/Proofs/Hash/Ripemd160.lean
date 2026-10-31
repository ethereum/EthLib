import EthLib.Cryptography.Hash.Ripemd160

/-!
# Proofs: `Hash.Ripemd160`

What is proved about RIPEMD-160:

- The added constants are the ones the authors derive from square and cube roots.
- Each group of sixteen steps of `r` and `r'` lists sixteen indices that include every message word, so it reads each once.
- Padding fills whole blocks, with the least zeros that do, and keeps the message and the `0x80` byte in place.
- Every digest is 20 bytes.
- The digests of the test vectors published with the algorithm, and of every way a message can end against the 64-byte block, are as listed.

This does not prove that `hash` equals a second, independent model of the algorithm.
The known answers pin the whole computation at the inputs below, and nothing more.
-/

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
  unfold pad
  rw [ByteArray.getElem_append_left (by simp; omega), ByteArray.getElem_append_left (by simp; omega)]
  exact Array.getElem_push_lt within

/-- The byte after the message is `0x80`. -/
theorem pad_delimiter (message : ByteArray) :
    (pad message)[message.size]'(by rw [pad_size]; omega) = 0x80 := by
  unfold pad
  rw [ByteArray.getElem_append_left (by simp; omega), ByteArray.getElem_append_left (by simp)]
  exact Array.getElem_push_eq

/-- Every byte between `0x80` and the length is zero. -/
theorem pad_zero (message : ByteArray) (i : Nat) (within : i < paddingZeros message.size) :
    (pad message)[message.size + 1 + i]'(by rw [pad_size]; omega) = 0 := by
  have zeroSize : (ByteArray.mk (Array.replicate (paddingZeros message.size) 0)).size =
      paddingZeros message.size := Array.size_replicate
  unfold pad
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

/-! ## Known answers

The first nine are the test vectors on Bosselaers' RIPEMD-160 page, which states them for the algorithm of the paper.
The tenth, one million times "a", is the page's last vector.
The kernel does not run it: it needs 15625 blocks.
The Python tests of the bindings do.

The rest pin each way a message can end against the 64-byte block.
Their digests come from two other implementations: OpenSSL 3 `openssl dgst -rmd160` and Python's `hashlib.new("ripemd160")`.
The two agree on every one of them.

```text
    bytes   blocks   padding
      0       1      56 zero bytes, then the length
     55       1      0 zero bytes
     56       2      63 zero bytes
     63       2      56 zero bytes
     64       2      55 zero bytes
    119       2      0 zero bytes
    120       3      63 zero bytes
```

Messages are the ASCII bytes of a string, or the byte `a` repeated.
Digests are written in hex, as on the page, and read by the kernel. -/

/-- The value of one hex digit, upper or lower case. -/
def hexDigit (c : Char) : Nat :=
  -- '0' is 48, 'A' is 65 and 'a' is 97 in ASCII.
  if c.toNat < 58 then c.toNat - 48 else if c.toNat < 71 then c.toNat - 55 else c.toNat - 87

/-- The bytes a hex string spells, two digits per byte, the high digit first. -/
def hexBytes (s : String) : ByteArray :=
  ⟨(go s.toList).toArray⟩
where
  /-- Read the digits two at a time. -/
  go : List Char → List UInt8
    | hi :: lo :: rest => UInt8.ofNat (16 * hexDigit hi + hexDigit lo) :: go rest
    | _ => []

/-- The ASCII bytes of a string. -/
def ascii (s : String) : ByteArray := ⟨(s.toList.map fun c => UInt8.ofNat c.toNat).toArray⟩

/-- A message of `count` bytes, each `a`. -/
def aRepeated (count : Nat) : ByteArray := ⟨Array.replicate count 0x61⟩

/-- The empty string. -/
theorem hash_empty :
    hash ByteArray.empty = hexBytes "9c1185a5c5e9fc54612808977ee8f548b2258d31" := by
  decide +kernel

/-- `"a"`. -/
theorem hash_a :
    hash (ascii "a") = hexBytes "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe" := by
  decide +kernel

/-- `"abc"`. -/
theorem hash_abc :
    hash (ascii "abc") = hexBytes "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc" := by
  decide +kernel

/-- `"message digest"`. -/
theorem hash_message_digest :
    hash (ascii "message digest") = hexBytes "5d0689ef49d2fae572b881b123a85ffa21595f36" := by
  decide +kernel

/-- `"a...z"`: the lowercase alphabet. -/
theorem hash_alphabet :
    hash (ascii "abcdefghijklmnopqrstuvwxyz") = hexBytes "f71c27109c692c1b56bbdceb5b9d2865b3708dbc" := by
  decide +kernel

/-- `"abcdbcde...nopq"`: the 56-byte message of the page, whose padding needs a second block. -/
theorem hash_abcdbcde :
    hash (ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")
      = hexBytes "12a053384a9c0c88e405a06c27dcf49ada62eb2b" := by
  decide +kernel

/-- `"A...Za...z0...9"`: both alphabets and the digits, 62 bytes. -/
theorem hash_alphanumeric :
    hash (ascii "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789")
      = hexBytes "b0e20b6e3116640286ed3a87a5713079b21f5189" := by
  decide +kernel

/-- Eight times `"1234567890"`: 80 bytes, two blocks. -/
theorem hash_digits :
    hash (ascii "12345678901234567890123456789012345678901234567890123456789012345678901234567890")
      = hexBytes "9b752e45573d4b39f4dbd3323cab82bf63326bfb" := by
  decide +kernel

/-- 55 bytes: the longest message padded within one block. -/
theorem hash_55 : hash (aRepeated 55) = hexBytes "0d8a8c9063a48576a7c97e9f95253a6e53ff6765" := by
  decide +kernel

/-- 56 bytes: the shortest message whose length spills into a second block. -/
theorem hash_56 : hash (aRepeated 56) = hexBytes "e72334b46c83cc70bef979e15453706c95b888be" := by
  decide +kernel

/-- 63 bytes: one byte short of a whole block. -/
theorem hash_63 : hash (aRepeated 63) = hexBytes "e640041293fe663b9bf3f8c21ffecac03819e6b2" := by
  decide +kernel

/-- 64 bytes: a whole block, followed by a block of padding. -/
theorem hash_64 : hash (aRepeated 64) = hexBytes "9dfb7d374ad924f3f88de96291c33e9abed53e32" := by
  decide +kernel

/-- 119 bytes: the longest message padded within two blocks. -/
theorem hash_119 : hash (aRepeated 119) = hexBytes "23e398ff2bac815aa1bbb57ca2a669c841872919" := by
  decide +kernel

/-- 120 bytes: the shortest message that needs a third block. -/
theorem hash_120 : hash (aRepeated 120) = hexBytes "c476770a6dae31fcee8d25efe6559a05c8024595" := by
  decide +kernel

end EthLib.Cryptography.Hash.Ripemd160
