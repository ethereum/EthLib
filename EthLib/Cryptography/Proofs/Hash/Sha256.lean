module

public import EthLib.Cryptography.Hash.Sha256

/-!
# Proofs: SHA-256

SHA-256 agrees with FIPS 180-4 on every message shorter than 2^61 bytes.

The file restates the standard as a model over 32-bit bit vectors.

The model shares only the 64 round constants with the executable code.

A theorem below derives them from the cube roots of the first 64 primes.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Sha256

/-! ## The model -/

namespace Spec

/-- A word whose arithmetic is modulo 2^32, FIPS 180-4 §3.2. -/
abbrev Word := BitVec 32

/-- The eight working variables a to h, FIPS 180-4 §6.2.2. -/
structure State where
  /-- The working variable `a`. -/
  a : Word
  /-- The working variable `b`. -/
  b : Word
  /-- The working variable `c`. -/
  c : Word
  /-- The working variable `d`. -/
  d : Word
  /-- The working variable `e`. -/
  e : Word
  /-- The working variable `f`. -/
  f : Word
  /-- The working variable `g`. -/
  g : Word
  /-- The working variable `h`. -/
  h : Word
  deriving DecidableEq

/-- σ0 of FIPS 180-4 §4.1.2 (4.6). -/
def small0 (x : Word) : Word := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)

/-- σ1 of FIPS 180-4 §4.1.2 (4.7). -/
def small1 (x : Word) : Word := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)

/-- Σ0 of FIPS 180-4 §4.1.2 (4.4). -/
def large0 (x : Word) : Word := x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

/-- Σ1 of FIPS 180-4 §4.1.2 (4.5). -/
def large1 (x : Word) : Word := x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

/-- One round of FIPS 180-4 §6.2.2, step 3. -/
def step (s : State) (constant word : Word) : State :=
  let choose := (s.e &&& s.f) ^^^ ((~~~s.e) &&& s.g)
  let majority := (s.a &&& s.b) ^^^ (s.a &&& s.c) ^^^ (s.b &&& s.c)
  let t1 := s.h + large1 s.e + choose + constant + word
  let t2 := large0 s.a + majority
  ⟨t1 + t2, s.a, s.b, s.c, s.d + t1, s.e, s.f, s.g⟩

/-- The message schedule of FIPS 180-4 §6.2.2, step 1, as a recurrence. -/
def messageWord (input : Vector Word 16) (t : Nat) : Word :=
  if early : t < 16 then input[t]
  else
    messageWord input (t - 16) + small0 (messageWord input (t - 15)) +
      messageWord input (t - 7) + small1 (messageWord input (t - 2))
termination_by t

/-- Four bytes read as one big-endian word, FIPS 180-4 §3.1. -/
def inputWord (block : ByteArray) (start : Nat) : Word :=
  (BitVec.ofNat 32 block[start]!.toNat) <<< 24 |||
    (BitVec.ofNat 32 block[start + 1]!.toNat) <<< 16 |||
    (BitVec.ofNat 32 block[start + 2]!.toNat) <<< 8 |||
    BitVec.ofNat 32 block[start + 3]!.toNat

/-- The sixteen words of the block starting at a byte offset, FIPS 180-4 §5.2.1. -/
def inputWords (block : ByteArray) (start : Nat) : Vector Word 16 :=
  Vector.ofFn fun t => inputWord block (start + 4 * t.val)

/-- The first rounds of one block, FIPS 180-4 §6.2.2, steps 2 and 3. -/
def rounds (input : Vector Word 16) (initial : State) : Nat → State
  | 0 => initial
  | n + 1 => step (rounds input initial n) (K[n]!).toBitVec (messageWord input n)

/-- One block: 64 rounds, then the intermediate hash value added in, FIPS 180-4 §6.2.2, step 4. -/
def compression (input : Vector Word 16) (initial : State) : State :=
  let w := rounds input initial 64
  ⟨initial.a + w.a, initial.b + w.b, initial.c + w.c, initial.d + w.d,
    initial.e + w.e, initial.f + w.f, initial.g + w.g, initial.h + w.h⟩

/-- The initial hash value, FIPS 180-4 §5.3.3. -/
def initial : State :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

/-- The number of zero bytes after the `0x80` byte, FIPS 180-4 §5.1.1. -/
def zeroCount (size : Nat) : Nat := (119 - size % 64) % 64

/--
The padded message, FIPS 180-4 §5.1.1.

It is the message, `0x80`, zeros, and the bit length in eight big-endian bytes.
-/
def padded (message : ByteArray) : ByteArray :=
  ⟨message.data ++ #[0x80] ++ Array.replicate (zeroCount message.size) 0 ++
    Array.ofFn fun i : Fin 8 => UInt8.ofNat ((message.size * 8 / 2 ^ (56 - 8 * i.val)) % 256)⟩

/-- The intermediate hash value after the first blocks of a padded message, FIPS 180-4 §6.2.2. -/
def blocks (message : ByteArray) (initial : State) : Nat → State
  | 0 => initial
  | n + 1 => compression (inputWords message (64 * n)) (blocks message initial n)

/-- The eight words in digest order. -/
def State.words (s : State) : Vector Word 8 := #v[s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h]

/-- The digest: each word as four big-endian bytes, FIPS 180-4 §6.2.2. -/
def digest (s : State) : ByteArray :=
  ⟨Array.ofFn fun i : Fin 32 =>
    UInt8.ofNat ((s.words[i.val / 4]'(by omega)).toNat / 2 ^ (24 - 8 * (i.val % 4)) % 256)⟩

/-- SHA-256, FIPS 180-4 §6.2. -/
def hash (message : ByteArray) : ByteArray :=
  let input := padded message
  digest (blocks input initial (input.size / 64))

end Spec

/-! ## The constants -/

/--
Whether a number below 324 is prime.

Trial division stops at 17, since every composite below 18² has a divisor that small.
-/
def smallPrime (candidate : Nat) : Bool :=
  2 ≤ candidate && (List.range 18).all fun divisor =>
    divisor < 2 || divisor * divisor > candidate || candidate % divisor != 0

/-- The primes below a bound, in order, for bounds up to 324. -/
def smallPrimes (bound : Nat) : List Nat := (List.range bound).filter smallPrime

/-- The largest number below 18 whose square is at most the given one. -/
def wholeSquareRoot (value : Nat) : Nat :=
  (List.range 18).foldl (fun best candidate => if candidate * candidate ≤ value then candidate else best) 0

/-- The largest number below 8 whose cube is at most the given one. -/
def wholeCubeRoot (value : Nat) : Nat :=
  (List.range 8).foldl (fun best candidate => if candidate ^ 3 ≤ value then candidate else best) 0

/--
Whether a word is the first 32 fractional bits of the square root of a prime.

With `root = ⌊√prime⌋ · 2^32 + word`, it is exactly when `root² ≤ prime · 2^64 < (root + 1)²`.
-/
def squareRootFraction (prime word : Nat) : Bool :=
  let root := wholeSquareRoot prime * 2 ^ 32 + word
  root ^ 2 ≤ prime * 2 ^ 64 && prime * 2 ^ 64 < (root + 1) ^ 2

/--
Whether a word is the first 32 fractional bits of the cube root of a prime.

With `root = ⌊∛prime⌋ · 2^32 + word`, it is exactly when `root³ ≤ prime · 2^96 < (root + 1)³`.
-/
def cubeRootFraction (prime word : Nat) : Bool :=
  let root := wholeCubeRoot prime * 2 ^ 32 + word
  root ^ 3 ≤ prime * 2 ^ 96 && prime * 2 ^ 96 < (root + 1) ^ 3

/--
The initial hash value is the one that FIPS 180-4 §5.3.3 derives.

It comes from the square roots of the first 8 primes.

So no initial word is taken on trust.
-/
theorem IV_from_primes :
    (smallPrimes 20).length = 8 ∧ IV.toList.length = 8 ∧
      ((smallPrimes 20).zip (IV.toList.map UInt32.toNat)).all
        (fun pair => squareRootFraction pair.1 pair.2) = true := by
  decide +kernel

/--
The round constants are the ones that FIPS 180-4 §4.2.2 derives.

They come from the cube roots of the first 64 primes.

So no round constant is taken on trust.
-/
theorem K_from_primes :
    (smallPrimes 312).length = 64 ∧ K.toList.length = 64 ∧
      ((smallPrimes 312).zip (K.toList.map UInt32.toNat)).all
        (fun pair => cubeRootFraction pair.1 pair.2) = true := by
  decide +kernel

/-! ## The functions on words -/

/-- The executable σ0 is σ0 of FIPS 180-4 §4.1.2. -/
theorem smallSigma0_toBitVec (x : UInt32) : (smallSigma0 x).toBitVec = Spec.small0 x.toBitVec := by
  -- Each pair of shifts joined by an or is a rotation.
  simp [smallSigma0, rotr, shr, Spec.small0, BitVec.rotateRight_def]

/-- The executable σ1 is σ1 of FIPS 180-4 §4.1.2. -/
theorem smallSigma1_toBitVec (x : UInt32) : (smallSigma1 x).toBitVec = Spec.small1 x.toBitVec := by
  simp [smallSigma1, rotr, shr, Spec.small1, BitVec.rotateRight_def]

/-- The executable Σ0 is Σ0 of FIPS 180-4 §4.1.2. -/
theorem bigSigma0_toBitVec (x : UInt32) : (bigSigma0 x).toBitVec = Spec.large0 x.toBitVec := by
  simp [bigSigma0, rotr, Spec.large0, BitVec.rotateRight_def]

/-- The executable Σ1 is Σ1 of FIPS 180-4 §4.1.2. -/
theorem bigSigma1_toBitVec (x : UInt32) : (bigSigma1 x).toBitVec = Spec.large1 x.toBitVec := by
  simp [bigSigma1, rotr, Spec.large1, BitVec.rotateRight_def]

/-- Four bytes of a byte array, read as one big-endian word, FIPS 180-4 §3.1. -/
theorem big32_toBitVec (b : ByteArray) (off : Nat) :
    (big32 b[off]! b[off + 1]! b[off + 2]! b[off + 3]!).toBitVec = Spec.inputWord b off := by
  -- Widening a byte keeps its value.
  have byte (v : UInt8) : v.toBitVec.setWidth 32 = BitVec.ofNat 32 v.toNat :=
    BitVec.eq_of_toNat_eq (by simp)
  simp [big32, Spec.inputWord, byte]

/-! ## The message schedule -/

/-- The schedule words of the model, as machine words. -/
private def scheduleWord (input : Vector Spec.Word 16) (t : Nat) : UInt32 :=
  UInt32.ofBitVec (Spec.messageWord input t)

/-- The window of sixteen values of a sequence of words. -/
private def windowOf (f : Nat → UInt32) : Window :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15⟩

/-- The first word of a window. -/
private theorem windowOf_w0 (f : Nat → UInt32) : (windowOf f).w0 = f 0 := rfl

/-- The first window holds the words of the block, FIPS 180-4 §6.2.2, step 1. -/
private theorem ofBlock_block (block : ByteArray) (start : Nat) (whole : start + 64 ≤ block.size) :
    Window.ofBlock block start whole
      = windowOf fun i => scheduleWord (Spec.inputWords block start) (0 + i) := by
  -- Each of the sixteen words reads four bytes of the block.
  have word (i : Nat) (input : i < 16) :
      big32 (block[start + 4 * i]'(by omega)) (block[start + 4 * i + 1]'(by omega))
          (block[start + 4 * i + 2]'(by omega)) (block[start + 4 * i + 3]'(by omega))
        = scheduleWord (Spec.inputWords block start) (0 + i) := by
    apply UInt32.toBitVec_inj.mp
    rw [scheduleWord, UInt32.toBitVec_ofBitVec, Nat.zero_add, Spec.messageWord]
    simp only [input, ↓reduceDIte, Spec.inputWords, Vector.getElem_ofFn]
    have read := big32_toBitVec block (start + 4 * i)
    simp (disch := omega) only [getElem!_pos] at read
    exact read
  simp (disch := decide) only [Window.ofBlock, windowOf, word]

/-- Each move of the window is one more word of the schedule, by the recurrence. -/
private theorem next_windowOf (input : Vector Spec.Word 16) (t : Nat) :
    (windowOf fun i => scheduleWord input (t + i)).next
      = windowOf fun i => scheduleWord input (t + 1 + i) := by
  have last : scheduleWord input (t + 16) = scheduleWord input t +
      smallSigma0 (scheduleWord input (t + 1)) + scheduleWord input (t + 9) +
      smallSigma1 (scheduleWord input (t + 14)) := by
    apply UInt32.toBitVec_inj.mp
    simp only [scheduleWord, UInt32.toBitVec_add, smallSigma0_toBitVec, smallSigma1_toBitVec,
      UInt32.toBitVec_ofBitVec]
    rw [Spec.messageWord]
    simp only [show ¬ t + 16 < 16 by omega, ↓reduceDIte, show t + 16 - 16 = t by omega,
      show t + 16 - 15 = t + 1 by omega, show t + 16 - 7 = t + 9 by omega,
      show t + 16 - 2 = t + 14 by omega]
  -- The other words only move one place.
  simp only [Window.next, windowOf, last, Nat.add_zero, Nat.add_assoc]

/-! ## One block -/

/-- A state read as the model's working variables. -/
def interpret (s : State) : Spec.State :=
  ⟨s.a.toBitVec, s.b.toBitVec, s.c.toBitVec, s.d.toBitVec,
    s.e.toBitVec, s.f.toBitVec, s.g.toBitVec, s.h.toBitVec⟩

/-- One round is one round of the model. -/
theorem round_toState (s : State) (constant word : UInt32) :
    interpret (round s constant word) =
      Spec.step (interpret s) constant.toBitVec word.toBitVec := by
  -- Machine addition and bit operations are the model's, word for word.
  simp [interpret, round, Spec.step, ch, maj, bigSigma0_toBitVec, bigSigma1_toBitVec]

/-- The rounds from any round on finish the model's rounds. -/
private theorem rounds_toState (input : Vector Spec.Word 16) (initial : Spec.State) :
    ∀ m n, m + n = 64 → ∀ s, interpret s = Spec.rounds input initial n →
      interpret (rounds (K.toList.drop n) (windowOf fun i => scheduleWord input (n + i)) s)
        = Spec.rounds input initial 64 := by
  intro m
  induction m with
  | zero =>
    intro n sum s hs
    -- After the last round, no constant is left.
    obtain rfl : n = 64 := by omega
    exact hs
  | succ m ih =>
    intro n sum s hs
    -- Round `n` takes constant `K_n` and the first word of the window, `W_n`.
    rw [List.drop_eq_getElem_cons (by simp; omega), rounds, next_windowOf]
    apply ih (n + 1) (by omega)
    rw [windowOf_w0, round_toState, hs, Spec.rounds, Nat.add_zero, scheduleWord,
      UInt32.toBitVec_ofBitVec, Vector.getElem_toList, getElem!_pos K n (by omega)]

/-- The compression of a whole block is the one of FIPS 180-4 §6.2.2, steps 2 to 4. -/
theorem compress_toState (s : State) (block : ByteArray) (start : Nat)
    (whole : start + 64 ≤ block.size) :
    interpret (compress s block start whole) =
      Spec.compression (Spec.inputWords block start) (interpret s) := by
  have all := rounds_toState (Spec.inputWords block start) (interpret s) 64 0 rfl s rfl
  simp only [compress]
  rw [ofBlock_block block start whole]
  simp only [List.drop_zero] at all
  simp only [Spec.compression, ← all]
  simp [interpret]

/-! ## Padding -/

/-- The length takes eight bytes. -/
@[simp] theorem lengthBytes_size (size : Nat) : (lengthBytes size).size = 8 := by
  simp only [lengthBytes, ByteArray.size, Array.size_ofFn]

/-- Padding adds the `0x80` byte, the zeros, and the eight length bytes. -/
theorem pad_size (message : ByteArray) :
    (pad message).size = message.size + 1 + paddingZeros message.size + 8 := by
  simp only [pad, ByteArray.size_append, lengthBytes_size]
  -- The `0x80` byte is one byte, and the zeros are as many as they count.
  show message.size + 1 + (Array.replicate (paddingZeros message.size) (0 : UInt8)).size + 8 = _
  rw [Array.size_replicate]

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

private theorem bits_toNat (size : Nat) (admitted : size < 2 ^ 61) :
    (UInt64.ofNat size * 8).toNat = size * 8 := by
  -- Below 2⁶¹ bytes, the bit count does not wrap.
  simp [UInt64.toNat_mul, UInt64.toNat_ofNat]
  omega

private theorem offset_toNat (i : Fin 8) : (8 * UInt64.ofNat i.val).toNat = 8 * i.val := by
  simp [UInt64.toNat_mul, UInt64.toNat_ofNat]
  omega

private theorem shift_toNat (i : Fin 8) : (56 - 8 * UInt64.ofNat i.val).toNat = 56 - 8 * i.val := by
  rw [UInt64.toNat_sub_of_le]
  · simp only [offset_toNat]; rfl
  · apply UInt64.le_iff_toNat_le.mpr
    rw [offset_toNat]
    change 8 * i.val ≤ 56
    omega

/-- Below 2⁶¹ bytes, the length bytes are the base-256 digits of the bit length. -/
theorem lengthBytes_digit (size : Nat) (admitted : size < 2 ^ 61) (i : Fin 8) :
    ((lengthBytes size)[i.val]'(by simp)).toNat = (size * 8 / 2 ^ (56 - 8 * i.val)) % 256 := by
  simp only [lengthBytes, ByteArray.getElem_eq_getElem_data, Array.getElem_ofFn,
    UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, bits_toNat size admitted, shift_toNat]
  change ((size * 8) >>> ((56 - 8 * i.val) % 64)) % 256 = _
  rw [Nat.mod_eq_of_lt (show 56 - 8 * i.val < 64 by omega), Nat.shiftRight_eq_div_pow]

/-- The padding is the one of FIPS 180-4 §5.1.1, below 2⁶¹ bytes. -/
theorem pad_eq_spec (message : ByteArray) (admitted : message.size < 2 ^ 61) :
    pad message = Spec.padded message := by
  have zeros : paddingZeros message.size = Spec.zeroCount message.size := by
    unfold paddingZeros Spec.zeroCount
    omega
  have length : (lengthBytes message.size).data =
      Array.ofFn fun i : Fin 8 =>
        UInt8.ofNat ((message.size * 8 / 2 ^ (56 - 8 * i.val)) % 256) := by
    apply Array.ext
    · exact (lengthBytes_size message.size).trans Array.size_ofFn.symm
    · intro p left right
      apply UInt8.toNat_inj.mp
      simpa [ByteArray.getElem_eq_getElem_data] using
        lengthBytes_digit message.size admitted ⟨p, by simpa using left⟩
  -- The message, the `0x80` byte, the zeros and the length agree region by region.
  apply ByteArray.ext
  simp [pad, Spec.padded, zeros, length, ByteArray.data_append]

/-! ## The hash -/

/-- Every digest is 32 bytes long, whatever the message. -/
@[simp] theorem hash_size (message : ByteArray) : (hash message).size = 32 := by
  simp only [hash, digest, ByteArray.size, List.size_toArray, List.length_cons, List.length_nil]

/-- The blocks from any block on continue the model's chain of blocks. -/
theorem chain_toState (block : ByteArray) (initial : Spec.State) :
    ∀ count first start s (whole : start + 64 * count ≤ block.size), start = 64 * first →
      interpret s = Spec.blocks block initial first →
      interpret (chain compress block count start whole s)
        = Spec.blocks block initial (first + count) := by
  intro count
  induction count with
  | zero => intro first start s _ _ hs; exact hs
  | succ count ih =>
    intro first start s whole hstart hs
    -- One block, then the rest from the next block on.
    rw [chain, show first + (count + 1) = first + 1 + count by omega]
    apply ih (first + 1) (start + 64) _ _ (by omega)
    rw [compress_toState s block start (by omega), hs, hstart, Spec.blocks]

/-- The digest is the model's digest. -/
theorem digest_eq_spec (s : State) : digest s = Spec.digest (interpret s) := by
  apply ByteArray.ext
  simp only [digest, byteAt, Spec.digest, Spec.State.words, interpret]
  apply Array.toList_inj.mp
  simp only [Array.toList_ofFn, List.ofFn_succ, List.ofFn_zero,
    Fin.val_succ, Fin.val_zero]
  -- Each output byte is one base-256 digit of its word.
  simp only [List.cons.injEq, and_true]
  repeat' constructor
  all_goals (apply UInt8.toNat_inj.mp; simp [Nat.shiftRight_eq_div_pow])

/--
SHA-256 is the hash of FIPS 180-4 §6.2, on every message shorter than 2⁶¹ bytes.

FIPS 180-4 §5.1.1 bounds a message at 2⁶⁴ bits, which is 2⁶¹ bytes.
-/
theorem hash_eq_spec (message : ByteArray) (admitted : message.size < 2 ^ 61) :
    hash message = Spec.hash message := by
  have start : interpret initial = Spec.initial := by decide
  -- The padded bytes are the model's, and the chain then runs over them.
  have padded : ∀ bytes, bytes = Spec.padded message → ∀ whole,
      digest (chain compress bytes (bytes.size / 64) 0 whole initial) = Spec.hash message := by
    intro bytes same whole
    subst same
    rw [digest_eq_spec, chain_toState _ Spec.initial _ 0 0 initial whole (by omega) start,
      Nat.zero_add, Spec.hash]
  exact padded (pad message) (pad_eq_spec message admitted) _

end EthLib.Cryptography.Hash.Sha256
