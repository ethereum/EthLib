module

public import EthLib.Base.Bytes
public import EthLib.Cryptography.Hash.Sha256

/-!
# Proofs: SHA-256

SHA-256 agrees with FIPS 180-4 on every message shorter than 2^61 bytes.

The file restates the standard as a model over 32-bit bit vectors.

The model shares only the 64 round constants with the executable code.

A theorem below derives them from the cube roots of the first 64 primes.

The last section states the padding and the words of a block on bit strings, as the standard does.
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
  ⟨w.a + initial.a, w.b + initial.b, w.c + initial.c, w.d + initial.d,
    w.e + initial.e, w.f + initial.f, w.g + initial.g, w.h + initial.h⟩

/-- The initial hash value, FIPS 180-4 §5.3.3. -/
def initial : State :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

/-- The number of zero bytes after the `0b10000000` byte, FIPS 180-4 §5.1.1. -/
def zeroCount (size : Nat) : Nat := (119 - size % 64) % 64

/--
The padded message, FIPS 180-4 §5.1.1.

It is the message, `0b10000000`, zeros, and the bit length in eight big-endian bytes.
-/
def padded (message : ByteArray) : ByteArray :=
  ⟨message.data ++ #[0b10000000] ++ Array.replicate (zeroCount message.size) 0 ++
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

Trial division stops at 17, since every composite below 18^2 has a divisor that small.
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

With `root = ⌊√prime⌋ · 2^32 + word`, it is exactly when `root^2 ≤ prime · 2^64 < (root + 1)^2`.
-/
def squareRootFraction (prime word : Nat) : Bool :=
  let root := wholeSquareRoot prime * 2 ^ 32 + word
  root ^ 2 ≤ prime * 2 ^ 64 && prime * 2 ^ 64 < (root + 1) ^ 2

/--
Whether a word is the first 32 fractional bits of the cube root of a prime.

With `root = ⌊∛prime⌋ · 2^32 + word`, it is exactly when `root^3 ≤ prime · 2^96 < (root + 1)^3`.
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
  simp [smallSigma0, rotr, WORD_BITS, shr, Spec.small0, BitVec.rotateRight_def]

/-- The executable σ1 is σ1 of FIPS 180-4 §4.1.2. -/
theorem smallSigma1_toBitVec (x : UInt32) : (smallSigma1 x).toBitVec = Spec.small1 x.toBitVec := by
  simp [smallSigma1, rotr, WORD_BITS, shr, Spec.small1, BitVec.rotateRight_def]

/-- The executable Σ0 is Σ0 of FIPS 180-4 §4.1.2. -/
theorem bigSigma0_toBitVec (x : UInt32) : (bigSigma0 x).toBitVec = Spec.large0 x.toBitVec := by
  simp [bigSigma0, rotr, WORD_BITS, Spec.large0, BitVec.rotateRight_def]

/-- The executable Σ1 is Σ1 of FIPS 180-4 §4.1.2. -/
theorem bigSigma1_toBitVec (x : UInt32) : (bigSigma1 x).toBitVec = Spec.large1 x.toBitVec := by
  simp [bigSigma1, rotr, WORD_BITS, Spec.large1, BitVec.rotateRight_def]

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

/-- The schedule one word later: the window drops `W_t` and gains `W_(t+16)`. -/
private def shift (w : Window) : Window :=
  ⟨w.w1, w.w2, w.w3, w.w4, w.w5, w.w6, w.w7, w.w8, w.w9, w.w10, w.w11, w.w12, w.w13, w.w14, w.w15,
    w.w0 + smallSigma0 w.w1 + w.w9 + smallSigma1 w.w14⟩

/-- The rounds one at a time: each takes the next constant and the first word of the window. -/
private def roundsList : List UInt32 → Window → State → State
  | [], _, s => s
  | K_t :: rest, w, s => roundsList rest (shift w) (round s K_t w.w0)

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
  -- The window numbers its words in `Fin 16`, whose values `0` to `15` are those numbers.
  rfl

/-- Each move of the window is one more word of the schedule, by the recurrence. -/
private theorem next_windowOf (input : Vector Spec.Word 16) (t : Nat) :
    shift (windowOf fun i => scheduleWord input (t + i))
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
  simp only [shift, windowOf, last, Nat.add_zero, Nat.add_assoc]

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
      interpret (roundsList (K.toList.drop n) (windowOf fun i => scheduleWord input (n + i)) s)
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
    rw [List.drop_eq_getElem_cons (by simp; omega), roundsList, next_windowOf]
    apply ih (n + 1) (by omega)
    rw [windowOf_w0, round_toState, hs, Spec.rounds, Nat.add_zero, scheduleWord,
      UInt32.toBitVec_ofBitVec, Vector.getElem_toList, getElem!_pos K n (by omega)]

/-- The constants as a list are the constants in order. -/
private theorem K_toList : K.toList =
    [K[0], K[1], K[2], K[3], K[4], K[5], K[6], K[7], K[8], K[9], K[10], K[11], K[12], K[13],
      K[14], K[15], K[16], K[17], K[18], K[19], K[20], K[21], K[22], K[23], K[24], K[25], K[26],
      K[27], K[28], K[29], K[30], K[31], K[32], K[33], K[34], K[35], K[36], K[37], K[38], K[39],
      K[40], K[41], K[42], K[43], K[44], K[45], K[46], K[47], K[48], K[49], K[50], K[51], K[52],
      K[53], K[54], K[55], K[56], K[57], K[58], K[59], K[60], K[61], K[62], K[63]] := rfl

/-- Sixteen rounds one word at a time end on the window sixteen words later. -/
private theorem roundsList_sixteen (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : UInt32)
    (rest : List UInt32) (w : Window) (s : State) :
    roundsList (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 ::
        c13 :: c14 :: c15 :: rest) w s =
      roundsList rest w.next
        (round (round (round (round (round (round (round (round (round (round (round (round
          (round (round (round (round s c0 w.w0) c1 w.w1) c2 w.w2) c3 w.w3) c4 w.w4) c5 w.w5)
          c6 w.w6) c7 w.w7) c8 w.w8) c9 w.w9) c10 w.w10) c11 w.w11) c12 w.w12) c13 w.w13)
          c14 w.w14) c15 w.w15) := rfl

/-- Sixteen rounds on a window that moves sixteen words are the rounds one word at a time. -/
private theorem compress_eq (s : State) (block : ByteArray) (start : Nat)
    (whole : start + 64 ≤ block.size) :
    compress s block start whole =
      let r := roundsList K.toList (Window.ofBlock block start whole) s
      { a := r.a + s.a, b := r.b + s.b, c := r.c + s.c, d := r.d + s.d,
        e := r.e + s.e, f := r.f + s.f, g := r.g + s.g, h := r.h + s.h } := by
  rw [K_toList, roundsList_sixteen, roundsList_sixteen, roundsList_sixteen, roundsList_sixteen,
    roundsList]
  rfl

/-- The compression of a whole block is the one of FIPS 180-4 §6.2.2, steps 2 to 4. -/
theorem compress_toState (s : State) (block : ByteArray) (start : Nat)
    (whole : start + 64 ≤ block.size) :
    interpret (compress s block start whole) =
      Spec.compression (Spec.inputWords block start) (interpret s) := by
  have all := rounds_toState (Spec.inputWords block start) (interpret s) 64 0 rfl s rfl
  rw [compress_eq]
  simp only
  rw [ofBlock_block block start whole]
  simp only [List.drop_zero] at all
  simp only [Spec.compression, ← all]
  simp [interpret]

/-! ## Padding -/

/-- Byte `i` of the length is the low eight bits of the bit length shifted right by `56 - 8 i`. -/
private theorem lengthBytes_eq_ofFn (size : Nat) : lengthBytes size =
    ⟨Array.ofFn fun i : Fin 8 =>
      ((UInt64.ofNat size * 8) >>> (56 - 8 * UInt64.ofNat i.val)).toUInt8⟩ := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [lengthBytes, ByteArray.push, ByteArray.emptyWithCapacity, List.ofFn_succ]
  rfl

/-- The length takes eight bytes. -/
@[simp] theorem lengthBytes_size (size : Nat) : (lengthBytes size).size = 8 := by
  simp only [lengthBytes_eq_ofFn, ByteArray.size, Array.size_ofFn]

private theorem bits_toNat (size : Nat) (admitted : size < 2 ^ 61) :
    (UInt64.ofNat size * 8).toNat = size * 8 := by
  -- Below 2^61 bytes, the bit count does not wrap.
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

/-- Below 2^61 bytes, the length bytes are the base-256 digits of the bit length. -/
theorem lengthBytes_digit (size : Nat) (admitted : size < 2 ^ 61) (i : Fin 8) :
    ((lengthBytes size)[i.val]'(by simp)).toNat = (size * 8 / 2 ^ (56 - 8 * i.val)) % 256 := by
  simp only [lengthBytes_eq_ofFn, ByteArray.getElem_eq_getElem_data, Array.getElem_ofFn,
    UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, bits_toNat size admitted, shift_toNat]
  change ((size * 8) >>> ((56 - 8 * i.val) % 64)) % 256 = _
  rw [Nat.mod_eq_of_lt (show 56 - 8 * i.val < 64 by omega), Nat.shiftRight_eq_div_pow]

/-- The padding is the one of FIPS 180-4 §5.1.1, below 2^61 bytes. -/
theorem pad_eq_spec (message : ByteArray) (admitted : message.size < 2 ^ 61) :
    pad message = Spec.padded message := by
  have zeros : Padding.paddingZeros message.size = Spec.zeroCount message.size := by
    unfold Padding.paddingZeros Spec.zeroCount
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
  -- The message, the `0b10000000` byte, the zeros and the length agree region by region.
  apply ByteArray.ext
  simp [pad, Padding.pad, Spec.padded, zeros, length, ByteArray.data_append, ByteArray.push]

/-! ## The hash -/

/-- The digest is the 32 bytes of the eight words, each most significant byte first. -/
private theorem digest_eq_bytes (H : State) : digest H =
    ⟨#[byteAt H.a 24, byteAt H.a 16, byteAt H.a 8, byteAt H.a 0,
      byteAt H.b 24, byteAt H.b 16, byteAt H.b 8, byteAt H.b 0,
      byteAt H.c 24, byteAt H.c 16, byteAt H.c 8, byteAt H.c 0,
      byteAt H.d 24, byteAt H.d 16, byteAt H.d 8, byteAt H.d 0,
      byteAt H.e 24, byteAt H.e 16, byteAt H.e 8, byteAt H.e 0,
      byteAt H.f 24, byteAt H.f 16, byteAt H.f 8, byteAt H.f 0,
      byteAt H.g 24, byteAt H.g 16, byteAt H.g 8, byteAt H.g 0,
      byteAt H.h 24, byteAt H.h 16, byteAt H.h 8, byteAt H.h 0]⟩ := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [digest, pushWord, ByteArray.push, ByteArray.emptyWithCapacity]
  rfl

/-- Every digest is 32 bytes long, whatever the message. -/
@[simp] theorem hash_size (message : ByteArray) : (hash message).size = 32 := by
  simp only [hash, digest_eq_bytes]
  rfl

/-- The 32-byte digest holds exactly the bytes of the byte-array digest. -/
@[simp] theorem packBytes_hash32 (message : ByteArray) :
    Base.packBytes (hash32 message) = hash message := rfl

/-- The blocks from any block on continue the model's chain of blocks. -/
theorem chain_toState (block : ByteArray) (initial : Spec.State) :
    ∀ count first start s (whole : start + BLOCK_SIZE_BYTES * count ≤ block.size),
      start = BLOCK_SIZE_BYTES * first →
      interpret s = Spec.blocks block initial first →
      interpret (chain compress block count start whole s)
        = Spec.blocks block initial (first + count) := by
  intro count
  induction count with
  | zero => intro first start s _ _ hs; exact hs
  | succ count ih =>
    intro first start s whole hstart hs
    -- One block, then the rest from the next block on.
    -- A block is 64 bytes.
    have blocks : start + 64 * (count + 1) ≤ block.size := whole
    unfold BLOCK_SIZE_BYTES at hstart
    rw [chain, show first + (count + 1) = first + 1 + count by omega]
    apply ih (first + 1) (start + BLOCK_SIZE_BYTES) _ _ (by unfold BLOCK_SIZE_BYTES; omega)
    rw [compress_toState s block start (by omega), hs, hstart, Spec.blocks]

/-- The digest is the model's digest. -/
theorem digest_eq_spec (s : State) : digest s = Spec.digest (interpret s) := by
  apply ByteArray.ext
  rw [digest_eq_bytes]
  simp only [byteAt, Spec.digest, Spec.State.words, interpret]
  apply Array.toList_inj.mp
  simp only [Array.toList_ofFn, List.ofFn_succ, List.ofFn_zero,
    Fin.val_succ, Fin.val_zero]
  -- Each output byte is one base-256 digit of its word.
  simp only [List.cons.injEq, and_true]
  repeat' constructor
  all_goals (apply UInt8.toNat_inj.mp; simp [Nat.shiftRight_eq_div_pow])

/--
SHA-256 is the hash of FIPS 180-4 §6.2, on every message shorter than 2^61 bytes.

FIPS 180-4 §5.1.1 bounds a message at 2^64 bits, which is 2^61 bytes.
-/
theorem hash_eq_spec (message : ByteArray) (admitted : message.size < 2 ^ 61) :
    hash message = Spec.hash message := by
  have start : interpret initial = Spec.initial := by decide
  -- The padded bytes are the model's, and the chain then runs over them.
  have padded : ∀ bytes, bytes = Spec.padded message → ∀ whole,
      digest (chain compress bytes (bytes.size / BLOCK_SIZE_BYTES) 0 whole initial)
        = Spec.hash message := by
    intro bytes same whole
    subst same
    rw [digest_eq_spec, chain_toState _ Spec.initial _ 0 0 initial whole (by omega) start,
      Nat.zero_add, Spec.hash]
    -- A block is 64 bytes.
    rfl
  exact padded (pad message) (pad_eq_spec message admitted) _

/-- The 32-byte digest agrees with FIPS 180-4 on every message shorter than 2^61 bytes. -/
theorem hash32_eq_spec (message : ByteArray) (admitted : message.size < 2 ^ 61) :
    Base.packBytes (hash32 message) = Spec.hash message :=
  hash_eq_spec message admitted

/-! ## The message in bits

FIPS 180-4 defines the padding and the parsing on bit strings.

The statements below read the byte arrays as those bit strings.

So they state the standard's own text.
-/

namespace Spec

/-- The bits of one byte, most significant first, FIPS 180-4 §3.1. -/
def byteBits (byte : UInt8) : List Bool := (List.range 8).reverse.map byte.toNat.testBit

/-- The bits of a byte string, FIPS 180-4 §3.1: its bytes in order, most significant bit first. -/
def messageBits (bytes : ByteArray) : List Bool := bytes.toList.flatMap byteBits

/--
The padding of a message `M` of `ℓ` bits, FIPS 180-4 §5.1.1.

It appends the bit 1, then `k` zero bits, then the low 64 bits of `ℓ`, most significant first.

FIPS 180-4 §5.1.1 admits only `ℓ < 2^64`, where these 64 bits are `ℓ` itself.

The number `k` is the smallest non-negative solution of `ℓ + 1 + k ≡ 448 (mod 512)`.
-/
def bitPad (M : List Bool) : List Bool :=
  let ℓ := M.length
  -- The solutions repeat every 512, so the smallest one is below 512.
  let k := ((List.range 512).find? fun k => (ℓ + 1 + k) % 512 = 448).getD 0
  M ++ [true] ++ List.replicate k false ++ (List.range 64).reverse.map ℓ.testBit

/-- The loop that lists a byte array reads the array from the index on. -/
private theorem toList_loop (b : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i := by
  fun_induction ByteArray.toList.loop b i r with
  | case1 i r h ih =>
    rw [ih]
    have : i < b.data.toList.length := by simpa using h
    rw [List.drop_eq_getElem_cons this]
    have inside : i < b.data.size := h
    simp [ByteArray.get!]
    exact getElem!_pos b.data i inside
  | case2 i r h =>
    simp at h
    simp [List.drop_eq_nil_of_le (show b.data.toList.length ≤ i by simpa using h)]

/-- The list of a byte array is the list of its bytes. -/
private theorem toList_eq (b : ByteArray) : b.toList = b.data.toList := by
  simp [ByteArray.toList, toList_loop]

/-- The zero byte is eight zero bits. -/
theorem byteBits_zero : byteBits 0 = List.replicate 8 false := by
  simp [byteBits, List.range_succ]

/-- A byte has eight bits. -/
@[simp] theorem byteBits_length (byte : UInt8) : (byteBits byte).length = 8 := by
  simp [byteBits]

/-- Bit `r` from the left of a byte is bit `7 - r` of its value. -/
theorem byteBits_getElem (byte : UInt8) (r : Nat) (h : r < (byteBits byte).length) :
    (byteBits byte)[r] = byte.toNat.testBit (7 - r) := by
  simp [byteBits]

/-- The bits of a byte string are the bits of its bytes, in order. -/
theorem messageBits_eq (b : ByteArray) : messageBits b = b.data.toList.flatMap byteBits := by
  rw [messageBits, toList_eq]

/-- Each byte contributes eight bits. -/
theorem flatMap_byteBits_length (l : List UInt8) : (l.flatMap byteBits).length = 8 * l.length := by
  induction l with
  | nil => simp
  | cons x l ih => simp [List.flatMap_cons, ih]; omega

/-- Bit `j` of a list of bytes is a bit of byte `j / 8`. -/
theorem flatMap_byteBits_getElem (l : List UInt8) (j : Nat) (h : j < (l.flatMap byteBits).length) :
    (l.flatMap byteBits)[j] =
      (l[j / 8]'(by rw [flatMap_byteBits_length] at h; omega)).toNat.testBit (7 - j % 8) := by
  induction l generalizing j with
  | nil => simp at h
  | cons x l ih =>
    rw [flatMap_byteBits_length] at h
    simp only [List.flatMap_cons]
    by_cases small : j < 8
    · have quotient : j / 8 = 0 := Nat.div_eq_of_lt small
      have remainder : j % 8 = j := Nat.mod_eq_of_lt small
      rw [List.getElem_append_left (by simpa using small), byteBits_getElem]
      simp [quotient, remainder]
    · rw [List.getElem_append_right (by simpa using small)]
      rw [ih]
      have quotient : (j - 8) / 8 + 1 = j / 8 := by omega
      have remainder : (j - 8) % 8 = j % 8 := by omega
      simp [remainder, ← quotient]

/-- The bits of two byte strings put end to end are their bits put end to end. -/
theorem messageBits_append (a b : ByteArray) :
    messageBits (a ++ b) = messageBits a ++ messageBits b := by
  simp [messageBits_eq, List.flatMap_append]

/-- Appending a byte appends its eight bits. -/
theorem messageBits_push (a : ByteArray) (x : UInt8) :
    messageBits (a.push x) = messageBits a ++ byteBits x := by
  simp [messageBits_eq]

/-- A byte string of `n` bytes has `8 n` bits. -/
theorem messageBits_length (b : ByteArray) : (messageBits b).length = 8 * b.size := by
  rw [messageBits_eq, flatMap_byteBits_length]
  simp

/-- Bit `j` of a byte string is bit `7 - j % 8` of byte `j / 8`. -/
theorem messageBits_getElem (b : ByteArray) (j : Nat) (h : j < (messageBits b).length) :
    (messageBits b)[j] =
      (b[j / 8]'(by rw [messageBits_length] at h; omega)).toNat.testBit (7 - j % 8) := by
  simp only [messageBits_eq] at h ⊢
  rw [flatMap_byteBits_getElem]
  rfl

/-- `n` zero bytes are `8 n` zero bits. -/
theorem messageBits_replicate_zero (n : Nat) :
    messageBits ⟨Array.replicate n 0⟩ = List.replicate (8 * n) false := by
  induction n with
  | zero => simp [messageBits_eq]
  | succ n ih =>
    simp [messageBits_eq, List.replicate_succ, List.flatMap_cons, byteBits_zero] at ih ⊢
    rw [ih, show 8 * (n + 1) = 8 + 8 * n by omega, ← List.replicate_append_replicate]
    rfl

end Spec

/-- The 64 bits of the length are the low bits of the bit length, `8 size` modulo 2^64. -/
theorem messageBits_lengthBytes (size : Nat) :
    Spec.messageBits (lengthBytes size) = (List.range 64).reverse.map (8 * size).testBit := by
  apply List.ext_getElem
  · simp [Spec.messageBits_length]
  · intro j left right
    rw [Spec.messageBits_getElem]
    simp only [lengthBytes_eq_ofFn, ByteArray.getElem_eq_getElem_data, Array.getElem_ofFn,
      UInt64.toNat_toUInt8, UInt64.toNat_shiftRight]
    have inside : j < 64 := by simpa using right
    have shift : (56 - 8 * UInt64.ofNat (j / 8)).toNat = 56 - 8 * (j / 8) :=
      shift_toNat ⟨j / 8, by omega⟩
    rw [shift, Nat.mod_eq_of_lt (show 56 - 8 * (j / 8) < 64 by omega)]
    simp only [UInt64.toNat_mul, List.getElem_map, List.getElem_reverse,
      List.getElem_range, List.length_range]
    have byte : 7 - j % 8 < 8 := by omega
    have index : 56 - 8 * (j / 8) + (7 - j % 8) = 64 - 1 - j := by omega
    have bits : (UInt64.ofNat size).toNat * UInt64.toNat 8 % 2 ^ 64 = 8 * size % 2 ^ 64 := by
      simp only [UInt64.toNat_ofNat', UInt64.toNat_ofNat]
      omega
    rw [bits, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow, index]
    simp [byte]
    omega

namespace Spec

/-- The padding congruence of FIPS 180-4 §5.1.1 first holds at `7` plus eight bits per zero byte. -/
theorem find_padding_bits (size : Nat) :
    ((List.range 512).find? fun k => (8 * size + 1 + k) % 512 = 448).getD 0 =
      7 + 8 * Padding.paddingZeros size := by
  have below : Padding.paddingZeros size < 64 := by
    unfold Padding.paddingZeros
    omega
  have found : (List.range 512).find? (fun k => decide ((8 * size + 1 + k) % 512 = 448)) =
      some (7 + 8 * Padding.paddingZeros size) := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨?_, 7 + 8 * Padding.paddingZeros size, by simp; omega, by simp, ?_⟩
    · simp only [decide_eq_true_eq]
      unfold Padding.paddingZeros
      omega
    · intro j smaller
      simp only [List.getElem_range, Bool.not_eq_true', decide_eq_false_iff_not]
      unfold Padding.paddingZeros at smaller
      omega
  rw [found]
  rfl

/-- The byte `0x80` is the bit 1 and seven zero bits, FIPS 180-4 §5.1.1. -/
theorem byteBits_delimiter : byteBits 0x80 = true :: List.replicate 7 false := by
  decide

end Spec

/--
The padded bytes are the padded bits of FIPS 180-4 §5.1.1.

The 64 length bits are the low bits of `ℓ`, so the statement needs no bound on the message.
-/
theorem pad_bits (message : ByteArray) :
    Spec.messageBits (pad message) = Spec.bitPad (Spec.messageBits message) := by
  unfold Spec.bitPad
  simp only [Spec.messageBits_length, Spec.find_padding_bits]
  -- The message, the delimiter byte, the zero bytes and the length are the four parts.
  simp only [pad, Padding.pad, Spec.messageBits_append, Spec.messageBits_push,
    Spec.messageBits_replicate_zero, messageBits_lengthBytes, Spec.byteBits_delimiter]
  rw [← List.replicate_append_replicate]
  simp [List.append_assoc]

/-- A word of a block is its 32 bits from the offset, FIPS 180-4 §5.2.1, byte by byte. -/
private theorem inputWord_getMsbD (block : ByteArray) (start : Nat) (whole : start + 4 ≤ block.size)
    (i : Nat) (inside : i < 32) :
    (Spec.inputWord block start).getMsbD i =
      (block[start + i / 8]'(by omega)).toNat.testBit (7 - i % 8) := by
  have b0 : block[start]! = block[start]'(by omega) := getElem!_pos block start (by omega)
  have b1 : block[start + 1]! = block[start + 1]'(by omega) :=
    getElem!_pos block (start + 1) (by omega)
  have b2 : block[start + 2]! = block[start + 2]'(by omega) :=
    getElem!_pos block (start + 2) (by omega)
  have b3 : block[start + 3]! = block[start + 3]'(by omega) :=
    getElem!_pos block (start + 3) (by omega)
  obtain ⟨q, r, hr, hq, rfl⟩ : ∃ q r, r < 8 ∧ q < 4 ∧ i = 8 * q + r :=
    ⟨i / 8, i % 8, by omega, by omega, by omega⟩
  have high (byte : UInt8) (k : Nat) (above : 8 ≤ k) : byte.toNat.testBit k = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (UInt8.toNat_lt byte)
      (Nat.pow_le_pow_right (by decide) above))
  have quotient : (8 * q + r) / 8 = q := by omega
  have remainder : (8 * q + r) % 8 = r := by omega
  simp only [quotient, remainder]
  rw [BitVec.getMsbD_eq_getLsbD]
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [Spec.inputWord, b0, b1, b2, b3, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ofNat]
     simp [high])

/--
A word of a block is its 32 bits from the offset, FIPS 180-4 §5.2.1.

Bit `i` from the left of the word is bit `8 start + i` of the block, for each `i` below 32.
-/
theorem inputWord_bits (block : ByteArray) (start : Nat) (whole : start + 4 ≤ block.size)
    (i : Nat) (inside : i < 32) :
    (Spec.inputWord block start).getMsbD i =
      (Spec.messageBits block)[8 * start + i]'(by
        rw [Spec.messageBits_length]
        omega) := by
  rw [Spec.messageBits_getElem, inputWord_getMsbD block start whole i inside]
  simp only [show (8 * start + i) / 8 = start + i / 8 by omega,
    show (8 * start + i) % 8 = i % 8 by omega]

/-- The model's padded message is the padded bits of FIPS 180-4 §5.1.1, below 2^61 bytes. -/
theorem padded_bits (message : ByteArray) (admitted : message.size < 2 ^ 61) :
    Spec.messageBits (Spec.padded message) = Spec.bitPad (Spec.messageBits message) := by
  rw [← pad_eq_spec message admitted, pad_bits]

/--
Word `t` of the block from byte `start` is its bits `32 t` to `32 t + 31`, FIPS 180-4 §5.2.1.

Bit `i` from the left of the word is bit `8 start + 32 t + i` of the bytes, for each `i` below 32.
-/
theorem inputWords_bits (block : ByteArray) (start : Nat) (whole : start + 64 ≤ block.size)
    (t : Fin 16) (i : Nat) (inside : i < 32) :
    (Spec.inputWords block start)[t].getMsbD i =
      (Spec.messageBits block)[8 * start + 32 * t.val + i]'(by
        rw [Spec.messageBits_length]
        omega) := by
  have word : (Spec.inputWords block start)[t] = Spec.inputWord block (start + 4 * t.val) := by
    simp [Spec.inputWords]
  rw [word, inputWord_bits block (start + 4 * t.val) (by omega) i inside]
  simp only [show 8 * (start + 4 * t.val) + i = 8 * start + 32 * t.val + i by omega]

end EthLib.Cryptography.Hash.Sha256
