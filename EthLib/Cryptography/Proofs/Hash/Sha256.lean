import EthLib.Cryptography.Hash.Sha256

/-!
# Proofs: `Hash.Sha256`

SHA-256 agrees with FIPS 180-4 on every message shorter than 2^61 bytes.

The standard is restated below as a model over 32-bit bit vectors, independent of the executable code.
-/

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

/-- One block: sixty-four rounds, then the intermediate hash value added in, FIPS 180-4 §6.2.2, step 4. -/
def compression (input : Vector Word 16) (initial : State) : State :=
  let w := rounds input initial 64
  ⟨initial.a + w.a, initial.b + w.b, initial.c + w.c, initial.d + w.d,
    initial.e + w.e, initial.f + w.f, initial.g + w.g, initial.h + w.h⟩

/-- The initial hash value, FIPS 180-4 §5.3.3. -/
def initial : State :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

/-- The number of zero bytes after the `0x80` byte, FIPS 180-4 §5.1.1. -/
def zeroCount (size : Nat) : Nat := (119 - size % 64) % 64

/-- The padded message, FIPS 180-4 §5.1.1: the message, `0x80`, zeros, and the bit length in eight big-endian bytes. -/
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

/-- Eight machine words read as the model's working variables. -/
def interpret (H : Vector UInt32 8) : Spec.State :=
  ⟨H[0].toBitVec, H[1].toBitVec, H[2].toBitVec, H[3].toBitVec,
    H[4].toBitVec, H[5].toBitVec, H[6].toBitVec, H[7].toBitVec⟩

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
The initial hash value is what FIPS 180-4 §5.3.3 derives: the square roots of the first eight primes.

So no initial word is taken on trust.
-/
theorem IV_from_primes :
    (smallPrimes 20).length = 8 ∧ IV.toList.length = 8 ∧
      ((smallPrimes 20).zip (IV.toList.map UInt32.toNat)).all
        (fun pair => squareRootFraction pair.1 pair.2) = true := by
  decide +kernel

/--
The round constants are what FIPS 180-4 §4.2.2 derives: the cube roots of the first sixty-four primes.

So no round constant is taken on trust.
-/
theorem K_from_primes :
    (smallPrimes 312).length = 64 ∧ K.toList.length = 64 ∧
      ((smallPrimes 312).zip (K.toList.map UInt32.toNat)).all
        (fun pair => cubeRootFraction pair.1 pair.2) = true := by
  decide +kernel

/-! ## The functions on words -/

/-- `smallSigma0` is σ0 of FIPS 180-4 §4.1.2. -/
theorem smallSigma0_toBitVec (x : UInt32) : (smallSigma0 x).toBitVec = Spec.small0 x.toBitVec := by
  -- Each pair of shifts joined by an or is a rotation.
  simp [smallSigma0, rotr, shr, Spec.small0, BitVec.rotateRight_def]

/-- `smallSigma1` is σ1 of FIPS 180-4 §4.1.2. -/
theorem smallSigma1_toBitVec (x : UInt32) : (smallSigma1 x).toBitVec = Spec.small1 x.toBitVec := by
  simp [smallSigma1, rotr, shr, Spec.small1, BitVec.rotateRight_def]

/-- `bigSigma0` is Σ0 of FIPS 180-4 §4.1.2. -/
theorem bigSigma0_toBitVec (x : UInt32) : (bigSigma0 x).toBitVec = Spec.large0 x.toBitVec := by
  simp [bigSigma0, rotr, Spec.large0, BitVec.rotateRight_def]

/-- `bigSigma1` is Σ1 of FIPS 180-4 §4.1.2. -/
theorem bigSigma1_toBitVec (x : UInt32) : (bigSigma1 x).toBitVec = Spec.large1 x.toBitVec := by
  simp [bigSigma1, rotr, Spec.large1, BitVec.rotateRight_def]

/-- `big32` reads four bytes as one big-endian word, FIPS 180-4 §3.1. -/
theorem big32_toBitVec (b : ByteArray) (off : Nat) : (big32 b off).toBitVec = Spec.inputWord b off := by
  -- Widening a byte keeps its value.
  have byte (v : UInt8) : v.toBitVec.setWidth 32 = BitVec.ofNat 32 v.toNat :=
    BitVec.eq_of_toNat_eq (by simp)
  simp [big32, Spec.inputWord, byte]

/-! ## The message schedule -/

/-- Extending the schedule keeps every word already computed. -/
theorem schedulePrefix_get (block : ByteArray) (start count upper i : Nat) (within : i < count)
    (bound : count ≤ upper) :
    (schedulePrefix block start upper)[i]'(by omega) = (schedulePrefix block start count)[i] := by
  -- Each step only appends, so no earlier position ever changes.
  induction upper generalizing count with
  | zero => omega
  | succ upper ih =>
    by_cases same : count = upper + 1
    · subst count; rfl
    · rw [schedulePrefix, Vector.getElem_push_lt (by omega)]
      exact ih count within (by omega)

/-- The first sixteen schedule words are the block's big-endian words. -/
theorem schedule_input (block : ByteArray) (start i : Nat) (input : i < 16) :
    (schedule block start)[i]'(by omega) = big32 block (start + 4 * i) := by
  rw [schedule, schedulePrefix_get block start (i + 1) 64 i (by omega) (by omega)]
  simp [schedulePrefix, input]

/-- Every later word mixes four earlier ones, FIPS 180-4 §6.2.2, step 1. -/
theorem schedule_recurrence (block : ByteArray) (start i : Nat) (later : 16 ≤ i) (within : i < 64) :
    (schedule block start)[i] =
      (schedule block start)[i - 16]'(by omega) + smallSigma0 ((schedule block start)[i - 15]'(by omega)) +
        (schedule block start)[i - 7]'(by omega) + smallSigma1 ((schedule block start)[i - 2]'(by omega)) := by
  -- The recurrence reads only older words, which the full schedule keeps.
  unfold schedule
  rw [schedulePrefix_get block start (i + 1) 64 i (by omega) (by omega),
    schedulePrefix_get block start i 64 (i - 16) (by omega) (by omega),
    schedulePrefix_get block start i 64 (i - 15) (by omega) (by omega),
    schedulePrefix_get block start i 64 (i - 7) (by omega) (by omega),
    schedulePrefix_get block start i 64 (i - 2) (by omega) (by omega)]
  simp [schedulePrefix, show ¬ i < 16 by omega]

/-- The schedule reads only the sixty-four bytes of its block. -/
theorem schedule_congr (b₁ b₂ : ByteArray) (s₁ s₂ : Nat) (same : ∀ i < 64, b₁[s₁ + i]! = b₂[s₂ + i]!) :
    schedule b₁ s₁ = schedule b₂ s₂ := by
  -- Every prefix agrees, by induction on its length.
  suffices ∀ n ≤ 64, schedulePrefix b₁ s₁ n = schedulePrefix b₂ s₂ n from this 64 (Nat.le_refl _)
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro within
    simp only [schedulePrefix, ih (by omega)]
    -- An input word reads four bytes of the block.
    by_cases first : n < 16
    · simp only [first, ↓reduceDIte, big32, Nat.add_assoc]
      rw [same (4 * n) (by omega), same (4 * n + 1) (by omega), same (4 * n + 2) (by omega),
        same (4 * n + 3) (by omega)]
    · simp only [first, ↓reduceDIte]

/-- Every schedule word is the one FIPS 180-4 §6.2.2, step 1 defines. -/
theorem schedule_toBitVec (block : ByteArray) (start : Nat) :
    ∀ t, (within : t < 64) →
      ((schedule block start)[t]).toBitVec = Spec.messageWord (Spec.inputWords block start) t := by
  -- Strong induction covers the four backward references of the recurrence.
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro within
    by_cases early : t < 16
    · rw [schedule_input block start t early, big32_toBitVec, Spec.messageWord]
      simp [early, Spec.inputWords]
    · rw [schedule_recurrence block start t (by omega) within]
      simp only [UInt32.toBitVec_add, smallSigma0_toBitVec, smallSigma1_toBitVec]
      rw [ih (t - 16) (by omega) (by omega), ih (t - 15) (by omega) (by omega),
        ih (t - 7) (by omega) (by omega), ih (t - 2) (by omega) (by omega)]
      conv => rhs; rw [Spec.messageWord]
      simp [early]

/-! ## One block -/

/-- One round is one round of the model. -/
theorem round_toState (state : Vector UInt32 8) (constant word : UInt32) :
    interpret (round state constant word) =
      Spec.step (interpret state) constant.toBitVec word.toBitVec := by
  -- Machine addition and bit operations are the model's, word for word.
  simp [interpret, round, Spec.step, ch, maj, bigSigma0_toBitVec, bigSigma1_toBitVec]

/-- The first rounds of a block are the model's first rounds. -/
private theorem rounds_toState (block : ByteArray) (start : Nat) (state : Vector UInt32 8) :
    ∀ n, (bounded : n ≤ 64) →
      interpret (((List.finRange 64).take n).foldl
        (fun current t => round current K[t] (schedule block start)[t]) state) =
      Spec.rounds (Spec.inputWords block start) (interpret state) n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro bounded
    -- One more index is one more round.
    rw [List.take_succ_eq_append_getElem (by simp; omega), List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, List.getElem_finRange, Fin.cast_mk]
    rw [round_toState, ih (by omega)]
    simp only [Fin.getElem_fin]
    rw [schedule_toBitVec block start n (by omega)]
    simp only [Spec.rounds, getElem!_pos K n (by omega)]

/-- `compress` is the compression of FIPS 180-4 §6.2.2, steps 2 to 4. -/
theorem compress_toState (state : Vector UInt32 8) (block : ByteArray) (start : Nat) :
    interpret (compress state block start) =
      Spec.compression (Spec.inputWords block start) (interpret state) := by
  have rounds := rounds_toState block start state 64 (by omega)
  rw [List.take_of_length_le (by simp)] at rounds
  simp only [compress, Spec.compression, ← rounds]
  simp [interpret]

/-- Compression reads only the sixty-four bytes of its block. -/
theorem compress_congr (state : Vector UInt32 8) (b₁ b₂ : ByteArray) (s₁ s₂ : Nat)
    (same : ∀ i < 64, b₁[s₁ + i]! = b₂[s₂ + i]!) : compress state b₁ s₁ = compress state b₂ s₂ := by
  simp only [compress, schedule_congr b₁ b₂ s₁ s₂ same]

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

private theorem bits_toNat (size : Nat) (admitted : size < 2 ^ 61) : (UInt64.ofNat size * 8).toNat = size * 8 := by
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

/-- Below 2⁶¹ bytes, the length bytes are the bit length's base-256 digits, most significant first. -/
theorem lengthBytes_digit (size : Nat) (admitted : size < 2 ^ 61) (i : Fin 8) :
    ((lengthBytes size)[i.val]'(by simp)).toNat = (size * 8 / 2 ^ (56 - 8 * i.val)) % 256 := by
  simp only [lengthBytes, ByteArray.getElem_eq_getElem_data, Array.getElem_ofFn, UInt64.toNat_toUInt8,
    UInt64.toNat_shiftRight, bits_toNat size admitted, shift_toNat]
  change ((size * 8) >>> ((56 - 8 * i.val) % 64)) % 256 = _
  rw [Nat.mod_eq_of_lt (show 56 - 8 * i.val < 64 by omega), Nat.shiftRight_eq_div_pow]

/-- `pad` is the padding of FIPS 180-4 §5.1.1, below 2⁶¹ bytes. -/
theorem pad_eq_spec (message : ByteArray) (admitted : message.size < 2 ^ 61) :
    pad message = Spec.padded message := by
  have zeros : paddingZeros message.size = Spec.zeroCount message.size := by
    unfold paddingZeros Spec.zeroCount
    omega
  have length : (lengthBytes message.size).data =
      Array.ofFn (fun i : Fin 8 => UInt8.ofNat ((message.size * 8 / 2 ^ (56 - 8 * i.val)) % 256)) := by
    apply Array.ext
    · exact (lengthBytes_size message.size).trans Array.size_ofFn.symm
    · intro p left right
      apply UInt8.toNat_inj.mp
      simpa [ByteArray.getElem_eq_getElem_data] using
        lengthBytes_digit message.size admitted ⟨p, by simpa using left⟩
  -- The message, the `0x80` byte, the zeros and the length agree region by region.
  apply ByteArray.ext
  simp only [pad, Spec.padded, ByteArray.data_append, ByteArray.data_push, zeros, length, Array.push_eq_append]

/-! ## The hash -/

/-- Every digest is 32 bytes long, whatever the message. -/
@[simp] theorem hash_size (message : ByteArray) : (hash message).size = 32 := by
  simp only [hash, digest, ByteArray.size, Array.size_ofFn]

/-- Compressing the first `n` blocks is the model's chain of blocks. -/
theorem blocks_toState (message : ByteArray) (state : Vector UInt32 8) (n : Nat) :
    interpret ((List.range n).foldl (fun current i => compress current message (64 * i)) state) =
      Spec.blocks message (interpret state) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, compress_toState, ih, Spec.blocks]

/-- The state words, read in digest order. -/
private theorem interpret_words (state : Vector UInt32 8) (i : Nat) (within : i < 8) :
    (interpret state).words[i] = state[i].toBitVec := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
  all_goals first | omega | simp [interpret, Spec.State.words]

/-- One output byte is one base-256 digit of its word. -/
private theorem digit (word : UInt32) (k : Nat) (within : k < 4) :
    (word >>> (24 - 8 * UInt32.ofNat k)).toUInt8 = UInt8.ofNat ((word.toNat / 2 ^ (24 - 8 * k)) % 256) := by
  rcases k with _ | _ | _ | _ | k
  all_goals first | omega | (apply UInt8.toNat_inj.mp; simp [Nat.shiftRight_eq_div_pow])

/-- `digest` writes the model's digest. -/
theorem digest_eq_spec (state : Vector UInt32 8) : digest state = Spec.digest (interpret state) := by
  apply ByteArray.ext
  apply Array.ext
  · simp [digest, Spec.digest]
  · intro p left right
    have within : p < 32 := by simpa [digest] using left
    simp only [digest, Spec.digest, Array.getElem_ofFn]
    rw [digit _ _ (Nat.mod_lt _ (by decide)), interpret_words state (p / 4) (by omega), UInt32.toNat_toBitVec]

/--
SHA-256 is the hash of FIPS 180-4 §6.2, on every message shorter than 2⁶¹ bytes.

FIPS 180-4 §5.1.1 bounds a message at 2⁶⁴ bits, which is 2⁶¹ bytes.
-/
theorem hash_eq_spec (message : ByteArray) (admitted : message.size < 2 ^ 61) :
    hash message = Spec.hash message := by
  have start : interpret IV = Spec.initial := by decide
  simp only [hash, Spec.hash, digest_eq_spec, blocks_toState, start, pad_eq_spec message admitted]

end EthLib.Cryptography.Hash.Sha256
