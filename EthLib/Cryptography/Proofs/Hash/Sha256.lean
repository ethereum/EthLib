import EthLib.Cryptography.Hash.Sha256
import EthLib.Cryptography.Proofs.IdLoops

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
def interpret (H : Array UInt32) : Spec.State :=
  ⟨H[0]!.toBitVec, H[1]!.toBitVec, H[2]!.toBitVec, H[3]!.toBitVec,
    H[4]!.toBitVec, H[5]!.toBitVec, H[6]!.toBitVec, H[7]!.toBitVec⟩

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
    (smallPrimes 20).length = 8 ∧ IV.size = 8 ∧
      ((smallPrimes 20).zip (IV.toList.map UInt32.toNat)).all
        (fun pair => squareRootFraction pair.1 pair.2) = true := by
  decide +kernel

/--
The round constants are what FIPS 180-4 §4.2.2 derives: the cube roots of the first sixty-four primes.

So no round constant is taken on trust.
-/
theorem K_from_primes :
    (smallPrimes 312).length = 64 ∧ K.size = 64 ∧
      ((smallPrimes 312).zip (K.toList.map UInt32.toNat)).all
        (fun pair => cubeRootFraction pair.1 pair.2) = true := by
  decide +kernel

/-! ## The functions on words -/

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

/-! ## Loops as folds -/

/-- A loop over `[start:stop:step]` that always continues is a fold over the same numbers. -/
theorem forIn_range_step_yield {β : Type} (start stop step : Nat) (positive : 0 < step) (init : β)
    (f : Nat → β → β) :
    (forIn (m := Id) { start := start, stop := stop, step := step, step_pos := positive : Std.Legacy.Range } init
        (fun j acc => ForInStep.yield (f j acc))) =
      (List.range' start ((stop - start + step - 1) / step) step).foldl (fun acc j => f j acc) init := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', IdLoops.forIn_list_yield]
  rfl

/-- Writing one entry of an array changes that entry and no other. -/
theorem getElem!_set! {α : Type} [Inhabited α] (a : Array α) (i j : Nat) (v : α) (hi : i < a.size) :
    (a.set! j v)[i]! = if j = i then v else a[i]! := by
  have hi' : i < (a.set! j v).size := by simpa [Array.set!] using hi
  rw [getElem!_pos (a.set! j v) i hi', getElem!_pos a i hi]
  exact Array.getElem_setIfInBounds hi

/-! ## The compression function -/

/-- One step of the first schedule loop: word `j` read from the block. -/
def loadStep (buf : ByteArray) (off : Nat) (acc : Array UInt32) (j : Nat) : Array UInt32 :=
  acc.set! j (big32 buf (off + 4 * j))

/-- One step of the second schedule loop: word `j` from four earlier words. -/
def extendStep (acc : Array UInt32) (j : Nat) : Array UInt32 :=
  acc.set! j (acc[j - 16]! + smallSigma0 acc[j - 15]! + acc[j - 7]! + smallSigma1 acc[j - 2]!)

/-- The schedule array `compressBlock` builds. -/
def scheduleArray (buf : ByteArray) (off : Nat) : Array UInt32 :=
  (List.range' 16 48).foldl extendStep ((List.range' 0 16).foldl (loadStep buf off) (Array.replicate 64 0))

/-- The eight working variables, as `compressBlock` carries them. -/
abbrev Working := UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32

/-- One round of `compressBlock`. -/
def roundStep (W : Array UInt32) (s : Working) (t : Nat) : Working :=
  (s.2.2.2.2.2.2.2 + bigSigma1 s.2.2.2.2.1 + ch s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2.1 + K[t]! + W[t]! +
      (bigSigma0 s.1 + maj s.1 s.2.1 s.2.2.1),
    s.1, s.2.1, s.2.2.1,
    s.2.2.2.1 + (s.2.2.2.2.2.2.2 + bigSigma1 s.2.2.2.2.1 + ch s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2.1 + K[t]! + W[t]!),
    s.2.2.2.2.1, s.2.2.2.2.2.1, s.2.2.2.2.2.2.1)

/-- The working variables read as the model's state. -/
def Working.toState (s : Working) : Spec.State :=
  ⟨s.1.toBitVec, s.2.1.toBitVec, s.2.2.1.toBitVec, s.2.2.2.1.toBitVec,
    s.2.2.2.2.1.toBitVec, s.2.2.2.2.2.1.toBitVec, s.2.2.2.2.2.2.1.toBitVec, s.2.2.2.2.2.2.2.toBitVec⟩

/-- `compressBlock`, with its three loops written as folds. -/
theorem compressBlock_eq (H : Array UInt32) (buf : ByteArray) (off : Nat) :
    compressBlock H buf off =
      let s := (List.range' 0 64).foldl (roundStep (scheduleArray buf off))
        (H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!)
      #[H[0]! + s.1, H[1]! + s.2.1, H[2]! + s.2.2.1, H[3]! + s.2.2.2.1, H[4]! + s.2.2.2.2.1,
        H[5]! + s.2.2.2.2.2.1, H[6]! + s.2.2.2.2.2.2.1, H[7]! + s.2.2.2.2.2.2.2] := by
  simp only [compressBlock, Id.run, IdLoops.id_pure, IdLoops.id_bind]
  rw [forIn_range_step_yield, forIn_range_step_yield, forIn_range_step_yield]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  -- Name each loop body, so that no step evaluates a loop.
  rw [show (fun (acc : Array UInt32) (j : Nat) => acc.set! j (big32 buf (off + 4 * j))) = loadStep buf off from rfl,
    show (fun (acc : Array UInt32) (j : Nat) =>
      acc.set! j (acc[j - 16]! + smallSigma0 acc[j - 15]! + acc[j - 7]! + smallSigma1 acc[j - 2]!)) = extendStep
      from rfl,
    show (64 - 16 : Nat) = 48 from rfl,
    show List.foldl extendStep (List.foldl (loadStep buf off) (Array.replicate 64 0) (List.range' 0 16))
      (List.range' 16 48) = scheduleArray buf off from rfl,
    show (fun (s : Working) (t : Nat) => (s.2.2.2.2.2.2.2 + bigSigma1 s.2.2.2.2.1 +
        ch s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2.1 + K[t]! + (scheduleArray buf off)[t]! +
          (bigSigma0 s.1 + maj s.1 s.2.1 s.2.2.1),
        s.1, s.2.1, s.2.2.1,
        s.2.2.2.1 + (s.2.2.2.2.2.2.2 + bigSigma1 s.2.2.2.2.1 + ch s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2.1 +
          K[t]! + (scheduleArray buf off)[t]!),
        s.2.2.2.2.1, s.2.2.2.2.2.1, s.2.2.2.2.2.2.1)) = roundStep (scheduleArray buf off) from rfl]

/-- The first loop writes the block's words, whatever array of 64 words it starts from. -/
private theorem load_fold (buf : ByteArray) (off : Nat) (A : Array UInt32) (size : A.size = 64) :
    ∀ n ≤ 16, ((List.range' 0 n).foldl (loadStep buf off) A).size = 64 ∧
      ∀ i < n, ((List.range' 0 n).foldl (loadStep buf off) A)[i]! = big32 buf (off + 4 * i) := by
  intro n
  induction n with
  | zero => intro _; simp [size]
  | succ n ih =>
    intro bound
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add]
    generalize (List.range' 0 n).foldl (loadStep buf off) A = B at ih ⊢
    obtain ⟨sizeB, words⟩ := ih (by omega)
    refine ⟨by simpa [loadStep, Array.set!] using sizeB, fun i lt => ?_⟩
    -- The new entry is written now, and every earlier one was written before.
    rw [loadStep, getElem!_set! _ _ _ _ (by omega)]
    split
    · subst_vars; rfl
    · exact words i (by omega)

/-- The second loop extends a prefix of model words by the recurrence. -/
private theorem extend_fold (input : Vector Spec.Word 16) (A : Array UInt32) (size : A.size = 64)
    (early : ∀ i < 16, A[i]!.toBitVec = Spec.messageWord input i) :
    ∀ k ≤ 48, ((List.range' 16 k).foldl extendStep A).size = 64 ∧
      ∀ i < 16 + k, ((List.range' 16 k).foldl extendStep A)[i]!.toBitVec = Spec.messageWord input i := by
  intro k
  induction k with
  | zero => intro _; exact ⟨size, fun i lt => early i (by omega)⟩
  | succ k ih =>
    intro bound
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range' 16 k).foldl extendStep A = B at ih ⊢
    obtain ⟨sizeB, words⟩ := ih (by omega)
    refine ⟨by simpa [extendStep, Array.set!] using sizeB, fun i lt => ?_⟩
    rw [extendStep, getElem!_set! _ _ _ _ (by omega)]
    split
    · -- The new word reads four earlier words, all of them already the model's.
      subst_vars
      simp only [UInt32.toBitVec_add, smallSigma0_toBitVec, smallSigma1_toBitVec]
      rw [words _ (by omega), words _ (by omega), words _ (by omega), words _ (by omega)]
      conv_rhs => rw [Spec.messageWord]
      simp [show ¬ 16 + k < 16 by omega]
    · exact words i (by omega)

/-- Every schedule word is the one FIPS 180-4 §6.2.2, step 1 defines. -/
theorem scheduleArray_toBitVec (buf : ByteArray) (off : Nat) :
    ∀ t < 64, (scheduleArray buf off)[t]!.toBitVec = Spec.messageWord (Spec.inputWords buf off) t := by
  obtain ⟨size16, words16⟩ := load_fold buf off (Array.replicate 64 0) (by simp) 16 (Nat.le_refl _)
  have early : ∀ i < 16, ((List.range' 0 16).foldl (loadStep buf off) (Array.replicate 64 0))[i]!.toBitVec =
      Spec.messageWord (Spec.inputWords buf off) i := by
    intro i lt
    rw [words16 i lt, big32_toBitVec, Spec.messageWord]
    simp [lt, Spec.inputWords]
  intro t lt
  exact (extend_fold _ _ size16 early 48 (Nat.le_refl _)).2 t (by omega)

/-- One executable round is one round of the model. -/
theorem roundStep_toState (W : Array UInt32) (s : Working) (t : Nat) :
    (roundStep W s t).toState = Spec.step s.toState (K[t]!).toBitVec (W[t]!).toBitVec := by
  -- Machine addition and bit operations are the model's, word for word.
  simp [roundStep, Working.toState, Spec.step, ch, maj, bigSigma0_toBitVec, bigSigma1_toBitVec]

/-- The first `n` executable rounds are the model's first `n` rounds. -/
theorem rounds_fold (buf : ByteArray) (off : Nat) (s : Working) :
    ∀ n ≤ 64, ((List.range' 0 n).foldl (roundStep (scheduleArray buf off)) s).toState =
      Spec.rounds (Spec.inputWords buf off) s.toState n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro bound
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add,
      roundStep_toState, ih (by omega), scheduleArray_toBitVec buf off n (by omega)]
    rfl

/-- `compressBlock` is the compression function of FIPS 180-4 §6.2.2. -/
theorem compressBlock_toState (H : Array UInt32) (buf : ByteArray) (off : Nat) :
    interpret (compressBlock H buf off) = Spec.compression (Spec.inputWords buf off) (interpret H) := by
  rw [compressBlock_eq]
  have rounds := rounds_fold buf off (H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!) 64 (Nat.le_refl _)
  generalize (List.range' 0 64).foldl (roundStep (scheduleArray buf off))
    (H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!) = s at rounds ⊢
  -- The feed-forward adds the incoming words back, position by position.
  simp only [Working.toState] at rounds
  simp [interpret, Spec.compression, ← rounds]

/-! ## Padding -/

/-- Writing one byte changes that byte and no other. -/
theorem bytes_getElem!_set! (b : ByteArray) (i j : Nat) (v : UInt8) (hi : i < b.size) :
    (b.set! j v)[i]! = if j = i then v else b[i]! := by
  rcases b with ⟨data⟩
  have hi' : i < (ByteArray.set! ⟨data⟩ j v).size := by
    simpa [ByteArray.set!, Array.set!, ByteArray.size] using hi
  rw [getElem!_pos (ByteArray.set! ⟨data⟩ j v) i hi', getElem!_pos (⟨data⟩ : ByteArray) i hi]
  simp only [ByteArray.set!, ByteArray.getElem_eq_getElem_data]
  exact Array.getElem_setIfInBounds (by simpa [ByteArray.size] using hi)

/-- Writing a byte keeps the size. -/
@[simp] theorem bytes_size_set! (b : ByteArray) (j : Nat) (v : UInt8) : (b.set! j v).size = b.size := by
  rcases b with ⟨data⟩
  simp [ByteArray.set!, Array.set!, ByteArray.size]

/-- Writing `n` bytes from a base offset fills exactly those positions. -/
theorem fold_set_bytes (b : ByteArray) (base : Nat) (g : Nat → UInt8) :
    ∀ n, ((List.range' 0 n).foldl (fun acc j => acc.set! (base + j) (g j)) b).size = b.size ∧
      ∀ p < b.size, ((List.range' 0 n).foldl (fun acc j => acc.set! (base + j) (g j)) b)[p]! =
        if base ≤ p ∧ p < base + n then g (p - base) else b[p]! := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add]
    generalize (List.range' 0 n).foldl (fun acc j => acc.set! (base + j) (g j)) b = c at ih ⊢
    obtain ⟨size, bytes⟩ := ih
    refine ⟨by simp [size], fun p lt => ?_⟩
    rw [bytes_getElem!_set! _ _ _ _ (by omega), bytes p lt]
    -- The newest write wins at its own position, and the earlier ones everywhere else in the run.
    by_cases at_n : base + n = p
    · subst at_n; simp
    · simp only [at_n, ite_false]
      by_cases inside : base ≤ p ∧ p < base + n
      · simp [inside, show base ≤ p ∧ p < base + (n + 1) by omega]
      · simp [inside, show ¬ (base ≤ p ∧ p < base + (n + 1)) by omega]

/-- Two byte arrays of the same size agree when they agree at every position. -/
theorem bytes_ext {a b : ByteArray} (size : a.size = b.size) (same : ∀ p < a.size, a[p]! = b[p]!) : a = b := by
  apply ByteArray.ext
  apply Array.ext (by simpa using size)
  intro p ha hb
  have := same p (by simpa using ha)
  rwa [getElem!_pos a p (by simpa using ha), getElem!_pos b p (by simpa using hb),
    ByteArray.getElem_eq_getElem_data, ByteArray.getElem_eq_getElem_data] at this

/-- The size of the model's padding. -/
theorem spec_padded_size (msg : ByteArray) :
    (Spec.padded msg).size = msg.size + 1 + Spec.zeroCount msg.size + 8 := by
  rw [← ByteArray.size_data]
  simp [Spec.padded]
  omega

/-- A byte of the model's padding: message, `0x80`, zeros, then the bit length. -/
theorem spec_padded_get (msg : ByteArray) (p : Nat) (lt : p < msg.size + 1 + Spec.zeroCount msg.size + 8) :
    (Spec.padded msg)[p]! =
      if p < msg.size then msg[p]! else if p = msg.size then 0x80
      else if p < msg.size + 1 + Spec.zeroCount msg.size then 0
      else UInt8.ofNat ((msg.size * 8 / 2 ^ (56 - 8 * (p - (msg.size + 1 + Spec.zeroCount msg.size)))) % 256) := by
  rw [getElem!_pos _ p (by rw [spec_padded_size]; exact lt), ByteArray.getElem_eq_getElem_data]
  simp only [Spec.padded]
  -- Each region of the concatenation is read where it sits.
  split_ifs with h1 h2 h3
  · rw [Array.getElem_append_left (by simp; omega), Array.getElem_append_left (by simp; omega),
      Array.getElem_append_left (by simp; omega), getElem!_pos msg p h1, ByteArray.getElem_eq_getElem_data]
  · subst h2
    rw [Array.getElem_append_left (by simp; omega), Array.getElem_append_left (by simp),
      Array.getElem_append_right (by simp)]
    simp
  · rw [Array.getElem_append_left (by simp; omega), Array.getElem_append_right (by simp; omega)]
    simp
  · rw [Array.getElem_append_right (by simp; omega)]
    simp

/-- One byte of the bit length: the 64-bit shift is the model's division, below 2^61 bytes. -/
theorem length_byte (len j : Nat) (admitted : len < 2 ^ 61) (hj : j < 8) :
    UInt8.ofNat ((UInt64.ofNat (len * 8) >>> UInt64.ofNat ((7 - j) * 8)).toNat) =
      UInt8.ofNat ((len * 8 / 2 ^ (56 - 8 * j)) % 256) := by
  apply UInt8.toNat_inj.mp
  -- Eight byte positions, each a fixed shift below the word width.
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
  all_goals first
    | omega
    | (simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; done)
    | (simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; omega)

/-- `padded` is the padding of FIPS 180-4 §5.1.1, for every message shorter than 2^61 bytes. -/
theorem padded_eq (msg : ByteArray) (admitted : msg.size < 2 ^ 61) : padded msg = Spec.padded msg := by
  simp only [padded, Id.run, IdLoops.id_pure, IdLoops.id_bind, IdLoops.forIn_range_yield]
  rw [show (fun (acc : ByteArray) (j : Nat) => acc.set! j msg[j]!) = (fun acc j => acc.set! (0 + j) msg[j]!) from by
    funext acc j; rw [Nat.zero_add]]
  generalize hz : (56 + 64 - (msg.size + 1) % 64) % 64 = z
  have zeros : z = Spec.zeroCount msg.size := by subst hz; unfold Spec.zeroCount; omega
  -- The three writes: the message, the `0x80` byte, then the eight length bytes.
  have size0 : (⟨Array.replicate (msg.size + 1 + z + 8) 0⟩ : ByteArray).size = msg.size + 1 + z + 8 := by
    rw [← ByteArray.size_data]; simp
  obtain ⟨size1, bytes1⟩ :=
    fold_set_bytes ⟨Array.replicate (msg.size + 1 + z + 8) 0⟩ 0 (fun j => msg[j]!) msg.size
  generalize (List.range' 0 msg.size).foldl (fun (acc : ByteArray) (j : Nat) => acc.set! (0 + j) msg[j]!)
    (⟨Array.replicate (msg.size + 1 + z + 8) 0⟩ : ByteArray) = B at size1 bytes1 ⊢
  obtain ⟨size3, bytes3⟩ := fold_set_bytes (B.set! msg.size 128) (msg.size + 1 + z + 8 - 8)
    (fun j => UInt8.ofNat ((UInt64.ofNat (msg.size * 8) >>> UInt64.ofNat ((7 - j) * 8)).toNat)) 8
  generalize (List.range' 0 8).foldl (fun (acc : ByteArray) (j : Nat) => acc.set! (msg.size + 1 + z + 8 - 8 + j)
    (UInt8.ofNat ((UInt64.ofNat (msg.size * 8) >>> UInt64.ofNat ((7 - j) * 8)).toNat)))
    (B.set! msg.size 128) = C at size3 bytes3 ⊢
  rw [size0] at size1
  apply bytes_ext
  · rw [size3, bytes_size_set!, size1, spec_padded_size, zeros]
  · intro p lt
    rw [size3, bytes_size_set!, size1] at lt
    rw [bytes3 p (by simpa [size1] using lt), spec_padded_get msg p (by rw [← zeros]; exact lt), ← zeros]
    -- Each position is a message byte, the `0x80` byte, a zero, or a length byte.
    split_ifs with h1 h2 h3 h4 h5 h6 <;> try omega
    · -- A length byte.
      rw [show msg.size + 1 + z + 8 - 8 = msg.size + 1 + z by omega]
      exact length_byte _ _ admitted (by omega)
    · -- A message byte.
      rw [bytes_getElem!_set! _ _ _ _ (by omega), ite_eq_right (by omega), bytes1 p (by rw [size0]; omega)]
      simp only [Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero]
      split_ifs
      rfl
    · -- The `0x80` byte.
      subst_vars
      rw [bytes_getElem!_set! _ _ _ _ (by omega)]
      simp
    · -- A zero byte.
      rw [bytes_getElem!_set! _ _ _ _ (by omega), ite_eq_right (by omega), bytes1 p (by rw [size0]; omega)]
      simp only [Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero]
      split_ifs
      rw [getElem!_pos _ p (by rw [size0]; exact lt), ByteArray.getElem_eq_getElem_data]
      simp

/-! ## The whole hash -/

/-- Compressing the first `n` blocks is the model's block chain. -/
theorem blocks_fold (buf : ByteArray) (H : Array UInt32) :
    ∀ n, interpret ((List.range' 0 n 64).foldl (fun acc off => compressBlock acc buf off) H) =
      Spec.blocks buf (interpret H) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, compressBlock_toState, ih,
      Nat.zero_add]
    rfl

/-- One step of the output loop: word `j` written as four big-endian bytes. -/
def outStep (H : Array UInt32) (acc : ByteArray) (j : Nat) : ByteArray :=
  (((acc.set! (4 * j) (UInt8.ofNat (H[j]! >>> 24).toNat)).set! (4 * j + 1)
    (UInt8.ofNat ((H[j]! >>> 16).toNat &&& 255))).set! (4 * j + 2)
    (UInt8.ofNat ((H[j]! >>> 8).toNat &&& 255))).set! (4 * j + 3) (UInt8.ofNat (H[j]!.toNat &&& 255))

/-- Each output byte is one base-256 digit of its word, most significant first. -/
theorem out_bytes (h : UInt32) :
    UInt8.ofNat (h >>> 24).toNat = UInt8.ofNat (h.toNat / 2 ^ 24 % 256) ∧
      UInt8.ofNat ((h >>> 16).toNat &&& 255) = UInt8.ofNat (h.toNat / 2 ^ 16 % 256) ∧
      UInt8.ofNat ((h >>> 8).toNat &&& 255) = UInt8.ofNat (h.toNat / 2 ^ 8 % 256) ∧
      UInt8.ofNat (h.toNat &&& 255) = UInt8.ofNat (h.toNat / 2 ^ 0 % 256) := by
  have mask (x : Nat) : x &&& 255 = x % 256 := Nat.and_two_pow_sub_one_eq_mod x 8
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
    simp [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, mask]

/-- The output loop writes every word of the state as its four big-endian bytes. -/
theorem out_fold (H : Array UInt32) :
    ∀ n ≤ 8, ((List.range' 0 n).foldl (outStep H) ⟨Array.replicate 32 0⟩).size = 32 ∧
      ∀ p < 4 * n, ((List.range' 0 n).foldl (outStep H) ⟨Array.replicate 32 0⟩)[p]! =
        UInt8.ofNat (H[p / 4]!.toNat / 2 ^ (24 - 8 * (p % 4)) % 256) := by
  intro n
  induction n with
  | zero => intro _; refine ⟨by rw [← ByteArray.size_data]; simp, fun p lt => by omega⟩
  | succ n ih =>
    intro bound
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add]
    generalize (List.range' 0 n).foldl (outStep H) ⟨Array.replicate 32 0⟩ = O at ih ⊢
    obtain ⟨size, bytes⟩ := ih (by omega)
    refine ⟨by simp [outStep, size], fun p lt => ?_⟩
    obtain ⟨b0, b1, b2, b3⟩ := out_bytes H[n]!
    simp only [outStep]
    rw [bytes_getElem!_set! _ _ _ _ (by simp [size]; omega), bytes_getElem!_set! _ _ _ _ (by simp [size]; omega),
      bytes_getElem!_set! _ _ _ _ (by simp [size]; omega), bytes_getElem!_set! _ _ _ _ (by omega)]
    -- The four new bytes belong to word `n`, and every earlier byte was already written.
    split_ifs with h3 h2 h1 h0
    · rw [b3, show p / 4 = n by omega, show p % 4 = 3 by omega]
    · rw [b2, show p / 4 = n by omega, show p % 4 = 2 by omega]
    · rw [b1, show p / 4 = n by omega, show p % 4 = 1 by omega]
    · rw [b0, show p / 4 = n by omega, show p % 4 = 0 by omega]
    · exact bytes p (by omega)

/-- The state words, read in digest order. -/
theorem interpret_words (H : Array UInt32) (i : Nat) (lt : i < 8) :
    (interpret H).words[i] = H[i]!.toBitVec := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
  all_goals first | omega | simp [interpret, Spec.State.words]

/-- A byte of `padded`: message, `0x80`, zeros, then the bit length in eight big-endian bytes. -/
theorem padded_get (msg : ByteArray) (admitted : msg.size < 2 ^ 61) (p : Nat)
    (lt : p < msg.size + 1 + Spec.zeroCount msg.size + 8) :
    (padded msg)[p]! =
      if p < msg.size then msg[p]! else if p = msg.size then 0x80
      else if p < msg.size + 1 + Spec.zeroCount msg.size then 0
      else UInt8.ofNat ((msg.size * 8 / 2 ^ (56 - 8 * (p - (msg.size + 1 + Spec.zeroCount msg.size)))) % 256) := by
  rw [padded_eq msg admitted]
  exact spec_padded_get msg p lt

/-- The size of a padded message is a whole number of blocks. -/
theorem padded_size_mod (msg : ByteArray) (admitted : msg.size < 2 ^ 61) : (padded msg).size % 64 = 0 := by
  rw [padded_eq msg admitted, spec_padded_size]
  unfold Spec.zeroCount
  omega

/--
SHA-256 is the hash of FIPS 180-4 §6.2, on every message shorter than 2^61 bytes.

FIPS 180-4 §5.1.1 bounds a message at 2^64 bits, which is 2^61 bytes.
-/
theorem hash_eq_spec (msg : ByteArray) (admitted : msg.size < 2 ^ 61) : Sha256.hash msg = Spec.hash msg := by
  simp only [Sha256.hash, Id.run, IdLoops.id_pure, IdLoops.id_bind, IdLoops.forIn_range_yield]
  rw [forIn_range_step_yield, show ((padded msg).size - 0 + 64 - 1) / 64 = (padded msg).size / 64 by
    have := padded_size_mod msg admitted; omega]
  have chain := blocks_fold (padded msg) IV ((padded msg).size / 64)
  generalize (List.range' 0 ((padded msg).size / 64) 64).foldl
    (fun acc off => compressBlock acc (padded msg) off) IV = H at chain ⊢
  rw [show (fun (acc : ByteArray) (j : Nat) =>
      (((acc.set! (4 * j) (UInt8.ofNat (H[j]! >>> 24).toNat)).set! (4 * j + 1)
        (UInt8.ofNat ((H[j]! >>> 16).toNat &&& 255))).set! (4 * j + 2)
        (UInt8.ofNat ((H[j]! >>> 8).toNat &&& 255))).set! (4 * j + 3) (UInt8.ofNat (H[j]!.toNat &&& 255)))
      = outStep H from rfl]
  obtain ⟨size, bytes⟩ := out_fold H 8 (Nat.le_refl _)
  -- The model hashes the same padded message from the same initial words.
  have start : interpret IV = Spec.initial := by decide
  simp only [Spec.hash, ← padded_eq msg admitted, ← start, ← chain]
  have digestSize : (Spec.digest (interpret H)).size = 32 := by rw [← ByteArray.size_data]; simp [Spec.digest]
  apply bytes_ext (by rw [size, digestSize])
  intro p lt
  rw [size] at lt
  rw [bytes p (by omega), getElem!_pos _ p (by rw [digestSize]; exact lt), ByteArray.getElem_eq_getElem_data]
  simp only [Spec.digest, Array.getElem_ofFn]
  rw [interpret_words H (p / 4) (by omega), UInt32.toNat_toBitVec]

end EthLib.Cryptography.Hash.Sha256
