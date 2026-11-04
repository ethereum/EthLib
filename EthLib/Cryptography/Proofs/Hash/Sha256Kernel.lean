module

public import EthLib.Cryptography.Proofs.Hash.Sha256

/-!
# Proofs: a fast form of SHA-256 for the kernel

The kernel reads a vector or a byte array by walking a list, so the specification is slow there.

This form keeps each word in a record field, and the padded message in a list.

The message schedule is a window of sixteen words that slides one word per round.

A known answer rewrites its hash to this form, which equals the specification for every message.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Sha256

namespace Kernel

/-! ## Records -/

/-- The eight words of a hash value, or the working variables a to h. -/
structure Words where
  (a b c d e f g h : UInt32)

/-- The record of a vector of eight words. -/
def Words.ofVector (H : Vector UInt32 8) : Words :=
  ⟨H[0], H[1], H[2], H[3], H[4], H[5], H[6], H[7]⟩

/-- The vector of a record's eight words. -/
def Words.toVector (s : Words) : Vector UInt32 8 :=
  #v[s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h]

/-- A vector of eight words is the vector of its record. -/
theorem toVector_ofVector (H : Vector UInt32 8) : (Words.ofVector H).toVector = H := by
  apply Vector.ext
  intro i hi
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | _ + 8, hi => omega

/-- Sixteen consecutive words `W_t` to `W_(t+15)` of the message schedule. -/
structure Window where
  (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt32)

/-- The window of sixteen values of a sequence of words. -/
def Window.ofFn (f : Nat → UInt32) : Window :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15⟩

/--
The window one word later, FIPS 180-4 §6.2.2, step 1.

The new last word is `W_(t+16) = W_t + σ0(W_(t+1)) + W_(t+9) + σ1(W_(t+14))`.
-/
def Window.next (w : Window) : Window :=
  ⟨w.w1, w.w2, w.w3, w.w4, w.w5, w.w6, w.w7, w.w8, w.w9, w.w10, w.w11, w.w12, w.w13, w.w14, w.w15,
    w.w0 + smallSigma0 w.w1 + w.w9 + smallSigma1 w.w14⟩

/-! ## One block -/

/-- Four bytes as one big-endian word, FIPS 180-4 §3.1. -/
def word (bytes : List UInt8) (start : Nat) : UInt32 :=
  bytes[start]!.toUInt32 <<< 24 ||| bytes[start + 1]!.toUInt32 <<< 16 |||
    bytes[start + 2]!.toUInt32 <<< 8 ||| bytes[start + 3]!.toUInt32

/-- The first sixteen words of the schedule: the block's own words, FIPS 180-4 §6.2.2, step 1. -/
def Window.ofBytes (bytes : List UInt8) : Window :=
  Window.ofFn fun i => word bytes (4 * i)

/-- One round on the working variables, FIPS 180-4 §6.2.2, step 3. -/
def round (constant word : UInt32) (s : Words) : Words :=
  let t1 := s.h + bigSigma1 s.e + ch s.e s.f s.g + constant + word
  let t2 := bigSigma0 s.a + maj s.a s.b s.c
  ⟨t1 + t2, s.a, s.b, s.c, s.d + t1, s.e, s.f, s.g⟩

/-- One round per constant, each with the first word of the window, which then slides. -/
def rounds : List UInt32 → Window → Words → Words
  | [], _, s => s
  | constant :: rest, w, s => rounds rest w.next (round constant w.w0 s)

/-- The hash value after one more block, FIPS 180-4 §6.2.2, steps 2 to 4. -/
def compress (s : Words) (block : List UInt8) : Words :=
  let r := rounds K.toList (Window.ofBytes block) s
  ⟨s.a + r.a, s.b + r.b, s.c + r.c, s.d + r.d, s.e + r.e, s.f + r.f, s.g + r.g, s.h + r.h⟩

/--
The hash value after the first blocks of a padded message, each absorbed by one step.

The step is an argument: with the compression inside, the kernel overflows on the equations.
-/
def chain (step : Words → List UInt8 → Words) : (count : Nat) → List UInt8 → Words → Words
  | 0, _, s => s
  | count + 1, bytes, s => chain step count (bytes.drop 64) (step s bytes)

/-! ## The hash -/

/-- The padded message, FIPS 180-4 §5.1.1, as a list of bytes. -/
def pad (message : List UInt8) : List UInt8 :=
  message ++ 0x80 :: List.replicate (paddingZeros message.length) 0 ++
    (lengthBytes message.length).data.toList

/-- SHA-256 over the record forms, FIPS 180-4 §6.2. -/
def hash (message : ByteArray) : ByteArray :=
  let padded := pad message.data.toList
  digest (chain compress (padded.length / 64) padded (Words.ofVector IV)).toVector

/-! ## The record form is the specification -/

/-- A byte of a byte array, read from the list of its bytes after an offset. -/
private theorem getElem!_drop (block : ByteArray) (start i : Nat) :
    (block.data.toList.drop start)[i]! = block[start + i]! := by
  simp only [getElem!_def, Array.getElem?_toList, List.getElem?_drop]
  rfl

/-- A word read from the list of a block's bytes is the word the specification reads. -/
private theorem word_drop (block : ByteArray) (start i : Nat) :
    word (block.data.toList.drop start) i = big32 block (start + i) := by
  simp only [word, big32, getElem!_drop, Nat.add_assoc]

/-- Every later word of a schedule prefix mixes four earlier ones, FIPS 180-4 §6.2.2, step 1. -/
private theorem schedulePrefix_recurrence (block : ByteArray) (start upper i : Nat) (later : 16 ≤ i)
    (within : i < upper) :
    (schedulePrefix block start upper)[i] =
      (schedulePrefix block start upper)[i - 16]'(by omega) +
        smallSigma0 ((schedulePrefix block start upper)[i - 15]'(by omega)) +
        (schedulePrefix block start upper)[i - 7]'(by omega) +
        smallSigma1 ((schedulePrefix block start upper)[i - 2]'(by omega)) := by
  -- The recurrence reads only older words, which the longer prefix keeps.
  rw [schedulePrefix_get block start (i + 1) upper i (by omega) (by omega),
    schedulePrefix_get block start i upper (i - 16) (by omega) (by omega),
    schedulePrefix_get block start i upper (i - 15) (by omega) (by omega),
    schedulePrefix_get block start i upper (i - 7) (by omega) (by omega),
    schedulePrefix_get block start i upper (i - 2) (by omega) (by omega)]
  simp [schedulePrefix, show ¬ i < 16 by omega]

/-- The schedule extended to 80 words, so that the window stays defined in the last rounds. -/
private def extended (block : ByteArray) (start t : Nat) : UInt32 :=
  (schedulePrefix block start 80)[t]!

/-- A word of the extended schedule, read with its bound. -/
private theorem extended_eq {block : ByteArray} {start t : Nat} (within : t < 80) :
    extended block start t = (schedulePrefix block start 80)[t] :=
  getElem!_pos (schedulePrefix block start 80) t within

/-- The first sixteen words of the extended schedule are the block's words. -/
private theorem extended_input (block : ByteArray) (start i : Nat) (input : i < 16) :
    extended block start i = big32 block (start + 4 * i) := by
  rw [extended_eq (by omega), schedulePrefix_get block start (i + 1) 80 i (by omega) (by omega)]
  simp [schedulePrefix, input]

/-- The first window holds the block's sixteen words. -/
private theorem ofBytes_eq (block : ByteArray) (start : Nat) :
    Window.ofBytes (block.data.toList.drop start)
      = Window.ofFn fun i => extended block start (0 + i) := by
  simp (disch := decide) only [Window.ofBytes, Window.ofFn, word_drop, Nat.zero_add, extended_input]

/-- Each slide of the window moves one word along the extended schedule. -/
private theorem next_ofFn (block : ByteArray) (start t : Nat) (within : t + 16 < 80) :
    (Window.ofFn fun i => extended block start (t + i)).next
      = Window.ofFn fun i => extended block start (t + 1 + i) := by
  -- The new last word is `W_(t+16)`, by the recurrence.
  have last : extended block start (t + 16) = extended block start t +
      smallSigma0 (extended block start (t + 1)) + extended block start (t + 9) +
      smallSigma1 (extended block start (t + 14)) := by
    rw [extended_eq (by omega), extended_eq (by omega), extended_eq (by omega),
      extended_eq (by omega), extended_eq (by omega)]
    rw [schedulePrefix_recurrence block start 80 (t + 16) (by omega) within]
    simp only [show t + 16 - 16 = t by omega, show t + 16 - 15 = t + 1 by omega,
      show t + 16 - 7 = t + 9 by omega, show t + 16 - 2 = t + 14 by omega]
  -- The other words only move one place.
  simp only [Window.next, Window.ofFn, last, Nat.add_zero, Nat.add_assoc]

/-- The state of the specification after its first rounds of one block. -/
private def after (state : Vector UInt32 8) (block : ByteArray) (start n : Nat) : Vector UInt32 8 :=
  ((List.finRange 64).take n).foldl
    (fun current t => Sha256.round current K[t] (schedule block start)[t]) state

/-- One more round of the specification. -/
private theorem after_succ (state : Vector UInt32 8) (block : ByteArray) (start n : Nat)
    (within : n < 64) :
    after state block start (n + 1)
      = Sha256.round (after state block start n) K[n] (schedule block start)[n] := by
  rw [after, List.take_succ_eq_append_getElem (by simp; omega), List.foldl_append]
  simp [after]

/-- The first word of a window. -/
private theorem Window.ofFn_w0 (f : Nat → UInt32) : (Window.ofFn f).w0 = f 0 := rfl

/-- The extended schedule starts with the specification's schedule. -/
private theorem extended_schedule {block : ByteArray} {start t : Nat} (within : t < 64) :
    extended block start t = (schedule block start)[t] := by
  rw [extended_eq (by omega), schedule, schedulePrefix_get block start 64 80 t within (by omega)]

/-- The rounds from any round on finish the specification's rounds. -/
private theorem rounds_after (state : Vector UInt32 8) (block : ByteArray) (start : Nat) :
    ∀ m n, m + n = 64 →
      rounds (K.toList.drop n) (Window.ofFn fun i => extended block start (n + i))
          (Words.ofVector (after state block start n))
        = Words.ofVector (after state block start 64) := by
  intro m
  induction m with
  | zero =>
    intro n sum
    -- After the last round, no constant is left.
    obtain rfl : n = 64 := by omega
    rfl
  | succ m ih =>
    intro n sum
    -- Round `n` takes constant `K_n` and the first word of the window, `W_n`.
    rw [List.drop_eq_getElem_cons (by simp; omega), rounds, next_ofFn block start n (by omega),
      ← ih (n + 1) (by omega), after_succ state block start n (by omega)]
    simp only [Vector.getElem_toList]
    rw [Window.ofFn_w0, Nat.add_zero, extended_schedule (by omega)]
    rfl

/-- The record compression is the specification's, for every block. -/
theorem compress_eq (state : Vector UInt32 8) (block : ByteArray) (start : Nat) :
    compress (Words.ofVector state) (block.data.toList.drop start)
      = Words.ofVector (Sha256.compress state block start) := by
  have all := rounds_after state block start 64 0 rfl
  simp only [after, List.take_zero, List.foldl_nil, Nat.zero_add, List.drop_zero,
    List.take_of_length_le (show (List.finRange 64).length ≤ 64 by simp)] at all
  -- The working variables after all sixty-four rounds are added to the hash value, word by word.
  simp only [compress, ofBytes_eq, Nat.zero_add, all]
  simp only [Sha256.compress, Words.ofVector, Vector.getElem_zipWith]

/-- The record chain of blocks is the specification's, from any block on. -/
theorem chain_eq (padded : ByteArray) (count first : Nat) (state : Vector UInt32 8) :
    chain compress count (padded.data.toList.drop (64 * first)) (Words.ofVector state)
      = Words.ofVector ((List.range' first count).foldl
          (fun current i => Sha256.compress current padded (64 * i)) state) := by
  induction count generalizing first state with
  | zero => rfl
  | succ count ih =>
    -- One block on each side, then the rest from the next block on.
    rw [chain, List.drop_drop, compress_eq, show 64 * first + 64 = 64 * (first + 1) by omega, ih,
      List.range'_succ, List.foldl_cons]

/-- The list padding is the specification's padding. -/
theorem pad_eq (message : ByteArray) :
    pad message.data.toList = (Sha256.pad message).data.toList := by
  simp only [pad, Sha256.pad, ByteArray.data_append, ByteArray.data_push, Array.toList_append,
    Array.toList_push, Array.toList_replicate, Array.length_toList, ByteArray.size_data,
    List.append_assoc, List.cons_append, List.nil_append]

/-- SHA-256 is SHA-256 over the record forms, for every message. -/
theorem hash_eq (message : ByteArray) : Sha256.hash message = hash message := by
  have whole := chain_eq (Sha256.pad message) ((Sha256.pad message).size / 64) 0 IV
  simp only [Nat.mul_zero, List.drop_zero, ← List.range_eq_range'] at whole
  simp only [hash, pad_eq, Array.length_toList, ByteArray.size_data, whole, toVector_ofVector,
    Sha256.hash]

/-! ## Known answers

The SHA-256 examples of FIPS 180-2, Appendix B, checked by the kernel over the record forms. -/

/-- FIPS 180-2 Appendix B.1: the one-block message `abc`. -/
theorem hash_abc :
    (Sha256.hash "abc".toUTF8).data = #[
      0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
      0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
      0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
      0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad] := by
  rw [hash_eq, String.toUTF8_eq_toByteArray]
  decide +kernel

/-- FIPS 180-2 Appendix B.2: the 56-byte message that pads to two blocks. -/
theorem hash_twoBlocks :
    (Sha256.hash "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8).data = #[
      0x24, 0x8d, 0x6a, 0x61, 0xd2, 0x06, 0x38, 0xb8,
      0xe5, 0xc0, 0x26, 0x93, 0x0c, 0x3e, 0x60, 0x39,
      0xa3, 0x3c, 0xe4, 0x59, 0x64, 0xff, 0x21, 0x67,
      0xf6, 0xec, 0xed, 0xd4, 0x19, 0xdb, 0x06, 0xc1] := by
  rw [hash_eq, String.toUTF8_eq_toByteArray]
  decide +kernel

end Kernel

end EthLib.Cryptography.Hash.Sha256
