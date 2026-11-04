module

public import EthLib.Cryptography.Hash.Crc32c

/-!
# Proofs: CRC-32C

Every message followed by its digest leaves the remainder `0x1c2d19ed`, as RFC 3720 §12.1 states.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Crc32c

/-! ## The remainder of a message followed by its digest

The last bullet of RFC 3720 §12.1: a message extended with its digest always leaves the remainder `0x1c2d19ed`.

The proof rests on two facts.

- The division is linear over GF(2): the XOR of two inputs gives the XOR of the remainders.
- Feeding a remainder its own bits, highest first, shifts every bit out and leaves 0.

The digest is the complemented remainder.

So feeding it is feeding the remainder's own bits, XORed with 32 ones.

By linearity, the result is the remainder of 32 ones fed into 0, which is `0x1c2d19ed`. -/

/-- The division step tests the coefficient of x^31, which is bit 31 of the register. -/
theorem top_eq_getLsbD (r : UInt32) : (r >>> 31 == 1) = r.toBitVec.getLsbD 31 := by
  rw [Bool.eq_iff_iff, beq_iff_eq, ← UInt32.toBitVec_inj]
  simp [BitVec.eq_of_getLsbD_eq_iff]
  constructor
  · intro h
    simpa using h 0 (by omega)
  · intro h i hi
    rcases i with _ | i
    · simpa using h
    -- Bits above 31 do not exist, so they read as 0.
    · simp [BitVec.getLsbD_of_ge r.toBitVec (31 + (i + 1)) (by omega)]

/-- Multiplying by x commutes with adding. -/
theorem shiftLeft_xor (r s : UInt32) : (r ^^^ s) <<< 1 = (r <<< 1) ^^^ (s <<< 1) := by
  apply UInt32.toBitVec_inj.mp
  simp [BitVec.shiftLeft_xor_distrib]

/-- What one division step adds after the multiplication by x: G(x) or nothing. -/
def feedback (b : Bool) : UInt32 := if b then generator else 0

/-- Adding two feedbacks is the feedback of the sum. -/
theorem feedback_xor (a b : Bool) : feedback (a ^^ b) = feedback a ^^^ feedback b := by
  cases a <;> cases b <;> simp [feedback]

/-- One division step: multiply by x, then add the feedback. -/
theorem shift_eq_feedback (r : UInt32) (c : Bool) :
    shift r c = (r <<< 1) ^^^ feedback ((r >>> 31 == 1) ^^ c) := by
  unfold shift feedback
  split <;> simp

/-- One division step is linear in the register and the coefficient together. -/
theorem shift_xor (r s : UInt32) (c d : Bool) :
    shift (r ^^^ s) (c ^^ d) = shift r c ^^^ shift s d := by
  -- The feedback bit of the sum is the sum of the feedback bits.
  have top : (((r ^^^ s) >>> 31 == 1) ^^ (c ^^ d))
      = (((r >>> 31 == 1) ^^ c) ^^ ((s >>> 31 == 1) ^^ d)) := by
    simp only [top_eq_getLsbD, UInt32.toBitVec_xor, BitVec.getLsbD_xor]
    cases r.toBitVec.getLsbD 31 <;> cases s.toBitVec.getLsbD 31 <;> cases c <;> cases d <;> rfl
  rw [shift_eq_feedback, shift_eq_feedback, shift_eq_feedback, top, feedback_xor, shiftLeft_xor]
  ac_rfl

/-- Linearity carries over to any run of division steps of equal length. -/
theorem foldl_shift_xor (cs ds : List Bool) (h : cs.length = ds.length) (r s : UInt32) :
    (List.zipWith (· ^^ ·) cs ds).foldl shift (r ^^^ s) = cs.foldl shift r ^^^ ds.foldl shift s := by
  induction cs generalizing ds r s with
  | nil =>
    cases ds with
    | nil => rfl
    | cons _ _ => simp at h
  | cons c cs ih =>
    cases ds with
    | nil => simp at h
    | cons d ds =>
      simp only [List.zipWith_cons_cons, List.foldl_cons]
      rw [shift_xor]
      exact ih ds (by simpa using h) _ _

/-- The first n bits of a register, the coefficient of x^31 first. -/
def topBits (r : UInt32) (n : Nat) : List Bool :=
  (List.range n).map fun k => r.toBitVec.getLsbD (31 - k)

/-- Feeding a register its own first n bits multiplies it by x^n and never adds G(x). -/
theorem foldl_shift_topBits (r : UInt32) (n : Nat) (hn : n ≤ 32) :
    ((topBits r n).foldl shift r).toBitVec = r.toBitVec <<< n := by
  induction n with
  | zero => simp [topBits]
  | succ n ih =>
    simp only [topBits, List.range_succ, List.map_append, List.foldl_append, List.map_cons,
      List.map_nil, List.foldl_cons, List.foldl_nil] at ih ⊢
    generalize hX : List.foldl shift r
      (List.map (fun k => r.toBitVec.getLsbD (31 - k)) (List.range n)) = X at ih ⊢
    have hX' := ih (by omega)
    -- After n steps, the coefficient of x^31 is bit 31 - n of the starting register.
    have same : (X >>> 31 == 1) = r.toBitVec.getLsbD (31 - n) := by
      rw [top_eq_getLsbD, hX', BitVec.getLsbD_shiftLeft]
      simp
      omega
    -- The incoming bit equals that coefficient, so the feedback is 0.
    rw [shift_eq_feedback, same, Bool.xor_self]
    simp only [feedback, Bool.false_eq_true, ↓reduceIte, UInt32.xor_zero]
    rw [UInt32.toBitVec_shiftLeft, hX']
    simp [BitVec.shiftLeft_add]

/-- After all 32 of its own bits, the register is 0. -/
theorem foldl_shift_topBits_32 (r : UInt32) : (topBits r 32).foldl shift r = 0 := by
  apply UInt32.toBitVec_inj.mp
  rw [foldl_shift_topBits r 32 (by omega)]
  simp

/-- The eight bits of a byte, in the order they enter the division. -/
def byteBits (b : UInt8) : List Bool :=
  (List.range 8).map fun i => (b >>> i.toUInt8) &&& 1 == 1

/-- Dividing byte by byte is dividing bit by bit. -/
theorem foldl_shiftByte (bytes : List UInt8) (r : UInt32) :
    bytes.foldl shiftByte r = (bytes.flatMap byteBits).foldl shift r := by
  induction bytes generalizing r with
  | nil => rfl
  | cons b bytes ih =>
    simp only [List.foldl_cons, List.flatMap_cons, List.foldl_append, ih]
    simp [shiftByte, byteBits, List.foldl_map]

/-- A reversed byte enters its bits from bit 7 down, checked on all 256 bytes. -/
theorem byteBits_reverseBits_all :
    ∀ n, n < 256 → byteBits (reverseBits n.toUInt8)
      = (List.range 8).map fun j => n.toUInt8.toBitVec.getLsbD (7 - j) := by
  decide +kernel

/-- A reversed byte enters its bits from bit 7 down. -/
theorem byteBits_reverseBits (b : UInt8) :
    byteBits (reverseBits b) = (List.range 8).map fun j => b.toBitVec.getLsbD (7 - j) := by
  simpa using byteBits_reverseBits_all b.toNat b.toNat_lt

/-- The four digest bytes of a word enter its 32 bits, the coefficient of x^31 first. -/
theorem digest_bits (r : UInt32) :
    [reverseBits (r >>> 24).toUInt8, reverseBits (r >>> 16).toUInt8,
      reverseBits (r >>> 8).toUInt8, reverseBits r.toUInt8].flatMap byteBits = topBits r 32 := by
  simp [byteBits_reverseBits, topBits, List.range_succ]

/-- The division of a concatenation continues from the remainder of the first part. -/
theorem remainder_append (a b : ByteArray) :
    remainder (a ++ b) = b.data.toList.foldl shiftByte (remainder a) := by
  simp [remainder, ByteArray.data_append, List.foldl_append]

/-- RFC 3720 §12.1: every message followed by its digest leaves the remainder `0x1c2d19ed`. -/
theorem remainder_append_digest (data : ByteArray) :
    remainder (data ++ ⟨(digest data).toArray⟩) = 0x1c2d19ed := by
  -- The bits of the complement are the bits of the remainder, each XORed with 1.
  have flip : topBits (~~~remainder data) 32
      = List.zipWith (· ^^ ·) (topBits (remainder data) 32) (List.replicate 32 true) := by
    simp [topBits, List.range_succ]
  -- 32 ones fed into the zero register.
  have ones : (List.replicate 32 true).foldl shift 0 = 0x1c2d19ed := by
    decide +kernel
  have linear := foldl_shift_xor (topBits (remainder data) 32) (List.replicate 32 true)
    (by simp [topBits]) (remainder data) 0
  rw [UInt32.xor_zero] at linear
  rw [remainder_append]
  simp only [digest, Vector.toArray_mk, List.toList_toArray]
  rw [foldl_shiftByte, digest_bits, flip, linear, foldl_shift_topBits_32, ones, UInt32.zero_xor]

end EthLib.Cryptography.Hash.Crc32c
