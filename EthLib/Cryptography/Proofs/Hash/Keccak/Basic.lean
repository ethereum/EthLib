module

public import EthLib.Cryptography.Hash.Keccak
import EthLib.Base.Proofs.Bytes
import Mathlib.Tactic.IntervalCases

/-!
# Proofs: `Hash.Keccak`

The constants of Keccak-f[1600] agree with the algorithms that define them.

Each step mapping, written lane by lane, is the formula of the standard for every lane.

The padding cuts every message into whole blocks, and no two messages pad alike.

The sponge reads the message in place, and absorbs the same blocks as the padded message.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Keccak

/-! ## The constants -/

/-- The table of round constants is what FIPS 202 §3.2.5, Algorithm 6 derives.

So no round constant is taken on trust. -/
theorem roundConstants_eq : RC = Vector.ofFn fun ir => Internal.roundConstant ir := by
  -- 24 constants of 7 bits each, with at most 167 register steps per bit.
  decide +kernel

/-- The table of rotation offsets is what FIPS 202 §3.2.2, Algorithm 2 derives.

So no rotation offset is taken on trust. -/
theorem rhoOffsets_eq : RHO.map UInt64.toNat = Internal.rhoOffsets := by
  -- Lean hides the bodies of `Array.map` and of the range loop, so state both over lists first.
  rw [← Vector.toList_inj, Vector.toList_map, Internal.rhoOffsets]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  -- The walk of 24 steps, run by the kernel.
  decide +kernel

/-! ## The step mappings are the formulas of the standard

Each theorem below states one step mapping for every lane, as FIPS 202 §3.2 writes it.

The coordinates are in `Fin 5`, where addition and subtraction wrap mod 5, as in §3.1.4. -/

/-- Lane `(x, y)` of a state, the field with the number `x + 5y`. -/
def State.lane (A : State) (x y : Fin 5) : UInt64 :=
  [A.a0, A.a1, A.a2, A.a3, A.a4, A.a5, A.a6, A.a7, A.a8, A.a9, A.a10, A.a11, A.a12, A.a13,
    A.a14, A.a15, A.a16, A.a17, A.a18, A.a19, A.a20, A.a21, A.a22, A.a23,
    A.a24][x.val + 5 * y.val]!

/-- The state whose lane `(x, y)` is `f x y`. -/
def State.ofLanes (f : Fin 5 → Fin 5 → UInt64) : State :=
  ⟨f 0 0, f 1 0, f 2 0, f 3 0, f 4 0, f 0 1, f 1 1, f 2 1, f 3 1, f 4 1,
    f 0 2, f 1 2, f 2 2, f 3 2, f 4 2, f 0 3, f 1 3, f 2 3, f 3 3, f 4 3,
    f 0 4, f 1 4, f 2 4, f 3 4, f 4 4⟩

/-- The parity `C[x]` of column `x`: the XOR of its five lanes. -/
def State.column (A : State) (x : Fin 5) : UInt64 :=
  A.lane x 0 ^^^ A.lane x 1 ^^^ A.lane x 2 ^^^ A.lane x 3 ^^^ A.lane x 4

/-- Theta is `A'[x, y] = A[x, y] ^ C[x - 1] ^ rot(C[x + 1], 1)`, FIPS 202 §3.2.1. -/
theorem theta_eq (A : State) :
    theta A = State.ofLanes fun x y =>
      A.lane x y ^^^ (A.column (x - 1) ^^^ rotl (A.column (x + 1)) 1) :=
  rfl

/-- Rho rotates lane `(x, y)` by the offset of index `x + 5y`, FIPS 202 §3.2.2. -/
theorem rho_eq (A : State) :
    rho A = State.ofLanes fun x y =>
      rotl (A.lane x y) (RHO[x.val + 5 * y.val]'(by simp only [LANES]; omega)) :=
  rfl

/-- Pi is `A'[x, y] = A[(x + 3y) mod 5, x]`, FIPS 202 §3.2.3. -/
theorem pi_eq (A : State) : pi A = State.ofLanes fun x y => A.lane (x + 3 * y) x :=
  rfl

/-- Chi is `A'[x, y] = A[x, y] ^ ((A[x + 1, y] ^ 1) & A[x + 2, y])`, FIPS 202 §3.2.4. -/
theorem chi_eq (A : State) :
    chi A = State.ofLanes fun x y => A.lane x y ^^^ (~~~A.lane (x + 1) y &&& A.lane (x + 2) y) :=
  rfl

/-- Iota XORs the round constant into lane `(0, 0)` and leaves the others, FIPS 202 §3.2.5. -/
theorem iota_eq (ir : Fin ROUNDS) (A : State) :
    iota ir A = State.ofLanes fun x y =>
      if x = 0 ∧ y = 0 then A.lane x y ^^^ RC[ir] else A.lane x y :=
  rfl

/-! ## The padding

FIPS 202 §4 cuts the padded message `P` into `n = len(P) / r` blocks of `r` bits.

Two facts make that sound:

- The padded length is a positive multiple of the rate, so no block is partial.
- Padding is injective, so two different messages never absorb the same blocks.

Both are about pad10*1 (§5.1), at any positive rate, so at 136 and at 72 bytes. -/

/-- Byte `i` of the padding is padding byte `i`, for each of its `rate - len mod rate` bytes. -/
theorem padding_data (rate len : Nat) :
    (padding rate len).data =
      Array.ofFn fun i : Fin (rate - len % rate) => paddingByte rate len i := by
  apply Array.ext
  · simp [padding]
  · intro i _ inside
    have hk : i < rate - len % rate := by simpa using inside
    simp only [padding, Array.getElem_ofFn]
    rw [Array.getElem_setIfInBounds (by simpa using hk),
      Array.getElem_setIfInBounds (by simpa using hk), Array.getElem_replicate]
    -- Byte i is written last when it is byte k - 1, and first when it is byte 0.
    split
    · next last => rw [last]
    · split
      · next first => rw [first]
      -- Any other padding byte is zero, as it holds neither 1 bit.
      · next notLast notFirst =>
        have hl : i + 1 ≠ rate - len % rate := by omega
        simp [paddingByte, Ne.symm notFirst, hl]

/-- The padding of a message of `len` bytes has `rate - len mod rate` bytes. -/
@[simp] theorem size_padding (rate len : Nat) :
    (padding rate len).size = rate - len % rate := by
  simp [ByteArray.size, padding_data]

/-- The padding has at most `rate` bytes, so it fits in one block. -/
theorem size_padding_le (rate len : Nat) : (padding rate len).size ≤ rate := by
  rw [size_padding]
  exact Nat.sub_le rate (len % rate)

/-- The padded length is the block count times the rate. -/
theorem size_pad {rate : Nat} (hr : 0 < rate) (msg : ByteArray) :
    (pad rate msg).size = rate * blockCount rate msg.size := by
  -- Write the message length as `rate * q + s` with `s < rate`.
  have hs : msg.size % rate < rate := Nat.mod_lt _ hr
  have hd := Nat.div_add_mod msg.size rate
  simp only [pad, ByteArray.size_append, size_padding, blockCount]
  -- Then `rate * q + s + (rate - s) = rate * (q + 1)`.
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- The padded length is a positive multiple of the rate.

So the sponge never reads a partial block. -/
theorem pad_size_dvd {rate : Nat} (hr : 0 < rate) (msg : ByteArray) :
    rate ∣ (pad rate msg).size ∧ 0 < (pad rate msg).size := by
  rw [size_pad hr]
  -- The block count is a quotient plus one, so at least one.
  exact ⟨⟨_, rfl⟩, Nat.mul_pos hr (Nat.succ_pos _)⟩

/-- Every block the sponge absorbs lies inside the padded message.

Block `i` covers bytes `rate * i` to `rate * i + rate - 1`.

The sponge runs `i` below the block count. -/
theorem block_le_size_pad {rate : Nat} (hr : 0 < rate) (msg : ByteArray) {i : Nat}
    (hi : i < blockCount rate msg.size) : rate * i + rate ≤ (pad rate msg).size := by
  rw [size_pad hr, ← Nat.mul_succ]
  exact Nat.mul_le_mul_left _ hi

/-- The padding always adds at least one byte. -/
theorem lt_size_pad {rate : Nat} (hr : 0 < rate) (msg : ByteArray) :
    msg.size < (pad rate msg).size := by
  rw [size_pad hr]
  -- `rate * (q + 1)` exceeds `rate * q + s`, since `s < rate`.
  have hs : msg.size % rate < rate := Nat.mod_lt _ hr
  have hd := Nat.div_add_mod msg.size rate
  simp only [blockCount, Nat.mul_add, Nat.mul_one]
  omega

/-- Bit 0 of a padding byte is set on the first padding byte, and only there. -/
theorem paddingByte_mod_two (rate len i : Nat) :
    (paddingByte rate len i).toNat % 2 = if i = 0 then 1 else 0 := by
  unfold paddingByte
  by_cases first : i = 0
  -- The first byte is 0x01 or 0x81: bit 0 set.
  · simp only [first, ite_true]
    split <;> decide
  -- Any later byte is 0x00 or 0x80: bit 0 clear.
  · simp only [first, ite_false]
    split <;> decide

/-- Byte `j` of a padded message: a message byte, then padding bytes counted from 0. -/
theorem getElem_pad_data (rate : Nat) (msg : ByteArray) (j : Nat)
    (h : j < (pad rate msg).data.size) :
    (pad rate msg).data[j] =
      if hj : j < msg.size then msg.data[j] else paddingByte rate msg.size (j - msg.size) := by
  simp only [pad, ByteArray.data_append] at h ⊢
  split
  -- Below the message length the byte is the message's own.
  · rw [Array.getElem_append_left]
  -- From there on it is padding byte `j - len`.
  · rename_i past
    rw [Array.getElem_append_right (Nat.le_of_not_lt past)]
    simp only [padding_data, Array.getElem_ofFn]
    rfl

/-- A shorter message in the same number of blocks pads differently.

Look at the byte where the longer message's padding starts:

```text
    longer:   [ ...  message  ...  | 0x01 or 0x81 | ... ]    bit 0 set
    shorter:  [ ... | padding byte j >= 1          | ... ]    bit 0 clear
```

Bit 0 is set only on a first padding byte, and the shorter message's padding started earlier. -/
private theorem pad_ne_of_lt {rate : Nat} (hr : 0 < rate) {a b : ByteArray}
    (shorter : a.size < b.size) (blocks : blockCount rate a.size = blockCount rate b.size) :
    pad rate a ≠ pad rate b := by
  intro same
  -- The byte at index `len(b)` exists in both padded strings, which have one length.
  have hb : b.size < (pad rate b).data.size := lt_size_pad hr b
  have ha : b.size < (pad rate a).data.size := by
    have : (pad rate a).size = (pad rate b).size := by rw [size_pad hr, size_pad hr, blocks]
    simp only [ByteArray.size] at this
    omega
  -- Equal strings agree on bit 0 of that byte.
  have bit0 :
      ((pad rate a).data[b.size]'ha).toNat % 2 = ((pad rate b).data[b.size]'hb).toNat % 2 := by
    simp only [same]
  -- For `a` it is padding byte `len(b) - len(a) >= 1`, for `b` padding byte 0.
  rw [getElem_pad_data, getElem_pad_data, dite_eq_right (by omega), dite_eq_right (Nat.lt_irrefl _),
    paddingByte_mod_two, paddingByte_mod_two, ite_eq_right (by omega), Nat.sub_self, ite_eq_left rfl]
    at bit0
  -- So 0 = 1.
  exact absurd bit0 (by decide)

/-- Padding is injective: two different messages never pad to the same blocks. -/
theorem pad_injective {rate : Nat} (hr : 0 < rate) : Function.Injective (pad rate) := by
  intro a b same
  -- Equal padded lengths mean equal block counts.
  have blocks : blockCount rate a.size = blockCount rate b.size := by
    have := congrArg ByteArray.size same
    rw [size_pad hr, size_pad hr] at this
    exact Nat.eq_of_mul_eq_mul_left hr this
  -- Neither message is shorter than the other.
  have lengths : a.size = b.size := by
    rcases Nat.lt_trichotomy a.size b.size with h | h | h
    · exact absurd same (pad_ne_of_lt hr h blocks)
    · exact h
    · exact absurd same.symm (pad_ne_of_lt hr h blocks.symm)
  -- Equal lengths mean equal padding, so the messages are equal prefixes of one string.
  have prefixes :
      a.data ++ (padding rate a.size).data = b.data ++ (padding rate a.size).data := by
    have := congrArg ByteArray.data same
    simpa only [pad, ByteArray.data_append, lengths] using this
  exact ByteArray.ext (Array.append_left_inj _ |>.mp prefixes)

/-! ## Lanes -/

/-- A byte widened to a lane keeps its eight bits, and is zero above them. -/
private theorem byteExtend (b : UInt8) (i : Nat) (hi : i < 64) :
    b.toUInt64.toBitVec.getLsbD i = (decide (i < 8) && b.toNat.testBit i) := by
  rw [UInt8.toBitVec_toUInt64, BitVec.getLsbD_setWidth]
  simp only [hi, decide_true, Bool.true_and]
  by_cases h : i < 8
  · simp only [h, decide_true, Bool.true_and]
    rw [← BitVec.testBit_toNat, UInt8.toNat_toBitVec]
  · simp only [h, decide_false, Bool.false_and]
    exact BitVec.getLsbD_of_ge b.toBitVec i (by omega)

/-- A byte shifted to byte `m` of a lane holds, at bit `i`, bit `i % 8` of the byte in byte `m`. -/
private theorem shiftedByte (b : UInt8) (m i : Nat) (hm : m < 8) (hi : i < 64) :
    (b.toUInt64 <<< UInt64.ofNat (8 * m)).toBitVec.getLsbD i =
      (decide (i / 8 = m) && b.toNat.testBit (i % 8)) := by
  have amount : (UInt64.ofNat (8 * m)).toBitVec.toNat % 64 = 8 * m := by
    simp
    omega
  simp only [UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', BitVec.toNat_umod,
    show (64 : BitVec 64).toNat = 64 by decide, amount, BitVec.getLsbD_shiftLeft, hi,
    decide_true, Bool.true_and]
  by_cases h : i / 8 = m
  · rw [byteExtend _ _ (by omega)]
    simp only [h, decide_true, Bool.true_and, show ¬ i < 8 * m by omega, decide_false,
      Bool.not_false, show i - 8 * m = i % 8 by omega, show i % 8 < 8 by omega]
  · by_cases low : i < 8 * m
    · simp [h, low]
    · rw [byteExtend _ _ (by omega)]
      simp [h, low, show ¬ i - 8 * m < 8 by omega]

/-- A lane read from a byte string is its eight bytes from the start, each shifted to its place. -/
private theorem laneAt_eq (bytes : ByteArray) (s : Nat) :
    Internal.laneAt bytes s =
      (EthLib.Base.byteAtOrZero bytes s).toUInt64 |||
      (EthLib.Base.byteAtOrZero bytes (s + 1)).toUInt64 <<< UInt64.ofNat (8 * 1) |||
      (EthLib.Base.byteAtOrZero bytes (s + 2)).toUInt64 <<< UInt64.ofNat (8 * 2) |||
      (EthLib.Base.byteAtOrZero bytes (s + 3)).toUInt64 <<< UInt64.ofNat (8 * 3) |||
      (EthLib.Base.byteAtOrZero bytes (s + 4)).toUInt64 <<< UInt64.ofNat (8 * 4) |||
      (EthLib.Base.byteAtOrZero bytes (s + 5)).toUInt64 <<< UInt64.ofNat (8 * 5) |||
      (EthLib.Base.byteAtOrZero bytes (s + 6)).toUInt64 <<< UInt64.ofNat (8 * 6) |||
      (EthLib.Base.byteAtOrZero bytes (s + 7)).toUInt64 <<< UInt64.ofNat (8 * 7) :=
  rfl

/-- Bit `i` of the lane at byte `s` is bit `i % 8` of byte `s + i / 8`, as in FIPS 202 §3.1.2. -/
theorem Internal.laneAt_testBit (bytes : ByteArray)
    (s i : Nat) (hi : i < 64) :
    (Internal.laneAt bytes s).toBitVec.getLsbD i =
      (EthLib.Base.byteAtOrZero bytes (s + i / 8)).toNat.testBit (i % 8) := by
  rw [laneAt_eq]
  simp only [UInt64.toBitVec_or, BitVec.getLsbD_or, byteExtend _ _ hi,
    shiftedByte _ 1 _ (by decide) hi, shiftedByte _ 2 _ (by decide) hi,
    shiftedByte _ 3 _ (by decide) hi, shiftedByte _ 4 _ (by decide) hi,
    shiftedByte _ 5 _ (by decide) hi, shiftedByte _ 6 _ (by decide) hi,
    shiftedByte _ 7 _ (by decide) hi]
  -- Exactly one of the eight bytes holds bit `i`: byte `i / 8`.
  have hq : i / 8 < 8 := by omega
  have low : (i < 8) ↔ (i / 8 = 0) := by omega
  have bit : i % 8 = i ∨ i / 8 ≠ 0 := by omega
  simp only [low]
  generalize hm : i / 8 = q at hq bit ⊢
  interval_cases q <;> simp_all
  -- Byte 0 holds bit `i` itself, since `i < 8`.
  rw [Nat.mod_eq_of_lt low]

/-! ## Blocks read in place

The sponge reads the blocks of the message in place, and builds no padded copy.

The whole blocks of the message are blocks of the padded message as they stand.

The last block is the rest of the message, with the two 1 bits of the padding XORed in.

So the sponge absorbs the same blocks as the padded message `P` of FIPS 202 §4, Algorithm 8. -/

/-- A lane reads only its own 8 bytes. -/
theorem laneAt_congr {a b : ByteArray} {s t : Nat}
    (h : ∀ k < 8, EthLib.Base.byteAtOrZero a (s + k) = EthLib.Base.byteAtOrZero b (t + k)) :
    Internal.laneAt a s = Internal.laneAt b t := by
  have h0 : EthLib.Base.byteAtOrZero a s = EthLib.Base.byteAtOrZero b t := by simpa using h 0 (by omega)
  unfold Internal.laneAt
  rw [h0, h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega), h 5 (by omega),
    h 6 (by omega), h 7 (by omega)]

open Internal in
/-- At a rate that is a whole number of lanes, a block lane is in the rate when `8i < rate`. -/
theorem Internal.blockLane_of_dvd {rate : Nat} (lanes : 8 ∣ rate) (read : Nat → UInt64)
    (start i : Nat) :
    blockLane rate read start i = if 8 * i < rate then read (start + 8 * i) else 0 := by
  obtain ⟨m, rfl⟩ := lanes
  -- Lane i lies wholly in the rate exactly when it starts in it.
  simp only [blockLane, show (8 * i + 8 ≤ 8 * m) = (8 * i < 8 * m) from propext (by omega)]

/-- Below the length of the message, the padded message holds the message's own bytes. -/
theorem byteAtOrZero_pad_of_lt (rate : Nat) {msg : ByteArray} {j : Nat} (h : j < msg.size) :
    EthLib.Base.byteAtOrZero (pad rate msg) j = EthLib.Base.byteAtOrZero msg j := by
  rw [pad, EthLib.Base.byteAtOrZero_append, ite_eq_left h]

/-- From the length of the message on, the padded message holds padding bytes, then zeros. -/
theorem byteAtOrZero_pad_of_le (rate : Nat) {msg : ByteArray} {j : Nat} (h : msg.size ≤ j) :
    EthLib.Base.byteAtOrZero (pad rate msg) j =
      if j - msg.size < rate - msg.size % rate then paddingByte rate msg.size (j - msg.size)
      else 0 := by
  rw [pad, EthLib.Base.byteAtOrZero_append, ite_eq_right (by omega), EthLib.Base.byteAtOrZero_eq_getD]
  split
  · next inside =>
    simp only [Array.getD_eq_getD_getElem?, padding_data, Array.getElem?_ofFn, inside,
      ↓reduceDIte, Option.getD_some]
  · next outside =>
    simp only [Array.getD_eq_getD_getElem?, padding_data, Array.getElem?_ofFn, outside,
      ↓reduceDIte, Option.getD_none]

/-- Bit `i` of the padding mask is bit 0 of the first flag, or bit 7 of the last flag. -/
private theorem maskBits : ∀ (first last : Bool) (i : Fin 8),
    (((if first then 1 else 0 : UInt8) ||| (if last then 128 else 0)).toNat.testBit i.val) =
      ((first && (decide (i.val = 0))) || (last && (decide (i.val = 7)))) := by
  decide +kernel

/-- Byte `pos` of the padding sets bit 0 when it is the first byte, and bit 7 when it is the last.

It sets no other bit. -/
theorem paddingByte_testBit (rate len pos bit : Nat) (h : bit < 8) :
    (paddingByte rate len pos).toNat.testBit bit =
      (decide (pos = 0 ∧ bit = 0) || decide (pos + 1 = rate - len % rate ∧ bit = 7)) := by
  have hb := maskBits (decide (pos = 0)) (decide (pos + 1 = rate - len % rate)) ⟨bit, h⟩
  simpa [paddingByte, Bool.and_eq_true] using hb

open Internal in
/-- A block that lies in the message reads the same lanes from the message and from `P`. -/
theorem blockLane_pad_of_le {rate : Nat} {msg : ByteArray} {start : Nat}
    (h : start + rate ≤ msg.size) (i : Nat) :
    blockLane rate (laneAt (pad rate msg)) start i = blockLane rate (laneAt msg) start i := by
  unfold blockLane
  split
  · exact laneAt_congr fun k hk => byteAtOrZero_pad_of_lt rate (by omega)
  · rfl

open Internal in
/-- The whole blocks of the message absorb alike from the message and from `P`. -/
theorem absorbBlocks_pad {m : Type → Type} [Monad m] (f : State → m State) (rate : Nat)
    (msg : ByteArray) (n start : Nat) (S : State) (h : start + rate * n ≤ msg.size) :
    absorbBlocks f rate (laneAt (pad rate msg)) n start S =
      absorbBlocks f rate (laneAt msg) n start S := by
  induction n generalizing start S with
  | zero => rfl
  | succ n ih =>
    have hlane : blockLane rate (laneAt (pad rate msg)) start = blockLane rate (laneAt msg) start :=
      funext (blockLane_pad_of_le (by rw [Nat.mul_succ] at h; omega))
    rw [absorbBlocks, absorbBlocks, absorbBlock, absorbBlock, hlane]
    exact congrArg _ (funext fun T => ih _ _ (by rw [Nat.mul_succ] at h; omega))

/-- A byte shifted to byte `m` of a lane, with the shift written as a natural number. -/
private theorem shiftedByte_toUInt64 (b : UInt8) (m i : Nat) (hm : m < 8) (hi : i < 64) :
    (b.toUInt64 <<< (8 * m).toUInt64).toBitVec.getLsbD i =
      (decide (i / 8 = m) && b.toNat.testBit (i % 8)) :=
  shiftedByte b m i hm hi

open Internal in
/-- Lane `i` of the last block of `P`: the lane of the rest of the message, and the padding bits.

The rest of the message starts the block, and its bytes past the end read as zero.

The padding puts bit 0 in byte `len mod rate` and bit 7 in byte `rate - 1` of the block. -/
theorem blockLane_pad_last (rate : Nat) (msg : ByteArray) (i : Nat) :
    blockLane rate (laneAt (pad rate msg)) (rate * (msg.size / rate)) i =
      blockLane rate (laneAt msg) (rate * (msg.size / rate)) i ^^^
        (if 8 * i + 8 ≤ rate ∧ msg.size % rate / 8 = i then
          (0x01 : UInt8).toUInt64 <<< (8 * (msg.size % rate % 8)).toUInt64 else 0) ^^^
        (if 8 * i + 8 ≤ rate ∧ (rate - 1) / 8 = i then
          (0x80 : UInt8).toUInt64 <<< (8 * ((rate - 1) % 8)).toUInt64 else 0) := by
  unfold blockLane
  by_cases hi : 8 * i + 8 ≤ rate
  swap
  · simp only [hi, false_and, ite_false, UInt64.xor_zero]
  have hr : 0 < rate := by omega
  have hdiv := Nat.div_add_mod msg.size rate
  have hs := Nat.mod_lt msg.size hr
  simp only [hi, true_and, ite_true]
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  have hb : z % 8 < 8 := Nat.mod_lt _ (by decide)
  have hm1 : msg.size % rate % 8 < 8 := Nat.mod_lt _ (by decide)
  have hm2 : (rate - 1) % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor, laneAt_testBit _ _ _ hz]
  -- Each padding bit is set where the padding puts it, and is clear elsewhere.
  have first : (if msg.size % rate / 8 = i then
      (0x01 : UInt8).toUInt64 <<< (8 * (msg.size % rate % 8)).toUInt64 else 0).toBitVec.getLsbD z
      = decide (8 * i + z / 8 = msg.size % rate ∧ z % 8 = 0) := by
    split
    · rw [shiftedByte_toUInt64 _ _ _ hm1 hz]
      generalize hc : z % 8 = c at hb
      interval_cases c <;> simp <;> first | omega | (intro; decide)
    · simp only [UInt64.toBitVec_zero, BitVec.getLsbD_zero]
      symm
      simp only [decide_eq_false_iff_not, not_and]
      omega
  have last : (if (rate - 1) / 8 = i then
      (0x80 : UInt8).toUInt64 <<< (8 * ((rate - 1) % 8)).toUInt64 else 0).toBitVec.getLsbD z
      = decide (8 * i + z / 8 = rate - 1 ∧ z % 8 = 7) := by
    split
    · rw [shiftedByte_toUInt64 _ _ _ hm2 hz]
      generalize hc : z % 8 = c at hb
      interval_cases c <;> simp [show Nat.testBit 128 7 = true by decide] <;>
        first | omega | (intro; decide)
    · simp only [UInt64.toBitVec_zero, BitVec.getLsbD_zero]
      symm
      simp only [decide_eq_false_iff_not, not_and]
      omega
  rw [first, last]
  -- Byte `8i + z / 8` of the block is a message byte, or a padding byte past the message.
  by_cases inMsg : rate * (msg.size / rate) + 8 * i + z / 8 < msg.size
  · rw [byteAtOrZero_pad_of_lt rate inMsg]
    have : ¬ (8 * i + z / 8 = msg.size % rate ∧ z % 8 = 0) := by omega
    have : ¬ (8 * i + z / 8 = rate - 1 ∧ z % 8 = 7) := by omega
    simp [*]
  · rw [byteAtOrZero_pad_of_le rate (by omega), EthLib.Base.byteAtOrZero_of_size_le (by omega),
      ite_eq_left (by omega), paddingByte_testBit _ _ _ _ hb]
    have hpos : rate * (msg.size / rate) + 8 * i + z / 8 - msg.size =
        8 * i + z / 8 - msg.size % rate := by
      omega
    rw [hpos]
    generalize hc : z % 8 = c at hb
    interval_cases c <;> simp <;> omega

/-- An index of 25 or more names no lane. -/
theorem State.xorLane_of_le (A : State) {i : Nat} (h : 25 ≤ i) (v : UInt64) :
    A.xorLane i v = A := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 25 := ⟨i - 25, by omega⟩
  rfl

/-- XORing one word into lane `i` of a block XORs it into lane `i` of the absorbed state. -/
theorem absorbBlock_lanes_xor (S : State) (g : Nat → UInt64) (i : Nat) (v : UInt64) :
    (⟨S.a0 ^^^ (g 0 ^^^ if 0 = i then v else 0), S.a1 ^^^ (g 1 ^^^ if 1 = i then v else 0),
      S.a2 ^^^ (g 2 ^^^ if 2 = i then v else 0), S.a3 ^^^ (g 3 ^^^ if 3 = i then v else 0),
      S.a4 ^^^ (g 4 ^^^ if 4 = i then v else 0), S.a5 ^^^ (g 5 ^^^ if 5 = i then v else 0),
      S.a6 ^^^ (g 6 ^^^ if 6 = i then v else 0), S.a7 ^^^ (g 7 ^^^ if 7 = i then v else 0),
      S.a8 ^^^ (g 8 ^^^ if 8 = i then v else 0), S.a9 ^^^ (g 9 ^^^ if 9 = i then v else 0),
      S.a10 ^^^ (g 10 ^^^ if 10 = i then v else 0), S.a11 ^^^ (g 11 ^^^ if 11 = i then v else 0),
      S.a12 ^^^ (g 12 ^^^ if 12 = i then v else 0), S.a13 ^^^ (g 13 ^^^ if 13 = i then v else 0),
      S.a14 ^^^ (g 14 ^^^ if 14 = i then v else 0), S.a15 ^^^ (g 15 ^^^ if 15 = i then v else 0),
      S.a16 ^^^ (g 16 ^^^ if 16 = i then v else 0), S.a17 ^^^ (g 17 ^^^ if 17 = i then v else 0),
      S.a18 ^^^ (g 18 ^^^ if 18 = i then v else 0), S.a19 ^^^ (g 19 ^^^ if 19 = i then v else 0),
      S.a20 ^^^ (g 20 ^^^ if 20 = i then v else 0), S.a21 ^^^ (g 21 ^^^ if 21 = i then v else 0),
      S.a22 ^^^ (g 22 ^^^ if 22 = i then v else 0), S.a23 ^^^ (g 23 ^^^ if 23 = i then v else 0),
      S.a24 ^^^ (g 24 ^^^ if 24 = i then v else 0)⟩ : State) =
    (⟨S.a0 ^^^ g 0, S.a1 ^^^ g 1, S.a2 ^^^ g 2, S.a3 ^^^ g 3, S.a4 ^^^ g 4, S.a5 ^^^ g 5,
      S.a6 ^^^ g 6, S.a7 ^^^ g 7, S.a8 ^^^ g 8, S.a9 ^^^ g 9, S.a10 ^^^ g 10, S.a11 ^^^ g 11,
      S.a12 ^^^ g 12, S.a13 ^^^ g 13, S.a14 ^^^ g 14, S.a15 ^^^ g 15, S.a16 ^^^ g 16,
      S.a17 ^^^ g 17, S.a18 ^^^ g 18, S.a19 ^^^ g 19, S.a20 ^^^ g 20, S.a21 ^^^ g 21,
      S.a22 ^^^ g 22, S.a23 ^^^ g 23, S.a24 ^^^ g 24⟩ : State).xorLane i v := by
  rcases Nat.lt_or_ge i 25 with h | h
  · interval_cases i <;> simp [State.xorLane, UInt64.xor_assoc]
  · rw [State.xorLane_of_le _ h]
    simp only [show ∀ j, j < 25 → (j = i) = False from fun j hj => eq_false (by omega),
      ite_false, UInt64.xor_zero, Nat.reduceLT]

open Internal in
/-- The state before the last permutation is FIPS 202 §4, Algorithm 8, run on `P`.

The blocks before the last one are absorbed from `P`, and the last block of `P` is XORed in. -/
theorem stateBeforeLastPermutation_eq_pad {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : State → m State) (rate : Nat) (msg : ByteArray) :
    stateBeforeLastPermutation f rate msg.size (laneAt msg) =
      (fun S => absorbBlock rate S (laneAt (pad rate msg)) (rate * (blockCount rate msg.size - 1)))
        <$> absorbBlocks f rate (laneAt (pad rate msg)) (blockCount rate msg.size - 1) 0
          State.zero := by
  rw [blockCount, Nat.add_sub_cancel,
    absorbBlocks_pad f rate msg _ 0 _ (by rw [Nat.zero_add]; exact Nat.mul_div_le _ _),
    stateBeforeLastPermutation, map_eq_pure_bind]
  refine congrArg _ (funext fun S => congrArg pure ?_)
  -- The last block of `P`: the lanes of the rest of the message, then the two padding bits.
  simp only [absorbBlock, blockLane_pad_last]
  unfold xorBlockByte
  generalize blockLane rate (laneAt msg) (rate * (msg.size / rate)) = l
  generalize (0x01 : UInt8).toUInt64 <<< (8 * (msg.size % rate % 8)).toUInt64 = v₁
  generalize (0x80 : UInt8).toUInt64 <<< (8 * ((rate - 1) % 8)).toUInt64 = v₂
  generalize msg.size % rate = p₁
  generalize rate - 1 = p₂
  -- A padding bit whose lane is in the rate goes into that lane alone; otherwise it is dropped.
  have bit : ∀ (p : Nat) (v : UInt64) j, (if 8 * j + 8 ≤ rate ∧ p / 8 = j then v else 0) =
      if 8 * (p / 8) + 8 ≤ rate then (if j = p / 8 then v else 0) else 0 := by
    intro p v j
    by_cases e : j = p / 8
    · subst e
      simp
    · simp only [e, ite_false, ite_self, ite_eq_right_iff, and_imp]
      omega
  simp only [bit]
  by_cases g₁ : 8 * (p₁ / 8) + 8 ≤ rate <;> by_cases g₂ : 8 * (p₂ / 8) + 8 ≤ rate <;>
    simp only [g₁, g₂, ite_true, ite_false, UInt64.xor_zero]
  · exact ((absorbBlock_lanes_xor S (fun j => l j ^^^ if j = p₁ / 8 then v₁ else 0) _ _).trans
      (congrArg (fun T => State.xorLane T _ v₂) (absorbBlock_lanes_xor S l _ _))).symm
  · exact (absorbBlock_lanes_xor S l _ _).symm
  · exact (absorbBlock_lanes_xor S l _ _).symm

/-! ## The absorbing phase -/

open Internal in
/-- Absorbing `k + n` blocks absorbs the first `k`, then the `n` after them. -/
theorem absorbBlocks_add {m : Type → Type} [Monad m] [LawfulMonad m] (f : State → m State)
    (rate : Nat) (read : Nat → UInt64) (k n start : Nat) (S : State) :
    absorbBlocks f rate read (k + n) start S
      = absorbBlocks f rate read k start S >>= absorbBlocks f rate read n (start + rate * k) := by
  induction k generalizing start S with
  | zero => simp [absorbBlocks]
  | succ k ih =>
    rw [Nat.succ_add, absorbBlocks, absorbBlocks, bind_assoc]
    refine congrArg _ (funext fun T => ?_)
    rw [ih, Nat.mul_succ, Nat.add_comm (rate * k), Nat.add_assoc]

/-- The absorbing phase is FIPS 202 §4, Algorithm 8, steps 1 to 6, block after block.

Every one of the `n` blocks of the padded message goes through `S = f(S ^ (P_i || 0^c))`. -/
theorem spongeAbsorb_eq {m : Type → Type} [Monad m] [LawfulMonad m] (f : State → m State)
    (rate : Nat) (msg : ByteArray) :
    Internal.spongeAbsorb f rate msg.size (Internal.laneAt msg) =
      Internal.absorbBlocks f rate (Internal.laneAt (pad rate msg)) (blockCount rate msg.size) 0
        State.zero := by
  -- The last of the n = len(N) / r + 1 blocks is the one the last permutation follows.
  rw [Internal.spongeAbsorb, stateBeforeLastPermutation_eq_pad, blockCount, Nat.add_sub_cancel,
    absorbBlocks_add, Nat.zero_add, bind_map_left]
  refine congrArg _ (funext fun S => ?_)
  simp only [Internal.absorbBlocks, bind_pure]

/-! ## Reading the message by lanes -/

/-- The rate of Keccak-256 is a whole number of lanes. -/
theorem lanes_rate : 8 ∣ RATE_256 := ⟨17, rfl⟩

open Internal in
/-- A block reads its message only at the offsets of its lanes in the rate. -/
theorem absorbBlock_congr_read (rate : Nat) (S : State) {read read' : Nat → UInt64} {s t : Nat}
    (h : ∀ i, 8 * i + 8 ≤ rate → read (s + 8 * i) = read' (t + 8 * i)) :
    absorbBlock rate S read s = absorbBlock rate S read' t := by
  have hlane : blockLane rate read s = blockLane rate read' t := by
    funext i
    unfold blockLane
    split
    · exact h i ‹_›
    · rfl
  simp only [absorbBlock, hlane]

open Internal in
/-- Absorbing `n` blocks reads the message only below `rate * n`, at multiples of 8. -/
theorem absorbBlocks_congr_read {m : Type → Type} [Monad m] (f : State → m State) {rate : Nat}
    (lanes : 8 ∣ rate) (n : Nat) (S : State) {read read' : Nat → UInt64} {s t : Nat}
    (h : ∀ q < rate * n, 8 ∣ q → read (s + q) = read' (t + q)) :
    absorbBlocks f rate read n s S = absorbBlocks f rate read' n t S := by
  induction n generalizing s t S with
  | zero => rfl
  | succ n ih =>
    rw [absorbBlocks, absorbBlocks, absorbBlock_congr_read rate S
      (fun i hi => h (8 * i) (by rw [Nat.mul_succ]; omega) ⟨i, rfl⟩)]
    refine congrArg _ (funext fun T => ih T ?_)
    intro q hq h8
    rw [Nat.add_assoc, Nat.add_assoc]
    exact h _ (by rw [Nat.mul_succ]; omega) (Nat.dvd_add lanes h8)

/-- The state before the last permutation reads the message only at multiples of 8.

So two lane readers that agree there give the same state. -/
theorem stateBeforeLastPermutation_congr {m : Type → Type} [Monad m] (f : State → m State)
    {rate : Nat} (lanes : 8 ∣ rate) (len : Nat) {read read' : Nat → UInt64}
    (h : ∀ q, 8 ∣ q → read q = read' q) :
    Internal.stateBeforeLastPermutation f rate len read =
      Internal.stateBeforeLastPermutation f rate len read' := by
  simp only [Internal.stateBeforeLastPermutation]
  rw [absorbBlocks_congr_read f lanes _ _ (read' := read') (t := 0)
      (fun q _ h8 => by simp only [Nat.zero_add]; exact h q h8)]
  refine congrArg _ (funext fun S => ?_)
  rw [absorbBlock_congr_read rate S (read' := read')
      (fun i _ => h _ (Nat.dvd_add (Dvd.dvd.mul_right lanes _) ⟨i, rfl⟩))]

/-- Keccak-256 of a byte string is the bytes of the squeezed state after absorbing it. -/
theorem keccak256_eq_squeeze256 (msg : ByteArray) :
    keccak256 msg = Internal.squeeze256 (Id.run (Internal.spongeAbsorb (fun S => pure (keccakF S))
      RATE_256 msg.size (Internal.laneAt msg))) :=
  rfl

/-- Keccak-256 over any permutation is the bytes of the squeezed state after absorbing. -/
theorem keccak256With_eq_squeeze256 {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : State → m State) (msg : ByteArray) :
    keccak256With f msg =
      Internal.squeeze256 <$> Internal.spongeAbsorb f RATE_256 msg.size (Internal.laneAt msg) := by
  rw [keccak256With, Internal.keccak256Read]
  exact Functor.map_map _ _ _

/-! ## A pure permutation

Over a permutation that is a pure function, the sponge in any lawful monad has no effect.

It returns the value the sponge computes in the identity monad. -/

open Internal in
/-- Absorbing over a pure permutation, in a lawful monad, is `pure` of the absorbed state. -/
theorem absorbBlocks_pure {m : Type → Type} [Monad m] [LawfulMonad m] (g : State → State)
    (rate : Nat) (read : Nat → UInt64) (n start : Nat) (S : State) :
    absorbBlocks (m := m) (fun T => pure (g T)) rate read n start S =
      pure (Id.run (absorbBlocks (fun T => pure (g T)) rate read n start S)) := by
  induction n generalizing start S with
  | zero => rfl
  | succ n ih => rw [absorbBlocks, pure_bind, ih]; rfl

open Internal in
/-- The state before the last permutation, over a pure permutation, is `pure` of its value. -/
theorem stateBeforeLastPermutation_pure {m : Type → Type} [Monad m] [LawfulMonad m]
    (g : State → State) (rate len : Nat) (read : Nat → UInt64) :
    stateBeforeLastPermutation (m := m) (fun T => pure (g T)) rate len read =
      pure (Id.run (stateBeforeLastPermutation (fun T => pure (g T)) rate len read)) := by
  rw [stateBeforeLastPermutation, absorbBlocks_pure, pure_bind]; rfl

open Internal in
/-- The absorbing phase over a pure permutation is `pure` of its value. -/
theorem spongeAbsorb_pure {m : Type → Type} [Monad m] [LawfulMonad m] (g : State → State)
    (rate len : Nat) (read : Nat → UInt64) :
    spongeAbsorb (m := m) (fun T => pure (g T)) rate len read =
      pure (Id.run (spongeAbsorb (fun T => pure (g T)) rate len read)) := by
  rw [spongeAbsorb, stateBeforeLastPermutation_pure, pure_bind]; rfl

/-- Keccak-256 of lanes over a pure permutation is `pure` of its value. -/
theorem keccak256LanesWith_pure {m : Type → Type} [Monad m] [LawfulMonad m] (g : State → State)
    (lanes : Array UInt64) :
    keccak256LanesWith (m := m) (fun T => pure (g T)) lanes =
      pure (Id.run (keccak256LanesWith (fun T => pure (g T)) lanes)) := by
  rw [keccak256LanesWith, Internal.keccak256Read, spongeAbsorb_pure, map_pure]; rfl

/-- Keccak-256 of bytes over a pure permutation is `pure` of its value. -/
theorem keccak256With_pure {m : Type → Type} [Monad m] [LawfulMonad m] (g : State → State)
    (msg : ByteArray) :
    keccak256With (m := m) (fun T => pure (g T)) msg =
      pure (Id.run (keccak256With (fun T => pure (g T)) msg)) := by
  rw [keccak256With, Internal.keccak256Read, spongeAbsorb_pure, map_pure]
  exact map_pure _ _

/-- Keccak-256 of lanes over Keccak-f[1600], in a lawful monad, is `pure` of its Keccak-256. -/
theorem keccak256LanesWith_keccakF {m : Type → Type} [Monad m] [LawfulMonad m]
    (lanes : Array UInt64) :
    keccak256LanesWith (m := m) (fun T => pure (keccakF T)) lanes = pure (keccak256Lanes lanes) :=
  keccak256LanesWith_pure keccakF lanes

/-- Keccak-256 of bytes over Keccak-f[1600], in a lawful monad, is `pure` of its Keccak-256. -/
theorem keccak256With_keccakF {m : Type → Type} [Monad m] [LawfulMonad m] (msg : ByteArray) :
    keccak256With (m := m) (fun T => pure (keccakF T)) msg = pure (keccak256 msg) :=
  keccak256With_pure keccakF msg

end EthLib.Cryptography.Hash.Keccak
