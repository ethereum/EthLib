module

public import EthLib.Cryptography.Hash.Keccak
-- The kernel checks the constants by reducing `Array.map` and the finite range loop.
import all Init.Data.Array.Basic
import all Init.Data.Range.Basic

/-!
# Proofs: `Hash.Keccak`

The constants of Keccak-f[1600] agree with the algorithms that define them.

Each step mapping, written lane by lane, is the formula of the standard for every lane.

The padding cuts every message into whole blocks, and no two messages pad alike.
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

Both are about pad10*1 (§5.1), here at `r = 136` bytes. -/

/-- The padding of a message of `len` bytes has `136 - len mod 136` bytes, from 1 to 136. -/
@[simp] theorem size_padding (len : Nat) : (padding len).size = RATE - len % RATE := by
  simp [padding, ByteArray.size]

/-- The padded length is the block count times the rate. -/
theorem size_pad (msg : ByteArray) : (pad msg).size = RATE * blockCount msg.size := by
  -- Write the message length as 136 q + s with s < 136.
  have hs : msg.size % RATE < RATE := Nat.mod_lt _ (by decide)
  have hd := Nat.div_add_mod msg.size RATE
  simp only [pad, ByteArray.size_append, size_padding, blockCount]
  -- Then 136 q + s + (136 - s) = 136 (q + 1).
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- The padded length is a positive multiple of the rate.

So the sponge never reads a partial block. -/
theorem pad_size_dvd (msg : ByteArray) : RATE ∣ (pad msg).size ∧ 0 < (pad msg).size := by
  rw [size_pad]
  -- The block count is a quotient plus one, so at least one.
  exact ⟨⟨_, rfl⟩, Nat.mul_pos (by decide) (Nat.succ_pos _)⟩

/-- Every block the sponge absorbs lies inside the padded message.

Block `i` covers bytes `136 i` to `136 i + 135`, and the sponge runs `i` below the block count. -/
theorem block_le_size_pad (msg : ByteArray) {i : Nat} (hi : i < blockCount msg.size) :
    RATE * i + RATE ≤ (pad msg).size := by
  rw [size_pad, ← Nat.mul_succ]
  exact Nat.mul_le_mul_left _ hi

/-- The padding always adds at least one byte. -/
theorem lt_size_pad (msg : ByteArray) : msg.size < (pad msg).size := by
  rw [size_pad]
  -- 136 (q + 1) exceeds 136 q + s, since s < 136.
  have hs : msg.size % RATE < RATE := Nat.mod_lt _ (by decide)
  have hd := Nat.div_add_mod msg.size RATE
  simp only [blockCount, Nat.mul_add, Nat.mul_one]
  omega

/-- Bit 0 of a padding byte is set on the first padding byte, and only there. -/
theorem paddingByte_mod_two (len i : Nat) :
    (paddingByte len i).toNat % 2 = if i = 0 then 1 else 0 := by
  unfold paddingByte
  by_cases first : i = 0
  -- The first byte is 0x01 or 0x81: bit 0 set.
  · simp only [first, ite_true]
    split <;> decide
  -- Any later byte is 0x00 or 0x80: bit 0 clear.
  · simp only [first, ite_false]
    split <;> decide

/-- Byte `j` of a padded message: a message byte, then padding bytes counted from 0. -/
theorem getElem_pad_data (msg : ByteArray) (j : Nat) (h : j < (pad msg).data.size) :
    (pad msg).data[j] =
      if hj : j < msg.size then msg.data[j] else paddingByte msg.size (j - msg.size) := by
  simp only [pad, ByteArray.data_append] at h ⊢
  split
  -- Below the message length the byte is the message's own.
  · rw [Array.getElem_append_left]
  -- From there on it is padding byte `j - len`.
  · rename_i past
    rw [Array.getElem_append_right (Nat.le_of_not_lt past)]
    unfold padding
    rw [Array.getElem_ofFn]
    rfl

/-- A shorter message in the same number of blocks pads differently.

Look at the byte where the longer message's padding starts:

```text
    longer:   [ ...  message  ...  | 0x01 or 0x81 | ... ]    bit 0 set
    shorter:  [ ... | padding byte j >= 1          | ... ]    bit 0 clear
```

Bit 0 is set only on a first padding byte, and the shorter message's padding started earlier. -/
private theorem pad_ne_of_lt {a b : ByteArray} (shorter : a.size < b.size)
    (blocks : blockCount a.size = blockCount b.size) : pad a ≠ pad b := by
  intro same
  -- The byte at index `len(b)` exists in both padded strings, which have one length.
  have hb : b.size < (pad b).data.size := lt_size_pad b
  have ha : b.size < (pad a).data.size := by
    have : (pad a).size = (pad b).size := by rw [size_pad, size_pad, blocks]
    simp only [ByteArray.size] at this
    omega
  -- Equal strings agree on bit 0 of that byte.
  have bit0 : ((pad a).data[b.size]'ha).toNat % 2 = ((pad b).data[b.size]'hb).toNat % 2 := by
    simp only [same]
  -- For `a` it is padding byte `len(b) - len(a) >= 1`, for `b` padding byte 0.
  rw [getElem_pad_data, getElem_pad_data, dite_eq_right (by omega), dite_eq_right (Nat.lt_irrefl _),
    paddingByte_mod_two, paddingByte_mod_two, ite_eq_right (by omega), Nat.sub_self, ite_eq_left rfl]
    at bit0
  -- So 0 = 1.
  exact absurd bit0 (by decide)

/-- Padding is injective: two different messages never pad to the same blocks. -/
theorem pad_injective : Function.Injective pad := by
  intro a b same
  -- Equal padded lengths mean equal block counts.
  have blocks : blockCount a.size = blockCount b.size := by
    have := congrArg ByteArray.size same
    rw [size_pad, size_pad] at this
    exact Nat.eq_of_mul_eq_mul_left (by decide) this
  -- Neither message is shorter than the other.
  have lengths : a.size = b.size := by
    rcases Nat.lt_trichotomy a.size b.size with h | h | h
    · exact absurd same (pad_ne_of_lt h blocks)
    · exact h
    · exact absurd same.symm (pad_ne_of_lt h blocks.symm)
  -- Equal lengths mean equal padding, so the messages are equal prefixes of one string.
  have prefixes : a.data ++ (padding a.size).data = b.data ++ (padding a.size).data := by
    have := congrArg ByteArray.data same
    simpa only [pad, ByteArray.data_append, lengths] using this
  exact ByteArray.ext (Array.append_left_inj _ |>.mp prefixes)

end EthLib.Cryptography.Hash.Keccak
