import EthLib.Cryptography.Hash.Keccak

/-!
# Proofs: `Hash.Keccak`

The constants of Keccak-f[1600] agree with the algorithms that define them.

The permutation agrees with the Keccak team's reference values.

The padding cuts every message into whole blocks, and no two messages pad alike.
-/

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

/-! ## Known answers

Both come from `KeccakF-1600-IntermediateValues.txt`, in the `tests/TestVectors/` directory of the Keccak team's XKCP repository.

That file applies Keccak-f[1600] twice:

```text
    all-zero state  --f-->  output 1  --f-->  output 2
```

Each theorem pins all 25 lanes, so every round, step mapping and constant is exercised. -/

/-- Output 1 of the reference file, lane `(x, y)` at index `x + 5 * y`. -/
def zeroOnce : State := #v[
  0xF1258F7940E1DDE7, 0x84D5CCF933C0478A, 0xD598261EA65AA9EE, 0xBD1547306F80494D, 0x8B284E056253D057,
  0xFF97A42D7F8E6FD4, 0x90FEE5A0A44647C4, 0x8C5BDA0CD6192E76, 0xAD30A6F71B19059C, 0x30935AB7D08FFC64,
  0xEB5AA93F2317D635, 0xA9A6E6260D712103, 0x81A57C16DBCF555F, 0x43B831CD0347C826, 0x01F22F1A11A5569F,
  0x05E5635A21D9AE61, 0x64BEFEF28CC970F2, 0x613670957BC46611, 0xB87C5A554FD00ECB, 0x8C3EE88A1CCF32C8,
  0x940C7922AE3A2614, 0x1841F924A2C509E4, 0x16F53526E70465C2, 0x75F644E97F30A13B, 0xEAF1FF7B5CECA249]

/-- Output 2 of the reference file, lane `(x, y)` at index `x + 5 * y`. -/
def zeroTwice : State := #v[
  0x2D5C954DF96ECB3C, 0x6A332CD07057B56D, 0x093D8D1270D76B6C, 0x8A20D9B25569D094, 0x4F9C4F99E5E7F156,
  0xF957B9A2DA65FB38, 0x85773DAE1275AF0D, 0xFAF4F247C3D810F7, 0x1F1B9EE6F79A8759, 0xE4FECC0FEE98B425,
  0x68CE61B6B9CE68A1, 0xDEEA66C4BA8F974F, 0x33C43D836EAFB1F5, 0xE00654042719DBD9, 0x7CF8A9F009831265,
  0xFD5449A6BF174743, 0x97DDAD33D8994B40, 0x48EAD5FC5D0BE774, 0xE3B8C8EE55B7B03C, 0x91A0226E649E42E9,
  0x900E3129E7BADD7B, 0x202A9EC5FAA3CCE8, 0x5B3402464E1C3DB6, 0x609F4E62A44C1059, 0x20D06CD26A8FBF5C]

/-- Keccak-f[1600] of the all-zero state. -/
theorem keccakF_zero : keccakF State.zero = zeroOnce := by
  -- 24 rounds on 25 lanes, evaluated by the kernel.
  decide +kernel

/-- Keccak-f[1600] of the previous output. -/
theorem keccakF_zeroOnce : keccakF zeroOnce = zeroTwice := by
  -- 24 rounds on 25 lanes, evaluated by the kernel.
  decide +kernel

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
