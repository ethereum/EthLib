module

public import EthLib.Cryptography.Aes.Block

/-!
# Proofs: `Aes.Block`

The S-box table is the S-box that FIPS 197 §5.1.1 defines, and the inverse table inverts it.

The round constants are the ten values of FIPS 197 Table 5.

The inverse cipher inverts the cipher for every key schedule, so for every key.

Each word of the key schedule is a key word or follows the recurrence of FIPS 197 §5.2, Algorithm 2.

That recurrence needs a key of at least one word.

AES-128 and AES-256 equal a model of FIPS 197, for every key and every block.

The model has its own multiplication in GF(2^8), its own S-box and its own key schedule.

EthLib has no AES-192, so no theorem here covers it.

No theorem compares the inverse cipher with a model of Algorithm 3 of §5.3.

The inverse cipher undoes the cipher, so it also undoes the model's cipher.
-/

@[expose] public section

namespace EthLib.Cryptography.Aes

/-- A check that the kernel runs on the 256 bytes holds for every byte. -/
theorem forall_of_all {p : UInt8 → Bool} (h : (List.range 256).all fun b => p b.toUInt8)
    (b : UInt8) : p b = true := by
  have hb : b.toNat ∈ List.range 256 := List.mem_range.mpr b.toNat_lt
  simpa using List.all_eq_true.mp h _ hb

/-! ## The S-box -/

/-- The power `b^254` of FIPS 197 §4.4 is an inverse: `b • b^-1 = {01}` for `b ≠ {00}`. -/
theorem mul_inv (b : UInt8) (h : b ≠ 0) : mul b (Internal.inv b) = 1 := by
  -- 256 products, run by the kernel.
  have all := forall_of_all (p := fun b => b == 0 || mul b (Internal.inv b) == 1)
    (by decide +kernel) b
  simpa [h] using all

/-- Table 4 is the S-box that FIPS 197 §5.1.1 defines, entry by entry. -/
theorem sbox_eq (b : UInt8) : sbox b = Internal.sbox b := by
  -- 256 inverses and affine maps, run by the kernel.
  simpa using forall_of_all (p := fun b => sbox b == Internal.sbox b) (by decide +kernel) b

/-- Table 6 undoes Table 4: `INVSBOX[SBOX[b]] = b` for every byte. -/
@[simp] theorem invSbox_sbox (b : UInt8) : invSbox (sbox b) = b := by
  simpa using forall_of_all (p := fun b => invSbox (sbox b) == b) (by decide +kernel) b

/-- Table 4 undoes Table 6: `SBOX[INVSBOX[b]] = b` for every byte. -/
@[simp] theorem sbox_invSbox (b : UInt8) : sbox (invSbox b) = b := by
  simpa using forall_of_all (p := fun b => sbox (invSbox b) == b) (by decide +kernel) b

/-! ## The round constants -/

/-- The first bytes of `Rcon[1]` to `Rcon[10]` are the values of FIPS 197 Table 5. -/
theorem rcon_table :
    (List.range' 1 10).map (fun j => (rcon j)[0]) =
      [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36] := by
  decide +kernel

/-! ## Linearity over GF(2)

Multiplication by a fixed byte is additive: `a • (c ^ c') = a • c ^ a • c'`.

So MIXCOLUMNS and INVMIXCOLUMNS are additive in each column.

An additive map on bytes is fixed by its values on the eight one-bit bytes.

So the kernel checks 32 columns instead of 2^32. -/

theorem xor_and (a b c : UInt8) : (a ^^^ b) &&& c = (a &&& c) ^^^ (b &&& c) := by
  apply UInt8.eq_of_toBitVec_eq
  simp only [UInt8.toBitVec_and, UInt8.toBitVec_xor]
  ext i
  simp only [BitVec.getElem_and, BitVec.getElem_xor]
  cases a.toBitVec[i] <;> cases b.toBitVec[i] <;> cases c.toBitVec[i] <;> rfl

theorem xor_shiftLeft (a b : UInt8) : (a ^^^ b) <<< 1 = (a <<< 1) ^^^ (b <<< 1) := by
  apply UInt8.eq_of_toBitVec_eq
  simp [BitVec.shiftLeft_xor_distrib]

theorem xor_shiftRight (a b : UInt8) : (a ^^^ b) >>> 1 = (a >>> 1) ^^^ (b >>> 1) := by
  apply UInt8.eq_of_toBitVec_eq
  simp [BitVec.ushiftRight_xor_distrib]

/-- XTIMES is additive: the shift is, and the reduction adds `{1b}` once per set top bit. -/
theorem xtimes_xor (a b : UInt8) : xtimes (a ^^^ b) = xtimes a ^^^ xtimes b := by
  -- The top bit of a byte is clear or set.
  have top (a : UInt8) : a &&& 0x80 = 0 ∨ a &&& 0x80 = 0x80 := by
    simpa using forall_of_all (p := fun a => a &&& 0x80 == 0 || a &&& 0x80 == 0x80)
      (by decide +kernel) a
  unfold xtimes
  rw [xor_and, xor_shiftLeft]
  rcases top a with ha | ha <;> rcases top b with hb | hb <;>
    simp [ha, hb] <;> ac_nf <;> simp only [← UInt8.xor_assoc, UInt8.xor_self, UInt8.zero_xor]

theorem mulAux_xor (n : Nat) (b c c' : UInt8) :
    mulAux n b (c ^^^ c') = mulAux n b c ^^^ mulAux n b c' := by
  -- The low bit of a byte is clear or set.
  have low (a : UInt8) : a &&& 1 = 0 ∨ a &&& 1 = 1 := by
    simpa using forall_of_all (p := fun a => a &&& 1 == 0 || a &&& 1 == 1) (by decide +kernel) a
  induction n generalizing b c c' with
  | zero => simp [mulAux]
  | succ n ih =>
    simp only [mulAux, xor_and, xor_shiftRight, ih]
    rcases low c with hc | hc <;> rcases low c' with hc' | hc' <;>
      simp [hc, hc'] <;> ac_nf <;> simp only [← UInt8.xor_assoc, UInt8.xor_self, UInt8.zero_xor]

/-- Multiplication by a fixed byte is additive in the other factor. -/
theorem mul_xor (a c c' : UInt8) : mul a (c ^^^ c') = mul a c ^^^ mul a c' :=
  mulAux_xor 8 a c c'

/-- The word with byte `x` in row `j` and zeros in the other rows. -/
def single (j : Fin 4) (x : UInt8) : Word :=
  Vector.ofFn fun r => if r = j then x else 0

theorem single_xor (j : Fin 4) (x y : UInt8) :
    single j (x ^^^ y) = xorWord (single j x) (single j y) := by
  ext r hr
  simp only [single, xorWord, Vector.getElem_ofFn, Vector.getElem_zipWith]
  split <;> simp

theorem eq_xor_singles (b : Word) :
    b = xorWord (xorWord (xorWord (single 0 b[0]) (single 1 b[1])) (single 2 b[2]))
      (single 3 b[3]) := by
  ext r hr
  simp only [single, xorWord, Vector.getElem_ofFn, Vector.getElem_zipWith]
  match r, hr with
  | 0, _ | 1, _ | 2, _ | 3, _ => simp

theorem mulWord_xor (a u v : Word) :
    mulWord a (xorWord u v) = xorWord (mulWord a u) (mulWord a v) := by
  ext r hr
  simp only [mulWord, xorWord, Vector.getElem_zipWith, mul_xor]
  match r, hr with
  | 0, _ | 1, _ | 2, _ | 3, _ =>
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    ac_rfl

/-- The eight one-bit bytes. -/
def bits : List UInt8 := [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80]

/-- A byte is the sum of its bits. -/
theorem eq_xor_bits (x : UInt8) :
    x = (x &&& 0x01) ^^^ (x &&& 0x02) ^^^ (x &&& 0x04) ^^^ (x &&& 0x08) ^^^
      (x &&& 0x10) ^^^ (x &&& 0x20) ^^^ (x &&& 0x40) ^^^ (x &&& 0x80) := by
  have := forall_of_all (p := fun x => x == (x &&& 0x01) ^^^ (x &&& 0x02) ^^^ (x &&& 0x04) ^^^
    (x &&& 0x08) ^^^ (x &&& 0x10) ^^^ (x &&& 0x20) ^^^ (x &&& 0x40) ^^^ (x &&& 0x80))
    (by decide +kernel) x
  simpa using this

/-- Each bit of a byte is clear or set. -/
theorem and_bit (x : UInt8) {m : UInt8} (hm : m ∈ bits) : x &&& m = 0 ∨ x &&& m = m := by
  have := forall_of_all (p := fun x => bits.all fun m => x &&& m == 0 || x &&& m == m)
    (by decide +kernel) x
  simpa using List.all_eq_true.mp this m hm

/-- Two additive maps from bytes to words that agree on zero and on the bits agree everywhere. -/
theorem eq_of_additive {f g : UInt8 → Word}
    (hf : ∀ x y, f (x ^^^ y) = xorWord (f x) (f y)) (hg : ∀ x y, g (x ^^^ y) = xorWord (g x) (g y))
    (h0 : f 0 = g 0) (hbits : ∀ m ∈ bits, f m = g m) (x : UInt8) : f x = g x := by
  -- On a bit `m`, the piece `x &&& m` is zero or `m`.
  have piece (m : UInt8) (hm : m ∈ bits) : f (x &&& m) = g (x &&& m) := by
    rcases and_bit x hm with h | h <;> rw [h]
    · exact h0
    · exact hbits m hm
  rw [eq_xor_bits x]
  simp only [hf, hg]
  simp only [bits, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at piece
  obtain ⟨p1, p2, p4, p8, p16, p32, p64, p128⟩ := piece
  rw [p1, p2, p4, p8, p16, p32, p64, p128]

/-! ## The inverse of MIXCOLUMNS -/

/-- The INVMIXCOLUMNS matrix undoes the MIXCOLUMNS matrix on every column.

Both are additive, so the kernel checks zero and the 32 one-bit columns. -/
theorem mulWord_inverse (b : Word) :
    mulWord #v[0x0e, 0x09, 0x0d, 0x0b] (mulWord #v[0x02, 0x01, 0x01, 0x03] b) = b := by
  -- The composite is additive, as each matrix is.
  have add (j : Fin 4) (x y : UInt8) :
      mulWord #v[0x0e, 0x09, 0x0d, 0x0b] (mulWord #v[0x02, 0x01, 0x01, 0x03] (single j (x ^^^ y))) =
        xorWord
          (mulWord #v[0x0e, 0x09, 0x0d, 0x0b] (mulWord #v[0x02, 0x01, 0x01, 0x03] (single j x)))
          (mulWord #v[0x0e, 0x09, 0x0d, 0x0b] (mulWord #v[0x02, 0x01, 0x01, 0x03] (single j y))) :=
    by
    rw [single_xor, mulWord_xor, mulWord_xor]
  -- On each row, the composite fixes zero and the eight bits.
  have row (j : Fin 4) (x : UInt8) :
      mulWord #v[0x0e, 0x09, 0x0d, 0x0b] (mulWord #v[0x02, 0x01, 0x01, 0x03] (single j x)) =
        single j x :=
    eq_of_additive
      (f := fun x =>
        mulWord #v[0x0e, 0x09, 0x0d, 0x0b] (mulWord #v[0x02, 0x01, 0x01, 0x03] (single j x)))
      (g := single j) (add j) (single_xor j) (by revert j; decide +kernel)
      (by revert j; decide +kernel) x
  -- A column is the sum of its four rows.
  rw [eq_xor_singles b]
  simp only [mulWord_xor, row]

theorem getElem_mixColumnsWith (a : Word) (s : Block) (i : Nat) (hi : i < 16) :
    (mixColumnsWith a s)[i] = (mulWord a (column s ⟨i / 4, by omega⟩))[i % 4]'(by omega) := by
  simp [mixColumnsWith]

theorem column_mixColumnsWith (a : Word) (s : Block) (c : Fin 4) :
    column (mixColumnsWith a s) c = mulWord a (column s c) := by
  ext r hr
  simp only [column, Vector.getElem_ofFn, getElem_mixColumnsWith]
  -- Index `r + 4c` lies in column `c`, at row `r`.
  have hc : (r + 4 * c.val) / 4 = c.val := by omega
  have hr' : (r + 4 * c.val) % 4 = r := by omega
  simp only [hc, hr']

theorem invMixColumns_mixColumns (s : Block) : invMixColumns (mixColumns s) = s := by
  ext i hi
  rw [invMixColumns, mixColumns, getElem_mixColumnsWith, column_mixColumnsWith, mulWord_inverse]
  simp only [column, Vector.getElem_ofFn]
  congr 1
  omega

/-! ## The other inverses -/

theorem invShiftRows_shiftRows (s : Block) : invShiftRows (shiftRows s) = s := by
  ext i hi
  simp only [invShiftRows, shiftRows, Vector.getElem_ofFn]
  -- Row `r` moves left by `r`, then right by `r`.
  congr 1
  omega

theorem invSubBytes_subBytes (s : Block) : invSubBytes (subBytes s) = s := by
  ext i hi
  simp [invSubBytes, subBytes]

/-- ADDROUNDKEY is its own inverse, as FIPS 197 §5.3.4 states. -/
theorem addRoundKey_addRoundKey (s k : Block) : addRoundKey (addRoundKey s k) k = s := by
  ext i hi
  simp [addRoundKey, UInt8.xor_assoc]

/-! ## The inverse cipher

INVCIPHER runs the inverse steps in the reverse order, but it groups them differently.

A middle round of the cipher ends with ADDROUNDKEY.

A middle round of the inverse cipher ends with INVMIXCOLUMNS.

So the proof moves INVSHIFTROWS and INVSUBBYTES from the start of each inverse round to the end. -/

/-- A fold, then a fold of left inverses over the reversed list, gives back the start. -/
theorem foldl_reverse_foldl {α β : Type} (f g : α → β → α) (hfg : ∀ s b, g (f s b) b = s)
    (l : List β) (s : α) : l.reverse.foldl g (l.foldl f s) = s := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih => simp [ih, hfg]

/-- A step `p` done before each round of a fold can move after each round instead. -/
theorem foldl_rotate {α β : Type} (p : α → α) (h : α → β → α) (l : List β) (s : α) :
    p (l.foldl (fun t b => h (p t) b) s) = l.foldl (fun t b => p (h t b)) (p s) := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih => exact ih _

/-- INVCIPHER inverts CIPHER, for every number of rounds and every key schedule. -/
theorem invCipher_cipher (Nr : Nat) (w : Vector Word (4 * (Nr + 1))) (x : Block) :
    invCipher Nr w (cipher Nr w x) = x := by
  -- An inverse round is INVSHIFTROWS and INVSUBBYTES, then ADDROUNDKEY and INVMIXCOLUMNS.
  have split (s k : Block) :
      invRound s k = invMixColumns (addRoundKey (invSubBytes (invShiftRows s)) k) := rfl
  simp only [cipher, invCipher, addRoundKey_addRoundKey, split]
  have rotate := foldl_rotate (fun s => invSubBytes (invShiftRows s))
    (fun t (r : { round // round ≤ Nr }) =>
      invMixColumns (addRoundKey t (roundKey w r.val r.property)))
    (middleRounds Nr).reverse
  simp only [rotate]
  -- After the move, each step undoes one middle round of the cipher.
  rw [invShiftRows_shiftRows, invSubBytes_subBytes,
    foldl_reverse_foldl _ _ (fun s r => by
      simp [round, addRoundKey_addRoundKey, invMixColumns_mixColumns, invShiftRows_shiftRows,
        invSubBytes_subBytes]),
    addRoundKey_addRoundKey]

/-- The inverse cipher of a key undoes the cipher of the same key, for AES-128 and AES-256. -/
theorem ciphInv_ciph (k : KeySize) (key : Key k) (x : Block) : ciphInv k key (ciph k key x) = x :=
  invCipher_cipher _ _ x

/-! ## The key expansion

The code builds the key schedule in an array and reads it back with a default for a missing word.

The two theorems below state Algorithm 2 on the schedule itself, so the default plays no part. -/

/-- The array of the key expansion after the first `m` passes of its second loop. -/
private def schedule (Nk : Nat) (key : Vector UInt8 (4 * Nk)) (m : Nat) : Array Word :=
  (List.range' Nk m).foldl
    (fun w i => w.push (nextWord Nk i (w.getD (i - 1) default) (w.getD (i - Nk) default)))
    (Array.ofFn fun i : Fin Nk => Vector.ofFn fun j : Fin 4 => key[4 * i.val + j.val]'(by omega))

private theorem keyExpansion_eq_schedule (Nk Nr : Nat) (key : Vector UInt8 (4 * Nk)) :
    keyExpansion Nk Nr key =
      Vector.ofFn fun i => (schedule Nk key (4 * (Nr + 1) - Nk)).getD i.val default :=
  rfl

private theorem schedule_succ (Nk : Nat) (key : Vector UInt8 (4 * Nk)) (m : Nat) :
    schedule Nk key (m + 1) =
      (schedule Nk key m).push (nextWord Nk (Nk + m)
        ((schedule Nk key m).getD (Nk + m - 1) default) ((schedule Nk key m).getD m default)) := by
  simp only [schedule, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
    Nat.one_mul, Nat.add_sub_cancel_left]

private theorem size_schedule (Nk : Nat) (key : Vector UInt8 (4 * Nk)) (m : Nat) :
    (schedule Nk key m).size = Nk + m := by
  induction m with
  | zero => simp [schedule]
  | succ m ih => rw [schedule_succ, Array.size_push, ih, Nat.add_assoc]

-- Later passes only push, so they keep every word already in the array.
private theorem getElem?_schedule_add (Nk : Nat) (key : Vector UInt8 (4 * Nk)) (m k i : Nat)
    (hi : i < Nk + m) : (schedule Nk key (m + k))[i]? = (schedule Nk key m)[i]? := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, schedule_succ, Array.getElem?_push, size_schedule,
      ite_eq_right_iff.mpr (fun h => by omega), ih]

private theorem getElem?_schedule_of_lt (Nk : Nat) (key : Vector UInt8 (4 * Nk)) (m i : Nat)
    (hi : i < Nk) :
    (schedule Nk key m)[i]? =
      some (Vector.ofFn fun j : Fin 4 => key[4 * i + j.val]'(by omega)) := by
  rw [show m = 0 + m by omega, getElem?_schedule_add Nk key 0 m i (by omega)]
  simp [schedule, hi]

private theorem getElem?_schedule_of_le (Nk : Nat) (key : Vector UInt8 (4 * Nk)) (hNk : 0 < Nk)
    (m i : Nat) (hk : Nk ≤ i) (hi : i < Nk + m) :
    (schedule Nk key m)[i]? = some (nextWord Nk i ((schedule Nk key m)[i - 1]?.getD default)
      ((schedule Nk key m)[i - Nk]?.getD default)) := by
  obtain ⟨n, rfl⟩ : ∃ n, i = Nk + n := ⟨i - Nk, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = n + 1 + k := ⟨m - (n + 1), by omega⟩
  rw [getElem?_schedule_add Nk key (n + 1) k _ (by omega),
    getElem?_schedule_add Nk key (n + 1) k _ (by omega),
    getElem?_schedule_add Nk key (n + 1) k _ (by omega), schedule_succ]
  simp only [Array.getElem?_push, size_schedule, Array.getD_eq_getD_getElem?,
    show Nk + n - 1 ≠ Nk + n by omega, show n ≠ Nk + n by omega,
    Nat.add_sub_cancel_left, ↓reduceIte]

/-- Word `i < Nk` of the schedule is word `i` of the key, as lines 2 to 6 of Algorithm 2 state.

Algorithm 2 is in FIPS 197 §5.2, and word `i` of the key is its bytes `4i` to `4i + 3`. -/
theorem getElem_keyExpansion_of_lt (Nk Nr : Nat) (key : Vector UInt8 (4 * Nk)) (i : Nat)
    (hi : i < 4 * (Nr + 1)) (hk : i < Nk) :
    (keyExpansion Nk Nr key)[i] = Vector.ofFn fun j : Fin 4 => key[4 * i + j.val]'(by omega) := by
  rw [keyExpansion_eq_schedule, Vector.getElem_ofFn, Array.getD_eq_getD_getElem?,
    getElem?_schedule_of_lt Nk key _ i hk, Option.getD_some]

/-- Each word `i >= Nk` comes from words `i - 1` and `i - Nk`, by lines 8 to 14 of Algorithm 2.

Both are words of the schedule itself, so neither read of the code returns the default.

A key of no words has no word `i - Nk` below `i`, so the key needs at least one word. -/
theorem getElem_keyExpansion_of_le (Nk Nr : Nat) (key : Vector UInt8 (4 * Nk)) (hNk : 0 < Nk)
    (i : Nat) (hi : i < 4 * (Nr + 1)) (hk : Nk ≤ i) :
    (keyExpansion Nk Nr key)[i] =
      nextWord Nk i (keyExpansion Nk Nr key)[i - 1] (keyExpansion Nk Nr key)[i - Nk] := by
  simp only [keyExpansion_eq_schedule, Vector.getElem_ofFn, Array.getD_eq_getD_getElem?]
  rw [getElem?_schedule_of_le Nk key hNk _ i hk (by omega), Option.getD_some]

/-! ## The model

The model follows FIPS 197 over the state `s[r, c]` of §3.4, kept as a function of `r` and `c`.

It multiplies bytes as polynomials reduced modulo `m(x)` (§4.2), with no XTIMES.

Its S-box is the inverse `b^254` of (4.11), then the affine transformation (5.3), with no table.

Its key schedule is the recurrence of Algorithm 2, defined for every index.

It shares with the code only the type of key sizes and the vector types of keys and blocks. -/

namespace Spec

/-- The product of two polynomials over GF(2), as in step 1 of FIPS 197 §4.2.

A natural number holds a polynomial, with bit `i` the coefficient of `x^i`, as (4.1) reads a byte.

The product adds `a x^i` for each set bit `i < n` of `b`, and adding is XOR (§4.1). -/
def polyMul : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n + 1, a, b => a * (b % 2) ^^^ polyMul n (2 * a) (b / 2)

/-- The remainder of `p` modulo `m(x) = x^8 + x^4 + x^3 + x + 1` of (4.3).

It holds for `p` of degree below `n + 8`.

Long division clears the coefficients of `x^(n + 7)` down to `x^8`.

It clears `x^(k + 8)` by adding `x^k m(x)`, whose bits are `{11b}` shifted left by `k`. -/
def polyMod : Nat → Nat → Nat
  | 0, p => p
  | k + 1, p => polyMod k (p ^^^ 0x11b * 2 ^ k * (p / 2 ^ (k + 8) % 2))

/-- The product `b • c` of FIPS 197 §4.2 (4.4): `b(x) c(x) mod m(x)`.

The product of two bytes has degree at most 14, below `7 + 8`. -/
def mul (b c : UInt8) : UInt8 :=
  (polyMod 7 (polyMul 8 b.toNat c.toNat)).toUInt8

/-- The inverse `b^-1 = b^254` of FIPS 197 §4.4 (4.11).

Square-and-multiply runs over the bits `11111110` of 254, from the top. -/
def inv (b : UInt8) : UInt8 :=
  [true, true, true, true, true, true, true, false].foldl
    (fun acc bit => if bit then mul (mul acc acc) b else mul acc acc) 1

/-- The affine transformation of FIPS 197 §5.1.1 (5.3), with `c = {63}` and indices mod 8. -/
def affine (b : UInt8) : UInt8 :=
  let bit (i : Nat) : Bool := b.toNat.testBit (i % 8)
  let c : Nat := 0x63
  ((List.range 8).foldl (fun acc i =>
    if bit i ^^ bit (i + 4) ^^ bit (i + 5) ^^ bit (i + 6) ^^ bit (i + 7) ^^ c.testBit i then
      acc + 2 ^ i
    else acc) 0).toUInt8

/-- SBOX of FIPS 197 §5.1.1: the byte `b~` of (5.2), then the affine transformation (5.3). -/
def sbox (b : UInt8) : UInt8 :=
  affine (if b = 0 then 0 else inv b)

/-- The state of FIPS 197 §3.4, with byte `s[r, c]` at `s r c`. -/
abbrev State := Fin 4 → Fin 4 → UInt8

/-- A word `[a_0, a_1, a_2, a_3]` of FIPS 197 §3.5, with byte `a_r` at `a r`. -/
abbrev Word := Fin 4 → UInt8

/-- SUBBYTES of FIPS 197 §5.1.1: the S-box on each byte of the state. -/
def subBytes (s : State) : State :=
  fun r c => sbox (s r c)

/-- SHIFTROWS of FIPS 197 §5.1.2 (5.5): `s'[r, c] = s[r, (c + r) mod 4]`.

The sum of two `Fin 4` values is taken mod 4. -/
def shiftRows (s : State) : State :=
  fun r c => s r (c + r)

/-- MIXCOLUMNS of FIPS 197 §5.1.3, byte by byte as (5.8) writes it. -/
def mixColumns (s : State) : State :=
  fun r c =>
    match r with
    | 0 => mul 0x02 (s 0 c) ^^^ mul 0x03 (s 1 c) ^^^ s 2 c ^^^ s 3 c
    | 1 => s 0 c ^^^ mul 0x02 (s 1 c) ^^^ mul 0x03 (s 2 c) ^^^ s 3 c
    | 2 => s 0 c ^^^ s 1 c ^^^ mul 0x02 (s 2 c) ^^^ mul 0x03 (s 3 c)
    | 3 => mul 0x03 (s 0 c) ^^^ s 1 c ^^^ s 2 c ^^^ mul 0x02 (s 3 c)

/-- ADDROUNDKEY of FIPS 197 §5.1.4 (5.9): column `c` XOR the word `w[4 round + c]`. -/
def addRoundKey (s : State) (w : Nat → Word) (round : Nat) : State :=
  fun r c => s r c ^^^ w (4 * round + c.val) r

/-- ROTWORD of FIPS 197 §5.2 (5.10): `[a_0, a_1, a_2, a_3]` to `[a_1, a_2, a_3, a_0]`. -/
def rotWord (a : Word) : Word :=
  fun r => a (r + 1)

/-- SUBWORD of FIPS 197 §5.2 (5.11): the S-box on each byte of a word. -/
def subWord (a : Word) : Word :=
  fun r => sbox (a r)

/-- The power `x^n` in GF(2^8), the product of `n` factors `x = {02}`. -/
def xPow (n : Nat) : UInt8 :=
  Nat.repeat (fun b => mul b 0x02) n 1

/-- The round constant `Rcon[j]` of FIPS 197 §5.2: `[x^(j - 1), {00}, {00}, {00}]`. -/
def rcon (j : Nat) : Word :=
  fun r => if r = 0 then xPow (j - 1) else 0

/-- Word `w[i]` of KEYEXPANSION of FIPS 197 §5.2, Algorithm 2, for a key of `Nk` words.

Algorithm 2 computes the words `i <= 4 Nr + 3`, and this function is defined for every `i`.

It needs at least one key word, so that `i - Nk` is below `i`. -/
def keyExpansion (Nk : Nat) (hNk : 0 < Nk) (key : Vector UInt8 (4 * Nk)) (i : Nat) : Word :=
  if h : i < Nk then
    -- Line 4: word `i` is bytes `4i` to `4i + 3` of the key.
    fun r => key[4 * i + r.val]'(by omega)
  else
    -- Lines 8 to 13.
    let temp := keyExpansion Nk hNk key (i - 1)
    let temp :=
      if i % Nk = 0 then fun r => subWord (rotWord temp) r ^^^ rcon (i / Nk) r
      else if Nk > 6 ∧ i % Nk = 4 then subWord temp
      else temp
    -- Line 14.
    fun r => keyExpansion Nk hNk key (i - Nk) r ^^^ temp r
termination_by i
decreasing_by all_goals omega

/-- CIPHER of FIPS 197 §5.1, Algorithm 1, over `Nr` rounds with key schedule `w`. -/
def cipher (Nr : Nat) (w : Nat → Word) (input : Vector UInt8 16) : Vector UInt8 16 :=
  -- Line 2: `s[r, c] = in[r + 4c]`, (3.6).
  let state : State := fun r c => input[r.val + 4 * c.val]
  -- Line 3.
  let state := addRoundKey state w 0
  -- Lines 4 to 9.
  let state := (List.range' 1 (Nr - 1)).foldl
    (fun state round => addRoundKey (mixColumns (shiftRows (subBytes state))) w round) state
  -- Lines 10 to 12.
  let state := addRoundKey (shiftRows (subBytes state)) w Nr
  -- Line 13: `out[r + 4c] = s[r, c]`, (3.7).
  Vector.ofFn fun i => state ⟨i.val % 4, by omega⟩ ⟨i.val / 4, by omega⟩

/-- AES-128 and AES-256 of FIPS 197 (5.1), with `Nk` and `Nr` of Table 3. -/
def ciph : (k : KeySize) → Key k → Block → Block
  | .aes128, key, input => cipher 10 (keyExpansion 4 (by decide) key) input
  | .aes256, key, input => cipher 14 (keyExpansion 8 (by decide) key) input

end Spec

/-! ## Agreement with the model

The kernel checks the byte functions on all 256 bytes.

The state, the words and the rounds then follow by rewriting, one step of the code at a time. -/

/-- Table 4 is the S-box of the model, entry by entry. -/
theorem sbox_eq_spec (b : UInt8) : sbox b = Spec.sbox b := by
  simpa using forall_of_all (p := fun b => sbox b == Spec.sbox b) (by decide +kernel) b

/-- Multiplication by `{01}` leaves a byte unchanged. -/
theorem one_mul (c : UInt8) : mul 0x01 c = c := by
  simpa using forall_of_all (p := fun c => mul 0x01 c == c) (by decide +kernel) c

/-- Multiplication by `{02}` is the model's. -/
theorem two_mul_eq_spec (c : UInt8) : mul 0x02 c = Spec.mul 0x02 c := by
  simpa using forall_of_all (p := fun c => mul 0x02 c == Spec.mul 0x02 c) (by decide +kernel) c

/-- Multiplication by `{03}` is the model's. -/
theorem three_mul_eq_spec (c : UInt8) : mul 0x03 c = Spec.mul 0x03 c := by
  simpa using forall_of_all (p := fun c => mul 0x03 c == Spec.mul 0x03 c) (by decide +kernel) c

/-- XTIMES is the model's multiplication by `{02}`, as (4.5) states. -/
theorem xtimes_eq_spec (b : UInt8) : xtimes b = Spec.mul b 0x02 := by
  simpa using forall_of_all (p := fun b => xtimes b == Spec.mul b 0x02) (by decide +kernel) b

/-- The model's `b^254` is the inverse of (4.10): `b • b^-1 = {01}` for `b ≠ {00}`. -/
theorem Spec.mul_inv (b : UInt8) (h : b ≠ 0) : Spec.mul b (Spec.inv b) = 1 := by
  have all := forall_of_all (p := fun b => b == 0 || Spec.mul b (Spec.inv b) == 1)
    (by decide +kernel) b
  simpa [h] using all

/-- The state of a block: byte `s[r, c]` at index `r + 4c`. -/
def toState (s : Block) : Spec.State :=
  fun r c => s[r.val + 4 * c.val]

/-- The bytes of a word. -/
def toWord (a : Word) : Spec.Word :=
  fun r => a[r.val]

theorem toState_subBytes (s : Block) : toState (subBytes s) = Spec.subBytes (toState s) := by
  funext r c
  simp [toState, subBytes, Spec.subBytes, sbox_eq_spec]

theorem toState_shiftRows (s : Block) : toState (shiftRows s) = Spec.shiftRows (toState s) := by
  funext r c
  simp only [toState, shiftRows, Spec.shiftRows, Vector.getElem_ofFn, Fin.val_add]
  congr 1
  omega

theorem toState_mixColumns (s : Block) :
    toState (mixColumns s) = Spec.mixColumns (toState s) := by
  funext r c
  simp only [toState, mixColumns, getElem_mixColumnsWith]
  have hc : (r.val + 4 * c.val) / 4 = c.val := by omega
  have hr : (r.val + 4 * c.val) % 4 = r.val := by omega
  simp only [hc, hr]
  match r with
  | 0 | 1 | 2 | 3 =>
    simp [Spec.mixColumns, mulWord, column, toState, one_mul, two_mul_eq_spec,
      three_mul_eq_spec, show ((3 : Fin 4) : Nat) = 3 from rfl]

theorem toState_addRoundKey (s : Block) {Nr : Nat} (w : Vector Word (4 * (Nr + 1)))
    (W : Nat → Spec.Word) (hw : ∀ i (hi : i < 4 * (Nr + 1)), toWord w[i] = W i) (round : Nat)
    (h : round ≤ Nr) :
    toState (addRoundKey s (roundKey w round h)) = Spec.addRoundKey (toState s) W round := by
  funext r c
  simp only [toState, addRoundKey, roundKey, Spec.addRoundKey, Vector.getElem_zipWith,
    Vector.getElem_ofFn, ← hw _ (by omega : 4 * round + c.val < 4 * (Nr + 1)), toWord]
  have hc : (r.val + 4 * c.val) / 4 = c.val := by omega
  have hr : (r.val + 4 * c.val) % 4 = r.val := by omega
  simp only [hc, hr]

/-! ## The key schedule -/

theorem toWord_xorWord (a b : Word) :
    toWord (xorWord a b) = fun r => toWord a r ^^^ toWord b r := by
  funext r
  simp [toWord, xorWord]

theorem toWord_subWord (a : Word) : toWord (subWord a) = Spec.subWord (toWord a) := by
  funext r
  simp [toWord, subWord, Spec.subWord, sbox_eq_spec]

theorem toWord_rotWord (a : Word) : toWord (rotWord a) = Spec.rotWord (toWord a) := by
  funext r
  match r with
  | 0 | 1 | 2 | 3 => simp [toWord, rotWord, Spec.rotWord, show ((3 : Fin 4) : Nat) = 3 from rfl]

theorem repeat_xtimes_eq_xPow (n : Nat) : Nat.repeat xtimes n 1 = Spec.xPow n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.repeat, Spec.xPow] at ih ⊢; rw [ih, xtimes_eq_spec]

theorem toWord_rcon (j : Nat) : toWord (rcon j) = Spec.rcon j := by
  funext r
  match r with
  | 0 | 1 | 2 | 3 =>
    simp [toWord, rcon, Spec.rcon, repeat_xtimes_eq_xPow, show ((3 : Fin 4) : Nat) = 3 from rfl]

theorem toWord_nextWord (Nk i : Nat) (prev back : Word) :
    toWord (nextWord Nk i prev back) = fun r => toWord back r ^^^
      (if i % Nk = 0 then
          fun r => Spec.subWord (Spec.rotWord (toWord prev)) r ^^^ Spec.rcon (i / Nk) r
        else if Nk > 6 ∧ i % Nk = 4 then Spec.subWord (toWord prev)
        else toWord prev) r := by
  by_cases h1 : i % Nk = 0 <;> by_cases h2 : Nk > 6 ∧ i % Nk = 4 <;>
    simp [nextWord, h1, h2, toWord_xorWord, toWord_subWord, toWord_rotWord, toWord_rcon]

/-- Each word of the key schedule is the word of the model, for every key of `Nk ≥ 1` words. -/
theorem toWord_keyExpansion (Nk Nr : Nat) (hNk : 0 < Nk) (key : Vector UInt8 (4 * Nk))
    (i : Nat) (hi : i < 4 * (Nr + 1)) :
    toWord (keyExpansion Nk Nr key)[i] = Spec.keyExpansion Nk hNk key i := by
  induction i using Nat.strongRecOn with
  | _ i ih =>
  rw [Spec.keyExpansion]
  by_cases hk : i < Nk
  · rw [getElem_keyExpansion_of_lt Nk Nr key i hi hk]
    funext r
    simp [toWord, hk]
  · rw [getElem_keyExpansion_of_le Nk Nr key hNk i hi (by omega), toWord_nextWord,
      ih (i - 1) (by omega) (by omega), ih (i - Nk) (by omega) (by omega)]
    simp only [hk, ↓reduceDIte]

/-! ## The cipher -/

theorem toState_round (s : Block) {Nr : Nat} (w : Vector Word (4 * (Nr + 1)))
    (W : Nat → Spec.Word) (hw : ∀ i (hi : i < 4 * (Nr + 1)), toWord w[i] = W i) (r : Nat)
    (h : r ≤ Nr) :
    toState (round s (roundKey w r h)) =
      Spec.addRoundKey (Spec.mixColumns (Spec.shiftRows (Spec.subBytes (toState s)))) W r := by
  rw [round, toState_addRoundKey _ w W hw, toState_mixColumns, toState_shiftRows,
    toState_subBytes]

theorem toState_foldl_round {Nr : Nat} (w : Vector Word (4 * (Nr + 1))) (W : Nat → Spec.Word)
    (hw : ∀ i (hi : i < 4 * (Nr + 1)), toWord w[i] = W i) (l : List { r : Nat // r ≤ Nr })
    (s : Block) :
    toState (l.foldl (fun s r => round s (roundKey w r.val r.property)) s) =
      (l.map Subtype.val).foldl
        (fun state r =>
          Spec.addRoundKey (Spec.mixColumns (Spec.shiftRows (Spec.subBytes state))) W r)
        (toState s) := by
  induction l generalizing s with
  | nil => rfl
  | cons r l ih => simp only [List.foldl_cons, List.map_cons, ih, toState_round _ w W hw]

theorem map_val_middleRounds (Nr : Nat) :
    (middleRounds Nr).map Subtype.val = List.range' 1 (Nr - 1) := by
  simp [middleRounds]

/-- A block is the output of its own state, `out[r + 4c] = s[r, c]`. -/
theorem eq_ofFn_toState (b : Block) :
    b = Vector.ofFn fun i => toState b ⟨i.val % 4, by omega⟩ ⟨i.val / 4, by omega⟩ := by
  ext i hi
  simp only [toState, Vector.getElem_ofFn]
  congr 1
  omega

/-- CIPHER is the model's CIPHER, for every number of rounds and every block.

It holds for every key schedule whose words are the model's words of the same index. -/
theorem cipher_eq_spec (Nr : Nat) (w : Vector Word (4 * (Nr + 1))) (W : Nat → Spec.Word)
    (hw : ∀ i (hi : i < 4 * (Nr + 1)), toWord w[i] = W i) (x : Block) :
    cipher Nr w x = Spec.cipher Nr W x := by
  rw [eq_ofFn_toState (cipher Nr w x)]
  simp only [cipher, Spec.cipher, toState_addRoundKey _ w W hw, toState_shiftRows,
    toState_subBytes, toState_foldl_round w W hw, map_val_middleRounds]
  rfl

/-- AES-128 and AES-256 are the model's, for every key and every block. -/
theorem ciph_eq_spec (k : KeySize) (key : Key k) (x : Block) :
    ciph k key x = Spec.ciph k key x := by
  cases k
  · exact cipher_eq_spec _ _ _ (toWord_keyExpansion 4 10 (by decide) key) x
  · exact cipher_eq_spec _ _ _ (toWord_keyExpansion 8 14 (by decide) key) x

/-- The inverse cipher undoes the model's cipher, for AES-128 and AES-256. -/
theorem ciphInv_spec_ciph (k : KeySize) (key : Key k) (x : Block) :
    ciphInv k key (Spec.ciph k key x) = x := by
  rw [← ciph_eq_spec, ciphInv_ciph]

end EthLib.Cryptography.Aes
