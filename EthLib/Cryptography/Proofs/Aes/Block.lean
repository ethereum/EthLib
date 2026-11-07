module

public import EthLib.Cryptography.Aes.Block

/-!
# Proofs: `Aes.Block`

The S-box table is the S-box that FIPS 197 §5.1.1 defines, and the inverse table inverts it.

The round constants are the ten values of FIPS 197 Table 5.

The inverse cipher inverts the cipher for every key schedule, so for every key.

Each word of the key schedule is a key word or follows the recurrence of FIPS 197 §5.2, Algorithm 2.

That recurrence needs a key of at least one word.
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

end EthLib.Cryptography.Aes
