module

public import EthLib.Cryptography.Aes.Ctr
public import EthLib.Base.Proofs.BigEndian

/-!
# Proofs: `Aes.Ctr`

CTR decryption returns the plaintext, for every cipher, counter and message.

The output has the length of the input.

With `m <= 128`, the standard increment gives `2^m` distinct counters before it repeats the first.
-/

@[expose] public section

namespace EthLib.Cryptography.Aes

/-! ## Blocks as integers -/

/-- A block is worth less than `2^128`. -/
theorem blockToNat_lt (A : Block) : blockToNat A < 2 ^ 128 := by
  have h := Base.bytesToNat_lt A.toList
  rw [Vector.length_toList] at h
  exact lt_of_lt_of_eq h (by decide)

/-- Two blocks with the same integer are equal. -/
theorem blockToNat_injective : Function.Injective blockToNat := by
  intro A B h
  exact Vector.toList_inj.mp (Base.bytesToNat_inj (by simp) h)

/-- The bytes `z / 256^(n - 1 - i)`, for `i < n`, are `z` written on `n` bytes. -/
private theorem ofFn_toUInt8_eq_natToBytes (n z : Nat) :
    List.ofFn (fun i : Fin n => (z / 256 ^ (n - 1 - i.val)).toUInt8) = Base.natToBytes n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    -- The last byte is `z mod 256`, and the bytes before it write `z / 256`.
    rw [List.ofFn_succ_last, Base.natToBytes_succ, ← ih (z / 256)]
    congr 1
    · congr 1
      funext i
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
      congr 3
      simp only [Fin.val_castSucc]
      omega
    · simp only [Fin.val_last, List.cons.injEq, and_true]
      apply UInt8.toNat_inj.mp
      simp [Nat.toUInt8_eq]

/-- An integer below `2^128` survives the round trip through a block. -/
theorem blockToNat_blockOfNat {z : Nat} (hz : z < 2 ^ 128) : blockToNat (blockOfNat z) = z := by
  have h := ofFn_toUInt8_eq_natToBytes 16 z
  simp only [show ∀ i : Fin 16, 16 - 1 - i.val = 15 - i.val from fun _ => rfl] at h
  rw [blockToNat, blockOfNat, Vector.toList_ofFn, h]
  exact Base.bytesToNat_natToBytes_of_lt (lt_of_lt_of_eq hz (by decide))

/-! ## The mode -/

/-- XOR with a key stream twice gives back the data, when the stream is long enough. -/
theorem zipWith_xor_xor (a k : List UInt8) (h : a.length ≤ k.length) :
    List.zipWith (· ^^^ ·) (List.zipWith (· ^^^ ·) a k) k = a := by
  induction a generalizing k with
  | nil => simp
  | cons x a ih =>
    cases k with
    | nil => simp at h
    | cons y k =>
      simp only [List.zipWith_cons_cons, UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero]
      rw [ih k (by simpa using h)]

/-- The output of the loop is the output so far, then the output of the loop from nothing. -/
theorem xorKeystream.go_toList (ciph : Block → Block) (m n : Nat) (T : Block)
    (data : List UInt8) (out : Array UInt8) :
    (go ciph m n T data out).toList = out.toList ++ (go ciph m n T data #[]).toList := by
  induction n generalizing T data out with
  | zero => simp [go]
  | succ n ih => rw [go, go, ih, ih (out := #[] ++ _)]; simp

/-- No blocks give no output. -/
theorem xorKeystream_zero (ciph : Block → Block) (m : Nat) (T : Block) (data : List UInt8) :
    xorKeystream ciph m 0 T data = [] := rfl

/-- The first block of the output is the first block of data XOR the cipher of the counter.

The rest is the output of the next counter on the rest of the data. -/
theorem xorKeystream_succ (ciph : Block → Block) (m n : Nat) (T : Block) (data : List UInt8) :
    xorKeystream ciph m (n + 1) T data =
      List.zipWith (· ^^^ ·) (data.take 16) (ciph T).toList ++
        xorKeystream ciph m n (inc m T) (data.drop 16) := by
  rw [xorKeystream, xorKeystream.go, xorKeystream.go_toList, xorKeystream]
  simp

theorem xorKeystream_nil (ciph : Block → Block) (m n : Nat) (T : Block) :
    xorKeystream ciph m n T [] = [] := by
  induction n generalizing T with
  | zero => rfl
  | succ n ih => simp [xorKeystream_succ, ih]

/-- The output has the length of the data, when the blocks cover it. -/
theorem length_xorKeystream (ciph : Block → Block) (m n : Nat) (T : Block) (data : List UInt8)
    (h : data.length ≤ 16 * n) : (xorKeystream ciph m n T data).length = data.length := by
  induction n generalizing T data with
  | zero => simp_all [xorKeystream_zero]
  | succ n ih =>
    simp only [xorKeystream_succ, List.length_append, List.length_zipWith, List.length_take,
      Vector.length_toList]
    rw [ih _ _ (by simp; omega)]
    simp only [List.length_drop]
    omega

/-- Running the key stream twice gives back the data. -/
theorem xorKeystream_xorKeystream (ciph : Block → Block) (m n : Nat) (T : Block)
    (data : List UInt8) (h : data.length ≤ 16 * n) :
    xorKeystream ciph m n T (xorKeystream ciph m n T data) = data := by
  induction n generalizing T data with
  | zero => simp_all [xorKeystream_zero]
  | succ n ih =>
    -- The first block of the output is the XOR of the first block of the data.
    have first :
        (List.zipWith (· ^^^ ·) (data.take 16) (ciph T).toList).length = min data.length 16 := by
      simp [List.length_take]; omega
    by_cases full : 16 ≤ data.length
    · -- A full first block: the output splits after 16 bytes, at the same place.
      simp only [xorKeystream_succ]
      rw [List.take_left' (by rw [first]; omega), List.drop_left' (by rw [first]; omega),
        zipWith_xor_xor _ _ (by simp; omega), ih _ _ (by simp; omega), List.take_append_drop]
    · -- A partial last block: the rest of the data is empty.
      have rest : data.drop 16 = [] := List.drop_eq_nil_of_le (by omega)
      have short : data.take 16 = data := List.take_of_length_le (by omega)
      simp only [short] at first
      simp only [xorKeystream_succ, rest, short, xorKeystream_nil, List.append_nil]
      rw [List.take_of_length_le (by rw [first]; omega),
        List.drop_eq_nil_of_le (by rw [first]; omega),
        xorKeystream_nil, List.append_nil, zipWith_xor_xor _ _ (by simp; omega)]

/-- CTR keeps the length of the data. -/
theorem size_ctr (ciph : Block → Block) (m : Nat) (T : Block) (data : ByteArray) :
    (ctr ciph m T data).size = data.size := by
  simp only [ctr, ByteArray.size]
  simp only [List.size_toArray]
  rw [length_xorKeystream _ _ _ _ _ (by simp; omega)]
  simp

/-- CTR decryption of SP 800-38A §6.5 undoes CTR encryption with the same cipher and counters.

It holds for every forward cipher, so for AES under every key. -/
theorem ctr_ctr (ciph : Block → Block) (m : Nat) (T : Block) (data : ByteArray) :
    ctr ciph m T (ctr ciph m T data) = data := by
  apply ByteArray.ext
  -- The outer call cuts the output of the inner one into as many blocks as the data.
  show (xorKeystream ciph m (((ctr ciph m T data).size + 15) / 16) T
    (ctr ciph m T data).data.toList).toArray = data.data
  rw [size_ctr]
  simp only [ctr, List.toList_toArray]
  rw [xorKeystream_xorKeystream _ _ _ _ _ (by rw [Array.length_toList]; show data.size ≤ _; omega)]

/-- Iterating `k` times from `f a` is iterating `k + 1` times from `a`. -/
theorem repeat_apply_eq_repeat_succ {α : Type} (f : α → α) (k : Nat) (a : α) :
    Nat.repeat f k (f a) = Nat.repeat f (k + 1) a := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg f ih

/-- Block `j` of the output, counted from 0, is block `j` of the data XORed with the cipher.

The cipher takes the counter `T` incremented `j` times, as in SP 800-38A §6.5.

A block is 16 bytes, and a partial last block of the data gives a partial last block. -/
theorem xorKeystream_block (ciph : Block → Block) (m : Nat) {n j : Nat} (hj : j < n) (T : Block)
    (data : List UInt8) :
    ((xorKeystream ciph m n T data).drop (16 * j)).take 16
      = List.zipWith (· ^^^ ·) ((data.drop (16 * j)).take 16)
          (ciph (Nat.repeat (inc m) j T)).toList := by
  induction j generalizing n T data with
  | zero =>
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [xorKeystream_succ, Nat.mul_zero, List.drop_zero, List.drop_zero, Nat.repeat]
    by_cases full : 16 ≤ data.length
    · -- A full first block: the output keeps its first 16 bytes.
      rw [List.take_append_of_le_length (by simp; omega)]
      exact List.take_of_length_le (by simp; omega)
    · -- A partial first block: nothing of the data follows it.
      rw [List.drop_eq_nil_of_le (by omega), xorKeystream_nil, List.append_nil]
      exact List.take_of_length_le (by simp; omega)
  | succ j ih =>
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [xorKeystream_succ, ← repeat_apply_eq_repeat_succ]
    by_cases full : 16 ≤ data.length
    · -- The first output block has 16 bytes, so block `j + 1` is block `j` of the rest.
      have hfirst :
          (List.zipWith (· ^^^ ·) (data.take 16) (ciph T).toList).length = 16 := by simp; omega
      rw [show 16 * (j + 1) = 16 + 16 * j by omega, ← List.drop_drop, ← List.drop_drop,
        List.drop_left' hfirst]
      exact ih (by omega) (inc m T) (data.drop 16)
    · -- A short message has no block `j + 1`: both sides are empty.
      have hrest : data.drop 16 = [] := List.drop_eq_nil_of_le (by omega)
      rw [hrest, xorKeystream_nil, List.append_nil, List.drop_eq_nil_of_le (by simp; omega),
        List.drop_eq_nil_of_le (as := data) (by omega)]
      simp

/-- Block `j` of a CTR output, counted from 0, is block `j` of the data XORed with the cipher.

The cipher takes the initial counter incremented `j` times, for every block `j` of the data. -/
theorem ctr_block (ciph : Block → Block) (m : Nat) (T : Block) (data : ByteArray) {j : Nat}
    (hj : j < (data.size + 15) / 16) :
    (((ctr ciph m T data).data.toList).drop (16 * j)).take 16
      = List.zipWith (· ^^^ ·) ((data.data.toList.drop (16 * j)).take 16)
          (ciph (Nat.repeat (inc m) j T)).toList := by
  simp only [ctr, List.toList_toArray]
  exact xorKeystream_block ciph m hj T data.data.toList

/-! ## Distinct counters

SP 800-38A Appendix B.1: the standard increment gives distinct counters to `n <= 2^m` blocks.

Block `j` of a message, counted from 0, uses the first counter incremented `j` times. -/

/-- The bits of a block above `m`, with any `m` low bits, stay below `2^128`. -/
private theorem div_mul_add_lt {x m r : Nat} (hx : x < 2 ^ 128) (hm : m ≤ 128) (hr : r < 2 ^ m) :
    x / 2 ^ m * 2 ^ m + r < 2 ^ 128 := by
  have hsplit : 2 ^ 128 = 2 ^ (128 - m) * 2 ^ m := by rw [← Nat.pow_add, Nat.sub_add_cancel hm]
  -- The high part counts fewer than `2^(128 - m)` steps of `2^m`.
  have hq : x / 2 ^ m < 2 ^ (128 - m) :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hsplit]; exact hx)
  calc x / 2 ^ m * 2 ^ m + r < x / 2 ^ m * 2 ^ m + 2 ^ m := Nat.add_lt_add_left hr _
    _ = (x / 2 ^ m + 1) * 2 ^ m := by rw [Nat.succ_mul]
    _ ≤ 2 ^ (128 - m) * 2 ^ m := Nat.mul_le_mul_right _ hq
    _ = 2 ^ 128 := hsplit.symm

/-- After `k` increments, the low `m` bits grew by `k` modulo `2^m`, and the bits above stay. -/
theorem blockToNat_repeat_inc {m : Nat} (hm : m ≤ 128) (T : Block) (k : Nat) :
    blockToNat (Nat.repeat (inc m) k T)
      = blockToNat T / 2 ^ m * 2 ^ m + (blockToNat T % 2 ^ m + k) % 2 ^ m := by
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  induction k with
  | zero =>
    rw [Nat.repeat, Nat.add_zero, Nat.mod_mod, Nat.div_add_mod']
  | succ k ih =>
    rw [Nat.repeat, inc, ih]
    -- The low part is below `2^m`, so it is the remainder and the high part is the quotient.
    have hr : (blockToNat T % 2 ^ m + k) % 2 ^ m < 2 ^ m := Nat.mod_lt _ hpos
    have hdiv : (blockToNat T / 2 ^ m * 2 ^ m + (blockToNat T % 2 ^ m + k) % 2 ^ m) / 2 ^ m
        = blockToNat T / 2 ^ m := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hr, Nat.zero_add]
    have hmod : (blockToNat T / 2 ^ m * 2 ^ m + (blockToNat T % 2 ^ m + k) % 2 ^ m) % 2 ^ m
        = (blockToNat T % 2 ^ m + k) % 2 ^ m := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]
    have hnext : ((blockToNat T % 2 ^ m + k) % 2 ^ m + 1) % 2 ^ m
        = (blockToNat T % 2 ^ m + (k + 1)) % 2 ^ m := by
      rw [Nat.mod_add_mod, Nat.add_assoc]
    rw [hdiv, hmod, hnext,
      blockToNat_blockOfNat (div_mul_add_lt (blockToNat_lt T) hm (Nat.mod_lt _ hpos))]

/-- The counters `i` and `j` increments after `T` differ, for `i != j` below `2^m`.

These are the counters of SP 800-38A Appendix B.1 for a message of at most `2^m` blocks.

The keystream gives block `j` the counter of `j` increments. -/
theorem repeat_inc_injOn {m : Nat} (hm : m ≤ 128) (T : Block) {i j : Nat} (hi : i < 2 ^ m)
    (hj : j < 2 ^ m) (h : Nat.repeat (inc m) i T = Nat.repeat (inc m) j T) : i = j := by
  have hv := congrArg blockToNat h
  rw [blockToNat_repeat_inc hm, blockToNat_repeat_inc hm] at hv
  have hlow := Nat.add_left_cancel hv
  -- Adding `2^m - x mod 2^m` turns `x mod 2^m + i` into `i`, modulo `2^m`.
  have ha : blockToNat T % 2 ^ m < 2 ^ m := Nat.mod_lt _ (Nat.two_pow_pos m)
  have hshift := Nat.add_mod_eq_add_mod_right (2 ^ m - blockToNat T % 2 ^ m) hlow
  rw [show blockToNat T % 2 ^ m + i + (2 ^ m - blockToNat T % 2 ^ m) = i + 2 ^ m by omega,
    show blockToNat T % 2 ^ m + j + (2 ^ m - blockToNat T % 2 ^ m) = j + 2 ^ m by omega,
    Nat.add_mod_right, Nat.add_mod_right, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hshift
  exact hshift

/-- `2^m` increments give back the first counter, so the bound `n <= 2^m` cannot grow. -/
theorem repeat_inc_two_pow {m : Nat} (hm : m ≤ 128) (T : Block) :
    Nat.repeat (inc m) (2 ^ m) T = T := by
  apply blockToNat_injective
  rw [blockToNat_repeat_inc hm, Nat.add_mod_right, Nat.mod_mod, Nat.div_add_mod']

end EthLib.Cryptography.Aes
