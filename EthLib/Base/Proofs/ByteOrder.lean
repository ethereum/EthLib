module

public import EthLib.Base.ByteOrder

/-!
# Proofs: `ByteOrder`

Writing and reading bytes undo each other, in either byte order.

A number below `256 ^ k` survives the trip through `k` bytes.

A vector of `k` bytes survives the trip through its value.

The big-endian bytes are the little-endian bytes in reverse order.
-/

@[expose] public section

namespace EthLib.Base.ByteOrder

/-- Byte `i` of a number is its quotient by `256 ^ i`, truncated to a byte. -/
theorem toLE_eq_div (k n : Nat) :
    toLE k n = Vector.ofFn fun i => UInt8.ofNat (n / 256 ^ i.val) := by
  simp only [toLE, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- The first byte is the low byte, and the rest encode the quotient by 256. -/
theorem toList_toLE_succ (k n : Nat) :
    (toLE (k + 1) n).toList = UInt8.ofNat n :: (toLE k (n / 256)).toList := by
  simp only [toLE_eq_div, Vector.toList_ofFn, List.ofFn_succ, Fin.val_zero, Nat.pow_zero,
    Nat.div_one, Fin.val_succ, Nat.pow_succ, Nat.div_div_eq_div_mul, List.cons.injEq, true_and]
  -- Byte `i + 1` of `n` is byte `i` of `n / 256`.
  congr 1
  funext i
  congr 1
  rw [Nat.mul_comm]

/-- Reading a number back folds over the bytes as a list. -/
theorem ofLE_eq_foldr {k : Nat} (v : Vector UInt8 k) :
    ofLE v = v.toList.foldr (fun byte acc => byte.toNat + 256 * acc) 0 := by
  unfold ofLE
  rw [← Array.foldr_toList]
  rfl

/-- Writing a number on `k` bytes and reading it back keeps its low `8k` bits. -/
@[simp] theorem ofLE_toLE (k n : Nat) :
    ofLE (toLE k n) = n % 256 ^ k := by
  rw [ofLE_eq_foldr]
  induction k generalizing n with
  | zero => simp [toLE_eq_div, Nat.mod_one, Vector.toList_ofFn]
  | succ k ih =>
    -- The low byte plus 256 times the higher bytes is the remainder by `256^(k+1)`.
    rw [toList_toLE_succ, List.foldr_cons, ih, Nat.pow_succ, Nat.mul_comm _ 256,
      Nat.mod_mul]
    simp [UInt8.toNat_ofNat']

private theorem foldr_lt (l : List UInt8) :
    l.foldr (fun byte acc => byte.toNat + 256 * acc) 0 < 256 ^ l.length := by
  induction l with
  | nil => simp
  | cons b t ih =>
    simp only [List.foldr_cons, List.length_cons, Nat.pow_succ]
    -- The low byte is below 256, and the rest is below `256^length`.
    have := b.toNat_lt
    omega

/-- A number read from `k` bytes is below `256^k`. -/
theorem ofLE_lt {k : Nat} (v : Vector UInt8 k) : ofLE v < 256 ^ k := by
  rw [ofLE_eq_foldr]
  simpa using foldr_lt v.toList

private theorem toLE_foldr (l : List UInt8) :
    (toLE l.length (l.foldr (fun byte acc => byte.toNat + 256 * acc) 0)).toList = l := by
  induction l with
  | nil => simp [toLE_eq_div, Vector.toList_ofFn]
  | cons b t ih =>
    rw [List.length_cons, toList_toLE_succ, List.foldr_cons]
    have hb := b.toNat_lt
    -- The low byte is below 256, so dividing by 256 leaves the higher bytes.
    have hdiv : (b.toNat + 256 * t.foldr (fun byte acc => byte.toNat + 256 * acc) 0) / 256
        = t.foldr (fun byte acc => byte.toNat + 256 * acc) 0 := by omega
    rw [hdiv, ih]
    -- The low byte of the number is the first byte itself.
    congr 1
    apply UInt8.toNat.inj
    simp

/-- Reading `k` bytes as a number and writing it back on `k` bytes returns the bytes. -/
@[simp] theorem toLE_ofLE {k : Nat} (v : Vector UInt8 k) :
    toLE k (ofLE v) = v := by
  -- Expose the vector as a list, so its length is the list's own.
  rcases v with ⟨⟨l⟩, rfl⟩
  apply Vector.toList_inj.mp
  rw [ofLE_eq_foldr]
  exact toLE_foldr l

/-- Two numbers below `256^k` with the same `k` bytes are equal. -/
theorem toLE_inj {k x y : Nat} (hx : x < 256 ^ k) (hy : y < 256 ^ k)
    (h : toLE k x = toLE k y) : x = y := by
  -- Reading the bytes back returns each number, unchanged by the bound.
  have := congrArg ofLE h
  simpa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using this

/-! ## Bytes as a list

A decoder that holds its input as a list reads a prefix of unknown length as a vector.

The type of that vector depends on the list, so proofs first turn it into a fold over the list.
-/

/-- A list of bytes, read as a number, is a fold from its last byte down. -/
theorem ofLE_toVector (l : List UInt8) :
    ofLE l.toArray.toVector = l.foldr (fun byte acc => byte.toNat + 256 * acc) 0 := by
  rw [ofLE_eq_foldr]
  simp

/-- The bytes of a number, folded back, keep its low `8k` bits. -/
theorem foldr_toLE (k n : Nat) :
    (toLE k n).toList.foldr (fun byte acc => byte.toNat + 256 * acc) 0 = n % 256 ^ k := by
  rw [← ofLE_eq_foldr, ofLE_toLE]

/-- The bytes of a number below `256^k`, folded back, give the number. -/
theorem foldr_toLE_of_lt {k n : Nat} (h : n < 256 ^ k) :
    (toLE k n).foldr (fun byte acc => byte.toNat + 256 * acc) 0 = n := by
  rw [← Vector.foldr_toList, foldr_toLE, Nat.mod_eq_of_lt h]

/-- At most eight bytes read as a number that a `UInt64` holds exactly. -/
theorem toNat_ofNat_ofLE {k : Nat} (data : Vector UInt8 k) (h : k ≤ 8) :
    (UInt64.ofNat (ofLE data)).toNat = ofLE data := by
  -- At most eight bytes write a value below `2^64`, so the conversion keeps it.
  have hlt : ofLE data < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (ofLE_lt data)
      (by simpa [show (2 : Nat) ^ 64 = 256 ^ 8 from rfl] using Nat.pow_le_pow_right (by decide) h)
  simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]

/-! ## Bytes as an array

A codec that holds its bytes as an array writes and reads a number one byte at a time.
-/

/-- The bytes of a number are its low byte, then the bytes of its quotient by 256. -/
theorem toArray_toLE_succ (k n : Nat) :
    (toLE (k + 1) n).toArray = #[UInt8.ofNat n] ++ (toLE k (n / 256)).toArray := by
  apply Array.toList_inj.mp
  simpa [Vector.toList] using toList_toLE_succ k n

/-- A number read from bytes is the first byte plus 256 times the number the rest read as. -/
theorem ofLE_ofFn_succ {k : Nat} (f : Fin (k + 1) → UInt8) :
    ofLE (Vector.ofFn f)
      = (f 0).toNat + 256 * ofLE (Vector.ofFn fun i => f i.succ) := by
  simp [ofLE_eq_foldr, Vector.toList_ofFn, List.ofFn_succ]

/-! ## Big-endian reading -/

/-- No bytes read as 0. -/
@[simp] theorem ofBE_nil : ofBE [] = 0 := rfl

/-- Bytes appended on the right are the lower digits of a big-endian number. -/
theorem ofBE_append (a b : List UInt8) :
    ofBE (a ++ b) = ofBE a * 256 ^ b.length + ofBE b := by
  rw [ofBE_eq_foldl, List.foldl_append, foldl_ofBE, Nat.mul_comm, ← ofBE_eq_foldl]

/-- A first byte of a big-endian number is worth `256 ^ k`, where `k` bytes follow it. -/
theorem ofBE_cons (b : UInt8) (bytes : List UInt8) :
    ofBE (b :: bytes) = b.toNat * 256 ^ bytes.length + ofBE bytes := by
  rw [← List.singleton_append, ofBE_append]
  simp [ofBE_eq_foldl]

/-- A last byte is the low digit of a big-endian number. -/
@[simp] theorem ofBE_append_singleton (bytes : List UInt8) (b : UInt8) :
    ofBE (bytes ++ [b]) = 256 * ofBE bytes + b.toNat := by
  rw [ofBE_eq_foldl, List.foldl_append, ← ofBE_eq_foldl]
  rfl

/-- A vector reads big-endian as its reversal reads little-endian. -/
theorem ofBE_toList_eq_ofLE_reverse {n : Nat} (v : Vector UInt8 n) :
    ofBE v.toList = ofLE v.reverse := by
  -- A left fold is a right fold over the reversed list.
  rw [ofLE_eq_foldr, Vector.toList_reverse, List.foldr_reverse, ofBE_eq_foldl]
  simp only [Nat.add_comm]

/-! ## Big-endian writing -/

/-- The big-endian bytes, as a list, are the bytes that the loop writes. -/
theorem toList_toBE_eq_go (n x : Nat) : (toBE n x).toList = toBE.go n x [] := rfl

/-- Bytes written before the loop starts stay at the end. -/
theorem toBE.go_append (n x : Nat) (written : List UInt8) :
    toBE.go n x written = toBE.go n x [] ++ written := by
  induction n generalizing x written with
  | zero => rfl
  | succ n ih =>
    rw [toBE.go, toBE.go, ih, ih (written := [_]), List.append_assoc]
    rfl

/-- On `n + 1` bytes, the higher bytes come first and the lowest byte last. -/
theorem toList_toBE_succ (n x : Nat) :
    (toBE (n + 1) x).toList = (toBE n (x / 256)).toList ++ [UInt8.ofNat (x % 256)] := by
  rw [toList_toBE_eq_go, toBE.go, toBE.go_append, ← toList_toBE_eq_go]
  exact congrArg ((toBE n (x / 256)).toList ++ [·]) UInt8.ofNat_mod_size.symm

/-- The big-endian bytes, as a list, are the little-endian bytes in reverse order. -/
theorem toList_toBE (n x : Nat) : (toBE n x).toList = (toLE n x).toList.reverse := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    -- The last big-endian byte is the first little-endian byte, the low byte of `x`.
    rw [toList_toLE_succ, List.reverse_cons, ← ih, toList_toBE_succ]
    exact congrArg ((toBE n (x / 256)).toList ++ [·]) UInt8.ofNat_mod_size

/-- The big-endian bytes are the little-endian bytes in reverse order. -/
theorem toBE_eq_reverse_toLE (n x : Nat) : toBE n x = (toLE n x).reverse := by
  apply Vector.toList_inj.mp
  rw [toList_toBE, Vector.toList_reverse]

/-- Writing a number on `n` bytes and reading it back big-endian keeps its low `8n` bits. -/
@[simp] theorem ofBE_toBE (n x : Nat) : ofBE (toBE n x).toList = x % 256 ^ n := by
  rw [toBE_eq_reverse_toLE, ofBE_toList_eq_ofLE_reverse, Vector.reverse_reverse, ofLE_toLE]

/-- A number below `256 ^ n` survives the round trip through `n` big-endian bytes. -/
theorem ofBE_toBE_of_lt {n x : Nat} (h : x < 256 ^ n) : ofBE (toBE n x).toList = x := by
  rw [ofBE_toBE, Nat.mod_eq_of_lt h]

/-- A list of bytes survives the trip through its big-endian number, written on as many bytes. -/
theorem toList_toBE_ofBE (bytes : List UInt8) :
    (toBE bytes.length (ofBE bytes)).toList = bytes := by
  generalize hn : bytes.length = n
  induction n generalizing bytes with
  | zero => simp [List.length_eq_zero_iff.mp hn]
  | succ n ih =>
    -- Split off the last byte, the lowest digit.
    obtain ⟨front, b, rfl⟩ := (List.eq_nil_or_concat bytes).resolve_left (by rintro rfl; simp at hn)
    rw [List.concat_eq_append] at hn ⊢
    have hf : front.length = n := by simpa using hn
    have hb : b.toNat < 256 := b.toNat_lt
    -- The front is the value divided by 256, and the last byte its remainder.
    have hdiv : (256 * ofBE front + b.toNat) / 256 = ofBE front := by omega
    have hmod : (256 * ofBE front + b.toNat) % 256 = b.toNat := by omega
    rw [ofBE_append_singleton, toList_toBE_succ, hdiv, hmod, ih front hf]
    simp

/-- A list of `n` bytes survives the trip through its big-endian number, written on `n` bytes. -/
theorem toList_toBE_ofBE_of_length {bytes : List UInt8} {n : Nat} (h : bytes.length = n) :
    (toBE n (ofBE bytes)).toList = bytes := by
  subst h
  exact toList_toBE_ofBE bytes

/-- Reading `n` bytes big-endian and writing the number back on `n` bytes returns the bytes. -/
@[simp] theorem toBE_ofBE {n : Nat} (v : Vector UInt8 n) : toBE n (ofBE v.toList) = v :=
  Vector.toList_inj.mp (toList_toBE_ofBE_of_length (by simp))

/-- Two numbers below `256 ^ n` with the same `n` big-endian bytes are equal. -/
theorem toBE_inj {n x y : Nat} (hx : x < 256 ^ n) (hy : y < 256 ^ n)
    (h : toBE n x = toBE n y) : x = y := by
  rw [← ofBE_toBE_of_lt hx, ← ofBE_toBE_of_lt hy, h]

/-- Two byte lists of one length that read as the same big-endian number are equal. -/
theorem ofBE_inj {a b : List UInt8} (length : a.length = b.length) (same : ofBE a = ofBE b) :
    a = b := by
  rw [← toList_toBE_ofBE a, ← toList_toBE_ofBE b, length, same]

/-! ## Big-endian bytes as a list

Many encodings concatenate big-endian fields, so these lemmas state the bytes as a list.
-/

/-- Writing on `n` bytes gives exactly `n` bytes. -/
theorem length_toList_toBE (n x : Nat) : (toBE n x).toList.length = n := by
  simp

/-- Zero bytes write nothing. -/
@[simp] theorem toList_toBE_zero (x : Nat) : (toBE 0 x).toList = [] := rfl

/-- Writing on `a + b` bytes puts `x / 256 ^ b` on the first `a` bytes and `x` on the last `b`. -/
theorem toList_toBE_add (a b x : Nat) :
    (toBE (a + b) x).toList = (toBE a (x / 256 ^ b)).toList ++ (toBE b x).toList := by
  induction b generalizing x with
  | zero => simp [toBE, toBE.go]
  | succ b ih =>
    -- Both sides end with the lowest byte, and the higher bytes are `x / 256` written on `a + b`.
    rw [← Nat.add_assoc, toList_toBE_succ, ih, toList_toBE_succ, List.append_assoc,
      Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 256]

/-- Byte `i` of a number written on `n` bytes is its digit worth `256 ^ (n - 1 - i)`. -/
theorem getElem_toBE {n x i : Nat} (hi : i < n) :
    (toBE n x)[i] = UInt8.ofNat (x / 256 ^ (n - 1 - i) % 256) := by
  -- Byte `i` from the start is little-endian byte `n - 1 - i`.
  rw [UInt8.ofNat_mod_size, toBE_eq_reverse_toLE, Vector.getElem_reverse, toLE_eq_div,
    Vector.getElem_ofFn]

/-- A number written on `n` bytes keeps only its remainder modulo `256 ^ n`. -/
theorem toBE_mod (n x : Nat) : toBE n (x % 256 ^ n) = toBE n x := by
  -- Both write `n` bytes that read back as `x % 256 ^ n`.
  apply Vector.toList_inj.mp
  apply ofBE_inj (by simp)
  simp

/-- Zero on `n` bytes is `n` zero bytes. -/
theorem toList_toBE_zero_right (n : Nat) : (toBE n 0).toList = List.replicate n 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [toList_toBE_succ, Nat.zero_div, ih, List.replicate_succ']; rfl

/-! ## Bytes with no leading zero -/

/-- Zero has no bytes. -/
@[simp] theorem byteLength_zero : byteLength 0 = 0 := rfl

/-- A nonzero number has `log2 / 8 + 1` bytes. -/
theorem byteLength_of_ne_zero {x : Nat} (hx : x ≠ 0) : byteLength x = x.log2 / 8 + 1 := by
  simp [byteLength, hx]

/-- A nonzero number has at least one byte. -/
theorem byteLength_pos {x : Nat} (hx : x ≠ 0) : 0 < byteLength x := by
  simp [byteLength, hx]

/-- A number is below 256 to the power of its number of bytes. -/
theorem lt_byteLength (x : Nat) : x < 256 ^ byteLength x := by
  by_cases hx : x = 0
  · subst hx
    simp [byteLength]
  · rw [byteLength_of_ne_zero hx]
    -- The number is below `2 ^ (log2 + 1)`, and `log2 + 1` bits fit in `log2 / 8 + 1` bytes.
    have h1 : x < 2 ^ (x.log2 + 1) := Nat.lt_log2_self
    have h2 : 2 ^ (x.log2 + 1) ≤ 2 ^ (8 * (x.log2 / 8 + 1)) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : 2 ^ (8 * (x.log2 / 8 + 1)) = 256 ^ (x.log2 / 8 + 1) := by
      rw [Nat.pow_mul]
    omega

/-- A nonzero number is at least `256` to the power of one less than its number of bytes. -/
theorem pow_byteLength_sub_one_le {x : Nat} (hx : x ≠ 0) :
    256 ^ (byteLength x - 1) ≤ x := by
  rw [byteLength_of_ne_zero hx, Nat.add_sub_cancel]
  -- The highest set bit is worth `2 ^ log2`, and `8 * (log2 / 8)` bits lie below it.
  have h1 : 2 ^ x.log2 ≤ x := Nat.log2_self_le (by omega)
  have h2 : 2 ^ (8 * (x.log2 / 8)) ≤ 2 ^ x.log2 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 2 ^ (8 * (x.log2 / 8)) = 256 ^ (x.log2 / 8) := by
    rw [Nat.pow_mul]
  omega

/-- A number below `256 ^ k` has at most `k` bytes. -/
theorem byteLength_le_of_lt {x k : Nat} (h : x < 256 ^ k) : byteLength x ≤ k := by
  by_cases hx : x = 0
  · subst hx
    simp
  · have h1 := pow_byteLength_sub_one_le hx
    have h2 : byteLength x - 1 < k :=
      (Nat.pow_lt_pow_iff_right (by omega)).mp (Nat.lt_of_le_of_lt h1 h)
    have h3 : byteLength x ≠ 0 := by have := byteLength_pos hx; omega
    omega

/-- A number at least `256 ^ k` and below `256 ^ (k + 1)` has `k + 1` bytes. -/
theorem byteLength_eq_of_bounds {x k : Nat} (low : 256 ^ k ≤ x) (high : x < 256 ^ (k + 1)) :
    byteLength x = k + 1 := by
  have hx : x ≠ 0 := by have := Nat.one_le_pow k 256 (by omega); omega
  have h1 := byteLength_le_of_lt high
  have h2 := pow_byteLength_sub_one_le hx
  have h3 := lt_byteLength x
  -- `256 ^ k ≤ x` is below 256 to the power of the byte count, so `k` is below the byte count.
  have h4 : k < byteLength x := (Nat.pow_lt_pow_iff_right (by omega)).mp (Nat.lt_of_le_of_lt low h3)
  omega

/-- The bytes of a number with no leading zero read back as the number. -/
theorem ofBE_toBE_byteLength (x : Nat) : ofBE (toBE (byteLength x) x).toList = x :=
  ofBE_toBE_of_lt (lt_byteLength x)

/-- The shortest bytes of a number start with a nonzero byte, if there is one. -/
theorem head_toBE_byteLength_ne_zero (x : Nat) :
    ∀ b ∈ (toBE (byteLength x) x).toList.head?, b ≠ 0 := by
  by_cases hx : x = 0
  · subst hx
    simp
  · obtain ⟨k, hk⟩ : ∃ k, byteLength x = k + 1 :=
      ⟨byteLength x - 1, by have := byteLength_pos hx; omega⟩
    have low : 256 ^ k ≤ x := by simpa [hk] using pow_byteLength_sub_one_le hx
    have high : x < 256 ^ (k + 1) := hk ▸ lt_byteLength x
    -- The first byte is the digit worth `256 ^ k`, which is between 1 and 255.
    have hq : 1 ≤ x / 256 ^ k := (Nat.le_div_iff_mul_le (Nat.pow_pos (by omega))).mpr (by omega)
    have hq' : x / 256 ^ k < 256 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega)), ← Nat.pow_succ']
      omega
    rw [hk]
    have hget := getElem_toBE (n := k + 1) (x := x) (i := 0) (by omega)
    rw [Nat.sub_zero, Nat.add_sub_cancel, Nat.mod_eq_of_lt hq'] at hget
    have : (toBE (k + 1) x).toList.head? = some (toBE (k + 1) x)[0] := by
      simp [List.head?_eq_getElem?]
    rw [this, hget]
    intro b hb h0
    simp only [Option.mem_def, Option.some.injEq] at hb
    subst hb
    have := congrArg UInt8.toNat h0
    rw [UInt8.toNat_ofNat_of_lt' (by omega)] at this
    simp at this
    omega

/-- Bytes with no leading zero have as many bytes as the number they read as. -/
theorem byteLength_ofBE {bytes : List UInt8} (h : ∀ b ∈ bytes.head?, b ≠ 0) :
    byteLength (ofBE bytes) = bytes.length := by
  cases bytes with
  | nil => simp
  | cons b rest =>
    have hb : b ≠ 0 := h b (by simp)
    have hpos : 1 ≤ b.toNat := by
      have : b.toNat ≠ 0 := fun h0 => hb (UInt8.toNat_inj.mp h0)
      omega
    have hlt := ofBE_lt rest
    have hcons := ofBE_cons b rest
    -- The first byte is worth at least `256 ^ rest.length`; the whole is below `256 ^ length`.
    have hb256 : b.toNat < 256 := b.toNat_lt
    have low : 256 ^ rest.length ≤ ofBE (b :: rest) := by
      rw [hcons]
      have := Nat.mul_le_mul_right (256 ^ rest.length) hpos
      omega
    have high : ofBE (b :: rest) < 256 ^ (rest.length + 1) := by
      simpa using ofBE_lt (b :: rest)
    exact byteLength_eq_of_bounds low high

/-- Two bytes compare as the numbers they hold. -/
theorem _root_.UInt8.compare_eq_compare_toNat (a b : UInt8) :
    compare a b = compare a.toNat b.toNat := by
  simp only [compare, compareOfLessAndEq, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj]

/-- Two lists of bytes of one length compare, byte after byte, as their big-endian numbers. -/
theorem compare_eq_compare_ofBE {a b : List UInt8} (h : a.length = b.length) :
    compare a b = compare (ofBE a) (ofBE b) := by
  induction a generalizing b with
  | nil =>
    rw [List.length_nil, eq_comm, List.length_eq_zero_iff] at h
    subst h
    rfl
  | cons x a ih =>
    obtain ⟨y, b, rfl⟩ := List.exists_cons_of_length_eq_add_one h.symm
    have hlen : a.length = b.length := by simpa using h
    have ha := ofBE_lt a
    have hb := ofBE_lt b
    rw [← hlen] at hb
    rw [List.compare_cons_cons, ih hlen, ofBE_cons, ofBE_cons, ← hlen,
      UInt8.compare_eq_compare_toNat]
    -- The first bytes decide, since each tail is worth less than one unit of the first byte.
    generalize 256 ^ a.length = unit at ha hb ⊢
    rcases Nat.lt_trichotomy x.toNat y.toNat with hxy | hxy | hxy
    · have : x.toNat * unit + ofBE a < y.toNat * unit + ofBE b := by
        have := Nat.mul_le_mul_right unit (Nat.succ_le_of_lt hxy)
        rw [Nat.succ_mul] at this
        omega
      rw [Nat.compare_eq_lt.mpr hxy, Nat.compare_eq_lt.mpr this]
      rfl
    · rw [hxy, Nat.compare_eq_eq.mpr rfl]
      simp only [Ordering.then, Nat.compare_eq_ite_lt, Nat.add_lt_add_iff_left]
    · have : y.toNat * unit + ofBE b < x.toNat * unit + ofBE a := by
        have := Nat.mul_le_mul_right unit (Nat.succ_le_of_lt hxy)
        rw [Nat.succ_mul] at this
        omega
      rw [Nat.compare_eq_gt.mpr hxy, Nat.compare_eq_gt.mpr this]
      rfl

/-- Numbers written on `w` bytes each, one after the other, take `w` bytes each. -/
theorem length_flatMap_toBE (w : Nat) (xs : List Nat) :
    (xs.flatMap fun x => (toBE w x).toList).length = w * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, length_toList_toBE, ih, List.length_cons,
      Nat.mul_succ, Nat.add_comm]

/-- Numbers below `256 ^ w`, written on `w` bytes each, read back from their blocks of `w` bytes.

Block `i` is the `w` bytes after the first `i * w`. -/
theorem map_range_ofBE_flatMap_toBE {w : Nat} {xs : List Nat}
    (hlt : ∀ x ∈ xs, x < 256 ^ w) :
    (List.range xs.length).map
      (fun i => ofBE (((xs.flatMap fun x => (toBE w x).toList).drop (i * w)).take w)) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : (toBE w x).toList.length = w := length_toList_toBE w x
    -- Past the first block, block `i + 1` of the list is block `i` of the rest.
    have hshift : ∀ i,
        (((toBE w x).toList ++ xs.flatMap fun x => (toBE w x).toList).drop ((i + 1) * w)).take w =
          ((xs.flatMap fun x => (toBE w x).toList).drop (i * w)).take w := fun i => by
      rw [Nat.add_one_mul, Nat.add_comm (i * w) w, ← List.drop_drop, List.drop_left' hx]
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.flatMap_cons]
    simp only [Function.comp_def, hshift, Nat.zero_mul, List.drop_zero]
    rw [ih fun y hy => hlt y (List.mem_cons_of_mem x hy), List.take_left' hx,
      ofBE_toBE_of_lt (hlt x List.mem_cons_self)]

/-- Bytes of length `w * n`, read as `n` blocks of `w` bytes and written back, are unchanged. -/
theorem flatMap_toBE_map_range_ofBE {w n : Nat} {bytes : List UInt8}
    (hlen : bytes.length = w * n) :
    ((List.range n).map fun i => ofBE ((bytes.drop (i * w)).take w)).flatMap
      (fun x => (toBE w x).toList) = bytes := by
  induction n generalizing bytes with
  | zero =>
    rw [Nat.mul_zero, List.length_eq_zero_iff] at hlen
    simp [hlen]
  | succ n ih =>
    have htake : (bytes.take w).length = w := by
      rw [List.length_take, hlen, Nat.mul_succ]
      omega
    have hdrop : (bytes.drop w).length = w * n := by
      rw [List.length_drop, hlen, Nat.mul_succ]
      omega
    -- Past the first block, block `i + 1` of the bytes is block `i` of the rest.
    have hshift : ∀ i, (bytes.drop ((i + 1) * w)).take w = ((bytes.drop w).drop (i * w)).take w :=
      fun i => by rw [List.drop_drop, Nat.add_one_mul, Nat.add_comm (i * w) w]
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.flatMap_cons]
    simp only [Function.comp_def, hshift, Nat.zero_mul, List.drop_zero]
    have hfirst := toList_toBE_ofBE (bytes.take w)
    rw [htake] at hfirst
    rw [ih hdrop, hfirst, List.take_append_drop]

end EthLib.Base.ByteOrder
