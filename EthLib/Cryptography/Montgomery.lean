module


/-!
# Montgomery arithmetic

Arithmetic mod an odd modulus `p` below `R = 2 ^ (32 n)`, on `n` limbs of 32 bits.

An element `a` is stored in Montgomery form, as `a R mod p`.

The product of two forms is then `a b R ^ 2`, and one Montgomery reduction divides it by `R`.

The reduction adds the multiple of `p` that clears the low limb, then drops that limb.

So it needs no division by `p`.

The product is the Coarsely Integrated Operand Scanning (CIOS) method of Koç, Acar and Kaliski.

It appeared as "Analyzing and comparing Montgomery multiplication algorithms" in IEEE Micro 16(3).

<https://doi.org/10.1109/40.502403>

It interleaves the product and the reduction, one limb of `b` at a time.

Each product of two limbs fits in 64 bits, so the code needs no wider product.

The code is written once for every limb count.

Instances for `0` and `n + 1` limbs build it, so the compiler unrolls it for a fixed count.

Every operation keeps its result below `p`, and the theorems here prove those bounds.

The proofs that the operations agree with the integers mod `p` come with the other properties.
-/

@[expose] public section

namespace EthLib.Cryptography

namespace Montgomery

/-! ## Words of 32 bits -/

/-- The low 32 bits and the carry of `t + a * b + c`. -/
@[inline] def mac (t a b c : UInt64) : UInt64 × UInt64 :=
  let s := t + a * b + c
  (s &&& 0xFFFFFFFF, s >>> 32)

/-- The two words of `mac` write `t + a b + c`, when every input is below `2 ^ 32`. -/
theorem mac_spec {t a b c : UInt64} (ht : t.toNat < 2 ^ 32) (ha : a.toNat < 2 ^ 32)
    (hb : b.toNat < 2 ^ 32) (hc : c.toNat < 2 ^ 32) :
    (mac t a b c).1.toNat + 2 ^ 32 * (mac t a b c).2.toNat
      = t.toNat + a.toNat * b.toNat + c.toNat ∧
    (mac t a b c).1.toNat < 2 ^ 32 ∧ (mac t a b c).2.toNat < 2 ^ 32 := by
  have hab : a.toNat * b.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hs : (t + a * b + c).toNat = t.toNat + a.toNat * b.toNat + c.toNat := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul]
    rw [Nat.mod_eq_of_lt (a := a.toNat * b.toNat) (by omega)]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hm : (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 := rfl
  simp only [mac, UInt64.toNat_and, UInt64.toNat_shiftRight, hs, hm,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  simp
  omega

/-- The low 32 bits of `x - y - b`, and the borrow out of them. -/
@[inline] def sbb (x y b : UInt64) : UInt64 × UInt64 :=
  let d := x - y - b
  (d &&& 0xFFFFFFFF, d >>> 63)

/-- The two words of `sbb` write `x - y - b`, with the borrow as a multiple of `2 ^ 32`. -/
theorem sbb_spec {x y b : UInt64} (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32)
    (hb : b.toNat ≤ 1) :
    (sbb x y b).1.toNat + y.toNat + b.toNat = x.toNat + 2 ^ 32 * (sbb x y b).2.toNat ∧
    (sbb x y b).1.toNat < 2 ^ 32 ∧ (sbb x y b).2.toNat ≤ 1 := by
  have hm : (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 := rfl
  simp only [sbb, UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.toNat_sub, hm,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  simp
  omega

/-! ## Numbers written in words -/

/-- The integer that the words `f k` to `f (k + n - 1)` write in base `2 ^ 32`, the lowest first. -/
def num : Nat → (Nat → UInt64) → Nat → Nat
  | 0, _, _ => 0
  | n + 1, f, k => (f k).toNat + 2 ^ 32 * num n f (k + 1)

/-- The words `f k` to `f (k + n - 1)` are below `2 ^ 32`. -/
def Fits : Nat → (Nat → UInt64) → Nat → Prop
  | 0, _, _ => True
  | n + 1, f, k => (f k).toNat < 2 ^ 32 ∧ Fits n f (k + 1)

/-- The word `h`, then the words of `w`. -/
@[inline] def cons (h : UInt64) (w : Nat → UInt64) (k : Nat) : UInt64 :=
  if k = 0 then h else w (k - 1)

/-- `n` steps of `f`, on the indices from `k`. -/
def loop {σ : Type} : Nat → (Nat → σ → σ) → Nat → σ → σ
  | 0, _, _, s => s
  | n + 1, f, k, s => loop n f (k + 1) (f k s)

/-- No words write `0`. -/
theorem num_zero (f : Nat → UInt64) (k : Nat) : num 0 f k = 0 := rfl

/-- The lowest word, then the others above it. -/
theorem num_succ (n : Nat) (f : Nat → UInt64) (k : Nat) :
    num (n + 1) f k = (f k).toNat + 2 ^ 32 * num n f (k + 1) := rfl

/-- No words fit. -/
theorem fits_zero (f : Nat → UInt64) (k : Nat) : Fits 0 f k := trivial

/-- `n + 1` words fit when the lowest one and the others fit. -/
theorem fits_succ {n : Nat} {f : Nat → UInt64} {k : Nat} :
    Fits (n + 1) f k ↔ (f k).toNat < 2 ^ 32 ∧ Fits n f (k + 1) := Iff.rfl

/-- Words that agree write the same integer. -/
theorem num_congr {n : Nat} {f g : Nat → UInt64} {j k : Nat}
    (h : ∀ i < n, f (j + i) = g (k + i)) : num n f j = num n g k := by
  induction n generalizing j k with
  | zero => rfl
  | succ n ih =>
    rw [num_succ, num_succ, show f j = g k from h 0 (by omega)]
    rw [@ih (j + 1) (k + 1) fun i hi => by
      rw [Nat.add_right_comm j 1 i, Nat.add_right_comm k 1 i]
      exact h (i + 1) (by omega)]

/-- Words that agree fit together. -/
theorem fits_congr {n : Nat} {f g : Nat → UInt64} {j k : Nat}
    (h : ∀ i < n, f (j + i) = g (k + i)) : Fits n f j ↔ Fits n g k := by
  induction n generalizing j k with
  | zero => exact Iff.rfl
  | succ n ih =>
    rw [fits_succ, fits_succ, show f j = g k from h 0 (by omega)]
    rw [@ih (j + 1) (k + 1) fun i hi => by
      rw [Nat.add_right_comm j 1 i, Nat.add_right_comm k 1 i]
      exact h (i + 1) (by omega)]

/-- The words fit when each one is below `2 ^ 32`. -/
theorem fits_of_lt {n : Nat} {f : Nat → UInt64} {k : Nat}
    (h : ∀ i < n, (f (k + i)).toNat < 2 ^ 32) : Fits n f k := by
  induction n generalizing k with
  | zero => trivial
  | succ n ih =>
    refine ⟨h 0 (by omega), ih fun i hi => ?_⟩
    rw [Nat.add_right_comm]
    exact h (i + 1) (by omega)

/-- After its first word, a word followed by `w` reads as `w`. -/
theorem num_cons {n : Nat} (h : UInt64) (w : Nat → UInt64) (k : Nat) :
    num n (cons h w) (k + 1) = num n w k :=
  num_congr fun i _ => by
    simp only [cons, Nat.add_right_comm k 1 i, Nat.add_one_ne_zero, ↓reduceIte,
      Nat.add_sub_cancel]

/-- After its first word, a word followed by `w` fits as `w`. -/
theorem fits_cons {n : Nat} (h : UInt64) (w : Nat → UInt64) (k : Nat) :
    Fits n (cons h w) (k + 1) ↔ Fits n w k :=
  fits_congr fun i _ => by
    simp only [cons, Nat.add_right_comm k 1 i, Nat.add_one_ne_zero, ↓reduceIte,
      Nat.add_sub_cancel]

/-- The integer of a word `h` followed by words `w`. -/
theorem num_cons_zero {n : Nat} (h : UInt64) (w : Nat → UInt64) :
    num (n + 1) (cons h w) 0 = h.toNat + 2 ^ 32 * num n w 0 := by
  rw [num_succ, num_cons]
  rfl

/-- A word followed by `w` fits when the word and `w` fit. -/
theorem fits_cons_zero {n : Nat} {h : UInt64} {w : Nat → UInt64} :
    Fits (n + 1) (cons h w) 0 ↔ h.toNat < 2 ^ 32 ∧ Fits n w 0 := by
  rw [fits_succ, fits_cons]
  rfl

/-- `2 ^ (32 (n + 1))` is `2 ^ 32` times `2 ^ (32 n)`. -/
theorem radix_succ (n : Nat) : 2 ^ (32 * (n + 1)) = 2 ^ 32 * 2 ^ (32 * n) := by
  rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]

/-- Words that fit write an integer below `2 ^ (32 n)`. -/
theorem num_lt {n : Nat} {f : Nat → UInt64} {k : Nat} (h : Fits n f k) :
    num n f k < 2 ^ (32 * n) := by
  induction n generalizing k with
  | zero => exact Nat.one_pos
  | succ n ih =>
    have := ih h.2
    rw [num_succ, radix_succ]
    have := h.1
    omega

/-- The top word of `n + 1` words weighs `2 ^ (32 n)`. -/
theorem num_snoc (n : Nat) (f : Nat → UInt64) (k : Nat) :
    num (n + 1) f k = num n f k + 2 ^ (32 * n) * (f (k + n)).toNat := by
  induction n generalizing k with
  | zero => simp [num]
  | succ n ih =>
    rw [num_succ, ih, num_succ, radix_succ, Nat.add_right_comm k 1 n, Nat.mul_add,
      Nat.mul_assoc, show f (k + (n + 1)) = f (k + n + 1) from rfl]
    omega

/-- The top word of fitting words is `0` when their integer is below `2 ^ (32 n)`. -/
theorem fits_snoc {n : Nat} {f : Nat → UInt64} {k : Nat} :
    Fits (n + 1) f k ↔ Fits n f k ∧ (f (k + n)).toNat < 2 ^ 32 := by
  induction n generalizing k with
  | zero => simp [Fits]
  | succ n ih =>
    rw [fits_succ, ih, fits_succ, Nat.add_right_comm k 1 n]
    exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩

/-- Fitting words with the same integer are the same words. -/
theorem eq_of_num_eq {n : Nat} {f g : Nat → UInt64} {k : Nat} (hf : Fits n f k)
    (hg : Fits n g k) (h : num n f k = num n g k) : ∀ i < n, f (k + i) = g (k + i) := by
  induction n generalizing k with
  | zero => intro i hi; omega
  | succ n ih =>
    rw [num_succ, num_succ] at h
    have := hf.1
    have := hg.1
    have h0 : (f k).toNat = (g k).toNat := by omega
    have h1 : num n f (k + 1) = num n g (k + 1) := by omega
    intro i hi
    rcases i with _ | i
    · exact UInt64.toNat_inj.mp h0
    · have e := ih hf.2 hg.2 h1 i (by omega)
      rwa [Nat.add_right_comm k 1 i, Nat.add_assoc] at e

/-- An invariant that each step keeps holds after the steps. -/
theorem loop_induct {σ : Type} (P : Nat → σ → Prop) (f : Nat → σ → σ) (n k : Nat) (s : σ)
    (h0 : P k s) (hs : ∀ i s, k ≤ i → i < k + n → P i s → P (i + 1) (f i s)) :
    P (k + n) (loop n f k s) := by
  induction n generalizing k s with
  | zero => exact h0
  | succ n ih =>
    rw [loop, show k + (n + 1) = k + 1 + n by omega]
    exact ih (k + 1) (f k s) (hs k s (Nat.le_refl k) (by omega) h0)
      (fun i s hi hi' => hs i s (by omega) (by omega))

/-- `k + m` steps are `k` steps, then `m` steps from the index after them. -/
theorem loop_add {σ : Type} (f : Nat → σ → σ) (k m i : Nat) (s : σ) :
    loop (k + m) f i s = loop m f (i + k) (loop k f i s) := by
  induction k generalizing i s with
  | zero => rw [Nat.zero_add, Nat.add_zero]; rfl
  | succ k ih =>
    rw [show k + 1 + m = k + m + 1 by omega, loop, ih, loop, show i + 1 + k = i + (k + 1) by omega]

/-! ## Unrolled words -/

/-- Words of `n` limbs, each held in 64 bits, with the operations of the product.

The instances for `0` and `n + 1` limbs build them, so a fixed count unrolls at compile time.

The words of `n + 1` limbs are a pair, which the compiler erases, so each word stays in a register.

Each operation reads its inputs through a function of the limb index.

So a modulus given by a match on the index folds to immediate constants.

Each operation carries the equation of its value, proved once from the instance below it. -/
class Words (n : Nat) where
  /-- The words. -/
  W : Type
  /-- The word at an index, and `0` past the last. -/
  word : W → Nat → UInt64
  /-- The words of `0`. -/
  zero : W
  /-- The words `a k` to `a (k + n - 1)`. -/
  load : (Nat → UInt64) → Nat → W
  /-- `t + a b + c`, for the words `a` from `k`: the low words and the carry out. -/
  mac : W → (Nat → UInt64) → UInt64 → UInt64 → Nat → W × UInt64
  /-- `t + m p + c` with the word `top` above `t`, for the words `p` from `k`.

  It gives `n + 1` low words, the top one first, and the carry out. -/
  sh : W → (Nat → UInt64) → UInt64 → UInt64 → Nat → UInt64 → (UInt64 × W) × UInt64
  /-- `(t + m p + R top) / 2 ^ 32`, when the low word of the sum is `0`, with `R = 2 ^ (32 n)`.

  It gives the low words and the word above them. -/
  red : W → (Nat → UInt64) → UInt64 → UInt64 → W × UInt64
  /-- `t - p - br`, for the words `p` from `k`: the low words and the borrow out. -/
  subb : W → (Nat → UInt64) → UInt64 → Nat → W × UInt64
  /-- `n` steps of `f`, from the index `k`. -/
  fold {σ : Type} : (Nat → σ → σ) → Nat → σ → σ
  /-- The words of zero are `0`. -/
  word_zero : ∀ i, word zero i = 0
  /-- The loaded words are the words read. -/
  word_load : ∀ a k i, i < n → word (load a k) i = a (k + i)
  /-- The product and sum write `t + a b + c`. -/
  mac_spec : ∀ t a b c k, Fits n (word t) 0 → Fits n a k → b.toNat < 2 ^ 32 →
    c.toNat < 2 ^ 32 →
    Fits n (word (mac t a b c k).1) 0 ∧ (mac t a b c k).2.toNat < 2 ^ 32 ∧
      num n (word (mac t a b c k).1) 0 + 2 ^ (32 * n) * (mac t a b c k).2.toNat =
        num n (word t) 0 + num n a k * b.toNat + c.toNat
  /-- The row writes `t + m p + c`, with `top` above `t`. -/
  sh_spec : ∀ t p m c k top, Fits n (word t) 0 → Fits n p k → m.toNat < 2 ^ 32 →
    c.toNat < 2 ^ 32 → top.toNat < 2 ^ 33 →
    Fits (n + 1) (cons (sh t p m c k top).1.1 (word (sh t p m c k top).1.2)) 0 ∧
      (sh t p m c k top).2.toNat < 2 ^ 32 ∧
      num (n + 1) (cons (sh t p m c k top).1.1 (word (sh t p m c k top).1.2)) 0 +
          2 ^ (32 * (n + 1)) * (sh t p m c k top).2.toNat =
        num n (word t) 0 + m.toNat * num n p k + c.toNat + 2 ^ (32 * n) * top.toNat
  /-- The reduction row writes the sum divided by `2 ^ 32`. -/
  red_spec : ∀ t p m top, Fits n (word t) 0 → Fits n p 0 → m.toNat < 2 ^ 32 →
    top.toNat < 2 ^ 33 →
    (num n (word t) 0 + m.toNat * num n p 0 + 2 ^ (32 * n) * top.toNat) % 2 ^ 32 = 0 →
    Fits n (word (red t p m top).1) 0 ∧ (red t p m top).2.toNat < 2 ^ 32 ∧
      2 ^ 32 * (num n (word (red t p m top).1) 0 + 2 ^ (32 * n) * (red t p m top).2.toNat) =
        num n (word t) 0 + m.toNat * num n p 0 + 2 ^ (32 * n) * top.toNat
  /-- The difference writes `t - p - br`, with the borrow on top. -/
  subb_spec : ∀ t p br k, Fits n (word t) 0 → Fits n p k → br.toNat ≤ 1 →
    Fits n (word (subb t p br k).1) 0 ∧ (subb t p br k).2.toNat ≤ 1 ∧
      num n (word (subb t p br k).1) 0 + num n p k + br.toNat =
        num n (word t) 0 + 2 ^ (32 * n) * (subb t p br k).2.toNat
  /-- The unrolled steps are the steps. -/
  fold_eq : ∀ {σ : Type} (f : Nat → σ → σ) k s, fold f k s = loop n f k s
  /-- Words with the same words at each index below `n` are equal. -/
  ext : ∀ s t, (∀ i < n, word s i = word t i) → s = t

/-- No words. -/
instance : Words 0 where
  W := Unit
  word _ _ := 0
  zero := ()
  load _ _ := ()
  mac _ _ _ c _ := ((), c)
  sh _ _ _ c _ top := let x := top + c; ((x &&& 0xFFFFFFFF, ()), x >>> 32)
  red _ _ _ top := ((), top >>> 32)
  subb _ _ br _ := ((), br)
  fold _ _ s := s
  word_zero _ := rfl
  word_load _ _ _ h := absurd h (Nat.not_lt_zero _)
  mac_spec _ _ _ c _ _ _ _ hc := ⟨trivial, hc, by simp [num]⟩
  sh_spec _ _ _ c _ top _ _ _ hc ht := by
    have hm : (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 := rfl
    have hx : (top + c).toNat = top.toNat + c.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    simp only [num_cons_zero, fits_cons_zero, UInt64.toNat_and, UInt64.toNat_shiftRight, hx, hm,
      Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
    simp [num, Fits]
    omega
  red_spec _ _ _ top _ _ _ ht h := by
    simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    simp [num, Fits] at h ⊢
    omega
  subb_spec _ _ _ _ _ _ hb := ⟨trivial, hb, by simp [num]⟩
  fold_eq _ _ _ := rfl
  ext _ _ _ := rfl

section Succ

variable {n : Nat} [inst : Words n]

/-- The words of `n + 1` limbs: the low word, then the others. -/
@[inline] def wordS (t : UInt64 × inst.W) : Nat → UInt64 :=
  cons t.1 (Words.word t.2)

/-- `t + a b + c` on `n + 1` words: the low word, then the words above it. -/
@[inline] def macS (t : UInt64 × inst.W) (a : Nat → UInt64) (b c : UInt64) (k : Nat) :
    (UInt64 × inst.W) × UInt64 :=
  let x := mac t.1 (a k) b c
  let r := Words.mac t.2 a b x.2 (k + 1)
  ((x.1, r.1), r.2)

/-- `t + m p + c` with `top` above it, on `n + 1` words: the low word, then the others. -/
@[inline] def shS (t : UInt64 × inst.W) (p : Nat → UInt64) (m c : UInt64) (k : Nat)
    (top : UInt64) : (UInt64 × (UInt64 × inst.W)) × UInt64 :=
  let x := mac t.1 m (p k) c
  let r := Words.sh t.2 p m x.2 (k + 1) top
  ((x.1, r.1), r.2)

/-- `(t + m p + R top) / 2 ^ 32` on `n + 1` words, when the low word of the sum is `0`. -/
@[inline] def redS (t : UInt64 × inst.W) (p : Nat → UInt64) (m top : UInt64) :
    (UInt64 × inst.W) × UInt64 :=
  -- The low word of the sum is `0`, so only its carry goes on.
  let x := mac t.1 m (p 0) 0
  Words.sh t.2 p m x.2 1 top

/-- `t - p - br` on `n + 1` words: the low word, then the others and the borrow. -/
@[inline] def subbS (t : UInt64 × inst.W) (p : Nat → UInt64) (br : UInt64) (k : Nat) :
    (UInt64 × inst.W) × UInt64 :=
  let d := sbb t.1 (p k) br
  let r := Words.subb t.2 p d.2 (k + 1)
  ((d.1, r.1), r.2)

/-- The words of a pair fit when its low word and the rest fit. -/
private theorem fits_wordS {t : UInt64 × inst.W} :
    Fits (n + 1) (wordS t) 0 ↔ t.1.toNat < 2 ^ 32 ∧ Fits n (Words.word t.2) 0 :=
  fits_cons_zero

/-- The integer of a pair is its low word plus `2 ^ 32` times the rest. -/
private theorem num_wordS (t : UInt64 × inst.W) :
    num (n + 1) (wordS t) 0 = t.1.toNat + 2 ^ 32 * num n (Words.word t.2) 0 :=
  num_cons_zero _ _

/-- The words of `t + a b + c` on `n + 1` words write the sum. -/
theorem macS_spec (t : UInt64 × inst.W) (a : Nat → UInt64) (b c : UInt64) (k : Nat)
    (ht : Fits (n + 1) (wordS t) 0) (ha : Fits (n + 1) a k) (hb : b.toNat < 2 ^ 32)
    (hc : c.toNat < 2 ^ 32) :
    Fits (n + 1) (wordS (macS t a b c k).1) 0 ∧ (macS t a b c k).2.toNat < 2 ^ 32 ∧
      num (n + 1) (wordS (macS t a b c k).1) 0 + 2 ^ (32 * (n + 1)) * (macS t a b c k).2.toNat =
        num (n + 1) (wordS t) 0 + num (n + 1) a k * b.toNat + c.toNat := by
  rw [fits_wordS] at ht
  obtain ⟨ex, lx, cx⟩ := mac_spec ht.1 ha.1 hb hc
  obtain ⟨fr, cr, er⟩ := Words.mac_spec t.2 a b (mac t.1 (a k) b c).2 (k + 1) ht.2 ha.2 hb cx
  refine ⟨fits_wordS.mpr ⟨lx, fr⟩, cr, ?_⟩
  dsimp only [macS]
  rw [num_wordS, num_wordS, num_succ n a k, radix_succ]
  generalize Words.mac t.2 a b (mac t.1 (a k) b c).2 (k + 1) = r at *
  generalize mac t.1 (a k) b c = x at *
  generalize 2 ^ (32 * n) = R at *
  simp only [Nat.add_mul, Nat.mul_assoc] at *
  omega

/-- The words of `t + m p + c` with `top` above write the sum. -/
theorem shS_spec (t : UInt64 × inst.W) (p : Nat → UInt64) (m c : UInt64) (k : Nat)
    (top : UInt64) (ht : Fits (n + 1) (wordS t) 0) (hp : Fits (n + 1) p k)
    (hm : m.toNat < 2 ^ 32) (hc : c.toNat < 2 ^ 32) (htop : top.toNat < 2 ^ 33) :
    Fits (n + 1 + 1) (cons (shS t p m c k top).1.1 (wordS (shS t p m c k top).1.2)) 0 ∧
      (shS t p m c k top).2.toNat < 2 ^ 32 ∧
      num (n + 1 + 1) (cons (shS t p m c k top).1.1 (wordS (shS t p m c k top).1.2)) 0 +
          2 ^ (32 * (n + 1 + 1)) * (shS t p m c k top).2.toNat =
        num (n + 1) (wordS t) 0 + m.toNat * num (n + 1) p k + c.toNat +
          2 ^ (32 * (n + 1)) * top.toNat := by
  rw [fits_wordS] at ht
  obtain ⟨ex, lx, cx⟩ := mac_spec ht.1 hm hp.1 hc
  obtain ⟨fr, cr, er⟩ := Words.sh_spec t.2 p m (mac t.1 m (p k) c).2 (k + 1) top ht.2 hp.2 hm cx
    htop
  refine ⟨fits_cons_zero.mpr ⟨lx, fr⟩, cr, ?_⟩
  change num (n + 1) (wordS (Words.sh t.2 p m (mac t.1 m (p k) c).2 (k + 1) top).1) 0 + _ = _
    at er
  dsimp only [shS]
  rw [num_cons_zero, num_wordS t, num_succ n p k, radix_succ (n + 1), radix_succ n]
  rw [radix_succ n] at er
  generalize Words.sh t.2 p m (mac t.1 m (p k) c).2 (k + 1) top = r at *
  generalize mac t.1 m (p k) c = x at *
  generalize num (n + 1) (wordS r.1) 0 = A at *
  generalize 2 ^ (32 * n) = R at *
  simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm _ (2 ^ 32)] at *
  omega

/-- The words of the reduction row write the sum divided by `2 ^ 32`. -/
theorem redS_spec (t : UInt64 × inst.W) (p : Nat → UInt64) (m top : UInt64)
    (ht : Fits (n + 1) (wordS t) 0) (hp : Fits (n + 1) p 0) (hm : m.toNat < 2 ^ 32)
    (htop : top.toNat < 2 ^ 33)
    (h : (num (n + 1) (wordS t) 0 + m.toNat * num (n + 1) p 0 +
      2 ^ (32 * (n + 1)) * top.toNat) % 2 ^ 32 = 0) :
    Fits (n + 1) (wordS (redS t p m top).1) 0 ∧ (redS t p m top).2.toNat < 2 ^ 32 ∧
      2 ^ 32 * (num (n + 1) (wordS (redS t p m top).1) 0 +
          2 ^ (32 * (n + 1)) * (redS t p m top).2.toNat) =
        num (n + 1) (wordS t) 0 + m.toNat * num (n + 1) p 0 +
          2 ^ (32 * (n + 1)) * top.toNat := by
  rw [fits_wordS] at ht
  have z : (0 : UInt64).toNat < 2 ^ 32 := by decide
  obtain ⟨ex, lx, cx⟩ := mac_spec ht.1 hm hp.1 z
  obtain ⟨fr, cr, er⟩ := Words.sh_spec t.2 p m (mac t.1 m (p 0) 0).2 1 top ht.2 hp.2 hm cx htop
  refine ⟨fr, cr, ?_⟩
  change num (n + 1) (wordS (Words.sh t.2 p m (mac t.1 m (p 0) 0).2 1 top).1) 0 + _ = _ at er
  dsimp only [redS]
  rw [num_wordS t, num_succ n p 0, radix_succ n] at h ⊢
  rw [radix_succ n] at er
  rw [UInt64.toNat_zero, Nat.add_zero] at ex
  generalize Words.sh t.2 p m (mac t.1 m (p 0) 0).2 1 top = r at *
  generalize mac t.1 m (p 0) 0 = x at *
  generalize num (n + 1) (wordS r.1) 0 = A at *
  generalize 2 ^ (32 * n) = R at *
  simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm _ (2 ^ 32), Nat.zero_add] at *
  omega

/-- The words of `t - p - br` write the difference, with the borrow on top. -/
theorem subbS_spec (t : UInt64 × inst.W) (p : Nat → UInt64) (br : UInt64) (k : Nat)
    (ht : Fits (n + 1) (wordS t) 0) (hp : Fits (n + 1) p k) (hb : br.toNat ≤ 1) :
    Fits (n + 1) (wordS (subbS t p br k).1) 0 ∧ (subbS t p br k).2.toNat ≤ 1 ∧
      num (n + 1) (wordS (subbS t p br k).1) 0 + num (n + 1) p k + br.toNat =
        num (n + 1) (wordS t) 0 + 2 ^ (32 * (n + 1)) * (subbS t p br k).2.toNat := by
  rw [fits_wordS] at ht
  obtain ⟨ed, ld, bd⟩ := sbb_spec ht.1 hp.1 hb
  obtain ⟨fr, br', er⟩ := Words.subb_spec t.2 p (sbb t.1 (p k) br).2 (k + 1) ht.2 hp.2 bd
  refine ⟨fits_wordS.mpr ⟨ld, fr⟩, br', ?_⟩
  dsimp only [subbS]
  rw [num_wordS, num_wordS, num_succ n p k, radix_succ]
  generalize Words.subb t.2 p (sbb t.1 (p k) br).2 (k + 1) = r at *
  generalize sbb t.1 (p k) br = d at *
  generalize 2 ^ (32 * n) = R at *
  simp only [Nat.mul_assoc] at *
  omega

/-- The words of `n + 1` limbs: a low word and the words of `n` limbs. -/
@[inline] instance instWordsSucc : Words (n + 1) where
  W := UInt64 × inst.W
  word := wordS
  zero := (0, Words.zero)
  load a k := (a k, Words.load a (k + 1))
  mac := macS
  sh := shS
  red := redS
  subb := subbS
  fold f k s := Words.fold (n := n) f (k + 1) (f k s)
  word_zero i := by
    simp only [wordS, cons]
    split
    · rfl
    · exact Words.word_zero _
  word_load a k i hi := by
    simp only [wordS, cons]
    split
    · rename_i h
      subst h
      rfl
    · rw [Words.word_load _ _ _ (by omega)]
      congr 1
      omega
  mac_spec := macS_spec
  sh_spec := shS_spec
  red_spec := redS_spec
  subb_spec := subbS_spec
  fold_eq f k s := by
    rw [Words.fold_eq]
    rfl
  ext s t h := by
    have h0 := h 0 (Nat.succ_pos n)
    simp only [wordS, cons, ↓reduceIte] at h0
    refine Prod.ext h0 (Words.ext _ _ fun i hi => ?_)
    have e := h (i + 1) (by omega)
    simpa only [wordS, cons, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] using e

end Succ

/-- The words of a fixed count are the words of a pair of a low word and the rest. -/
theorem word_succ {n : Nat} [Words n] (t : Words.W (n + 1)) :
    Words.word t = cons (t : UInt64 × Words.W n).1 (Words.word (t : UInt64 × Words.W n).2) := rfl

/-- The words of fitting words are below `2 ^ 32`. -/
theorem lt_of_fits {n : Nat} {f : Nat → UInt64} {k : Nat} (h : Fits n f k) :
    ∀ i < n, (f (k + i)).toNat < 2 ^ 32 := by
  induction n generalizing k with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    rcases i with _ | i
    · exact h.1
    · have e := ih h.2 i (by omega)
      rwa [Nat.add_right_comm k 1 i, Nat.add_assoc] at e

section Generic

variable {n : Nat} [Words n]

/-- The words of zero fit and write `0`. -/
theorem zero_spec : Fits n (Words.word (Words.zero : Words.W n)) 0 ∧
    num n (Words.word (Words.zero : Words.W n)) 0 = 0 := by
  have h : ∀ i < n, Words.word (Words.zero : Words.W n) (0 + i) = (fun _ => 0) (0 + i) :=
    fun i _ => Words.word_zero _
  rw [fits_congr (g := fun _ => 0) (k := 0) h, num_congr (g := fun _ => 0) (k := 0) h]
  refine ⟨fits_of_lt fun _ _ => by decide, ?_⟩
  clear h
  have hz (m k : Nat) : num m (fun _ => 0) k = 0 := by
    induction m generalizing k with
    | zero => rfl
    | succ m ih => rw [num_succ, ih]; rfl
  exact hz n 0

/-- Loaded words are the words read. -/
theorem load_spec (a : Nat → UInt64) (k : Nat) :
    (Fits n (Words.word (Words.load (n := n) a k)) 0 ↔ Fits n a k) ∧
      num n (Words.word (Words.load (n := n) a k)) 0 = num n a k := by
  have h : ∀ i < n, Words.word (Words.load (n := n) a k) (0 + i) = a (k + i) :=
    fun i hi => by rw [Nat.zero_add]; exact Words.word_load _ _ _ hi
  exact ⟨fits_congr h, num_congr h⟩

/-- The integer of `n` limbs, mod `2 ^ 32`, is the integer of its low limb. -/
theorem num_mod {f : Nat → UInt64} {k : Nat} (hn : 0 < n) (h : Fits n f k) :
    num n f k % 2 ^ 32 = (f k).toNat := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [num_succ]
  have := h.1
  omega

/-- `2 ^ (32 n)` is a multiple of `2 ^ 32` for `n > 0`. -/
theorem radix_mod (hn : 0 < n) : ∃ q, 2 ^ (32 * n) = 2 ^ 32 * q := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ⟨_, radix_succ m⟩

private theorem low_zero {m x y z : Nat} (hm : m = x * y % 2 ^ 32)
    (h : (z * y + 1) % 2 ^ 32 = 0) : (x + m * z) % 2 ^ 32 = 0 := by
  subst hm
  rw [Nat.add_mod, Nat.mod_mul_mod, ← Nat.add_mod, Nat.mul_assoc, Nat.mul_comm y z]
  have : x + x * (z * y) = x * (z * y + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
  rw [this, Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]

/-! ## The product -/

/-- One CIOS step: `(t + a b_i + m p) / 2 ^ 32`, as the low words and the word above them.

`m` is the multiple of `p` that makes the low word of the sum zero. -/
@[inline] def step (p : Nat → UInt64) (pinv : UInt64) (a b : Nat → UInt64) (i : Nat)
    (st : Words.W n × UInt64) : Words.W n × UInt64 :=
  let r := Words.mac st.1 a (b i) 0 0
  let m := (Words.word r.1 0 * pinv) &&& 0xFFFFFFFF
  Words.red r.1 p m (st.2 + r.2)

/-- The integer of words and the word above them. -/
def value (st : Words.W n × UInt64) : Nat :=
  num n (Words.word st.1) 0 + 2 ^ (32 * n) * st.2.toNat

/-- A modulus with an inverse mod `2 ^ 32` is positive. -/
theorem pos_of_pinv {P : Nat} {pinv : UInt64} (hpinv : (P * pinv.toNat + 1) % 2 ^ 32 = 0) :
    0 < P := by
  rcases Nat.eq_zero_or_pos P with h | h
  · rw [h, Nat.zero_mul] at hpinv
    exact absurd hpinv (by decide)
  · exact h

/-- One CIOS step adds `a b_i` and a multiple of `p`, divides by `2 ^ 32`, and stays below `2 p`. -/
theorem step_spec {p : Nat → UInt64} {pinv : UInt64} (hp : Fits n p 0)
    (hpinv : (num n p 0 * pinv.toNat + 1) % 2 ^ 32 = 0) {a : Nat → UInt64} (ha : Fits n a 0)
    (hA : num n a 0 < num n p 0) (b : Nat → UInt64) {i : Nat} (hb : (b i).toNat < 2 ^ 32)
    {st : Words.W n × UInt64} (ht : Fits n (Words.word st.1) 0)
    (hv : value st < 2 * num n p 0) :
    Fits n (Words.word (step p pinv a b i st).1) 0 ∧ value (step p pinv a b i st) < 2 * num n p 0 ∧
      ∃ m, 2 ^ 32 * value (step p pinv a b i st) = value st + num n a 0 * (b i).toNat +
        m * num n p 0 := by
  have hP := pos_of_pinv hpinv
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      exact absurd hP (by simp [num])
    · exact h
  have hR := num_lt hp
  have z : (0 : UInt64).toNat < 2 ^ 32 := by decide
  obtain ⟨fr, cr, er⟩ := Words.mac_spec st.1 a (b i) 0 0 ht ha hb z
  have hst : st.2.toNat < 2 := by
    simp only [value] at hv
    have : 2 ^ (32 * n) * st.2.toNat < 2 ^ (32 * n) * 2 := by
      rw [Nat.mul_comm _ 2]
      omega
    exact Nat.lt_of_mul_lt_mul_left this
  have htop : (st.2 + (Words.mac st.1 a (b i) 0 0).2).toNat =
      st.2.toNat + (Words.mac st.1 a (b i) 0 0).2.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hm : ((Words.word (Words.mac st.1 a (b i) 0 0).1 0 * pinv) &&& 0xFFFFFFFF).toNat =
      (Words.word (Words.mac st.1 a (b i) 0 0).1 0).toNat * pinv.toNat % 2 ^ 32 := by
    have hk : (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 := rfl
    rw [UInt64.toNat_and, hk, Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_mul,
      Nat.mod_mod_of_dvd _ (by decide)]
  generalize hmd : (Words.word (Words.mac st.1 a (b i) 0 0).1 0 * pinv) &&& 0xFFFFFFFF = m at hm
  have hml : m.toNat < 2 ^ 32 := hm ▸ Nat.mod_lt _ (by decide)
  have hlow := low_zero hm hpinv
  have h0 := num_mod hn fr
  obtain ⟨q, hq⟩ := radix_mod (n := n) hn
  have hsum : (num n (Words.word (Words.mac st.1 a (b i) 0 0).1) 0 + m.toNat * num n p 0 +
      2 ^ (32 * n) * (st.2 + (Words.mac st.1 a (b i) 0 0).2).toNat) % 2 ^ 32 = 0 := by
    rw [hq, Nat.mul_assoc, Nat.add_mul_mod_self_left]
    omega
  obtain ⟨fs, cs, es⟩ := Words.red_spec _ p m _ fr hp hml (by omega) hsum
  simp only [step]
  rw [hmd]
  refine ⟨fs, ?_, ⟨m.toNat, ?_⟩⟩
  · have hb1 : num n a 0 * (b i).toNat ≤ num n p 0 * (2 ^ 32 - 1) :=
      Nat.mul_le_mul (Nat.le_of_lt hA) (by omega)
    have hb2 : m.toNat * num n p 0 ≤ (2 ^ 32 - 1) * num n p 0 := Nat.mul_le_mul_right _ (by omega)
    simp only [value, UInt64.toNat_zero, Nat.add_zero] at *
    rw [htop, Nat.mul_add (2 ^ (32 * n))] at es
    omega
  · simp only [value, UInt64.toNat_zero, Nat.add_zero] at *
    rw [htop, Nat.mul_add (2 ^ (32 * n))] at es
    omega

/-- `x - p` when `x ≥ p`, else `x`, for `x < 2 p` given as words and the word above them. -/
@[inline] def reduce (p : Nat → UInt64) (t : Words.W n) (top : UInt64) {β : Type}
    (out : Words.W n → β) : β :=
  let d := Words.subb t p 0 0
  -- The borrow exceeds the top word exactly when `x < p`.
  if top < d.2 then out t else out d.1

/-- The final reduction hands its result to its continuation. -/
theorem reduce_out (p : Nat → UInt64) (t : Words.W n) (top : UInt64) {β : Type}
    (out : Words.W n → β) : reduce p t top out = out (reduce p t top id) := by
  unfold reduce
  dsimp only
  split <;> rfl

/-- The final reduction gives the integer mod `p`. -/
theorem reduce_spec {p : Nat → UInt64} (hp : Fits n p 0) {t : Words.W n} {top : UInt64}
    (ht : Fits n (Words.word t) 0) (hv : value (t, top) < 2 * num n p 0) :
    Fits n (Words.word (reduce p t top id)) 0 ∧
      num n (Words.word (reduce p t top id)) 0 = value (t, top) % num n p 0 := by
  have z : (0 : UInt64).toNat ≤ 1 := by decide
  obtain ⟨fd, bd, ed⟩ := Words.subb_spec t p 0 0 ht hp z
  have hR := num_lt hp
  have hRt := num_lt ht
  have hRd := num_lt fd
  simp only [value, UInt64.toNat_zero, Nat.add_zero] at hv ed
  have htop : top.toNat < 2 := by
    have : 2 ^ (32 * n) * top.toNat < 2 ^ (32 * n) * 2 := by
      rw [Nat.mul_comm _ 2]
      omega
    exact Nat.lt_of_mul_lt_mul_left this
  unfold reduce
  simp only [value, id]
  generalize Words.subb t p 0 0 = d at *
  generalize 2 ^ (32 * n) = R at *
  have hb : d.2.toNat = 0 ∨ d.2.toNat = 1 := by omega
  have ht' : top.toNat = 0 ∨ top.toNat = 1 := by omega
  split
  · rename_i h
    have h' : top.toNat < d.2.toNat := h
    refine ⟨ht, ?_⟩
    rcases hb with hb | hb <;> rcases ht' with ht' | ht' <;> simp only [hb, ht'] at * <;>
      first | omega | (rw [Nat.mod_eq_of_lt (by omega)]; omega)
  · rename_i h
    have h' : ¬ top.toNat < d.2.toNat := h
    refine ⟨fd, ?_⟩
    rcases hb with hb | hb <;> rcases ht' with ht' | ht' <;> simp only [hb, ht'] at * <;>
      first | omega | (rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega)

/-- The CIOS product `a b 2 ^ (-32 n)` mod `p`, reduced, given to `out`. -/
@[inline] def mulWords (p : Nat → UInt64) (pinv : UInt64) (a b : Nat → UInt64) {β : Type}
    (out : Words.W n → β) : β :=
  let st := Words.fold (n := n) (step p pinv a b) 0 (Words.zero, 0)
  reduce p st.1 st.2 out

/-- The product hands its result to its continuation. -/
theorem mulWords_out (p : Nat → UInt64) (pinv : UInt64) (a b : Nat → UInt64) {β : Type}
    (out : Words.W n → β) : mulWords p pinv a b out = out (mulWords p pinv a b id) :=
  reduce_out _ _ _ _

/-- The CIOS product is `a b R⁻¹` mod `p`, below `p`, with `R = 2 ^ (32 n)`. -/
theorem mulWords_spec {p : Nat → UInt64} {pinv : UInt64} (hp : Fits n p 0)
    (hpinv : (num n p 0 * pinv.toNat + 1) % 2 ^ 32 = 0) {a : Nat → UInt64} (ha : Fits n a 0)
    (hA : num n a 0 < num n p 0) {b : Nat → UInt64} (hb : Fits n b 0) :
    Fits n (Words.word (mulWords (n := n) p pinv a b id)) 0 ∧
      num n (Words.word (mulWords (n := n) p pinv a b id)) 0 < num n p 0 ∧
      2 ^ (32 * n) * num n (Words.word (mulWords (n := n) p pinv a b id)) 0 % num n p 0 =
        num n a 0 * num n b 0 % num n p 0 := by
  have hP := pos_of_pinv hpinv
  have hbi := lt_of_fits hb
  let Inv (i : Nat) (st : Words.W n × UInt64) : Prop :=
    Fits n (Words.word st.1) 0 ∧ value st < 2 * num n p 0 ∧
      ∃ K, 2 ^ (32 * i) * value st = num n a 0 * num i b 0 + K * num n p 0
  have hinv : Inv (0 + n) (loop n (step p pinv a b) 0 (Words.zero, 0)) := by
    apply loop_induct
    · refine ⟨zero_spec.1, ?_, 0, ?_⟩
      · simp only [value, zero_spec.2, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]
        omega
      · simp [value, zero_spec.2, num]
    · intro i st _ hi ⟨hf, hv, K, hK⟩
      obtain ⟨fs, vs, m, es⟩ := step_spec hp hpinv ha hA b (i := i)
        (by have := hbi i (by omega); rwa [Nat.zero_add] at this) hf hv
      refine ⟨fs, vs, K + 2 ^ (32 * i) * m, ?_⟩
      rw [radix_succ, num_snoc, Nat.zero_add, Nat.mul_assoc, Nat.mul_left_comm, es]
      generalize value (step p pinv a b i st) = V' at *
      generalize 2 ^ (32 * i) = X at *
      grind
  rw [Nat.zero_add] at hinv
  obtain ⟨hf, hv, K, hK⟩ := hinv
  unfold mulWords
  rw [Words.fold_eq]
  generalize loop n (step p pinv a b) 0 ((Words.zero : Words.W n), 0) = st at *
  obtain ⟨fr, er⟩ := reduce_spec hp hf hv
  refine ⟨fr, ?_, ?_⟩
  · rw [er]
    exact Nat.mod_lt _ hP
  · rw [er, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, hK, Nat.add_mul_mod_self_right]

/-- Whether the integer of the words `t` is below that of the words `p`: `t - p` borrows. -/
@[inline] def ltWords (t : Words.W n) (p : Nat → UInt64) : Bool :=
  (Words.subb t p 0 0).2 != 0

/-- The comparison of words is the comparison of their integers. -/
theorem ltWords_iff {t : Words.W n} {p : Nat → UInt64} (ht : Fits n (Words.word t) 0)
    (hp : Fits n p 0) : ltWords t p = true ↔ num n (Words.word t) 0 < num n p 0 := by
  have z : (0 : UInt64).toNat ≤ 1 := by decide
  obtain ⟨fd, bd, ed⟩ := Words.subb_spec t p 0 0 ht hp z
  have := num_lt fd
  have := num_lt ht
  have := num_lt hp
  simp only [ltWords, bne_iff_ne, ne_eq, UInt64.toNat_zero, Nat.add_zero] at ed ⊢
  rw [← UInt64.toNat_inj, UInt64.toNat_zero]
  generalize Words.subb t p 0 0 = d at *
  generalize 2 ^ (32 * n) = R at *
  have hb : d.2.toNat = 0 ∨ d.2.toNat = 1 := by omega
  rcases hb with hb | hb <;> rw [hb] at ed ⊢ <;> simp only [Nat.mul_zero, Nat.mul_one] at ed <;>
    omega

/-! ## Stored limbs -/

/-- `n` limbs of 32 bits, as an element stores them.

A structure of `n` fields of 32 bits takes one allocation and no work to free. -/
class Limbs (n : Nat) [Words n] where
  /-- The stored limbs. -/
  T : Type
  /-- The limb at an index, and `0` past the last. -/
  get : T → Nat → UInt64
  /-- The low 32 bits of each word. -/
  pack : Words.W n → T
  /-- Equality of stored limbs. -/
  decEq : DecidableEq T
  /-- Each limb is below `2 ^ 32`. -/
  get_lt : ∀ a k, (get a k).toNat < 2 ^ 32
  /-- The stored limbs are the low 32 bits of the words. -/
  get_pack : ∀ t k, k < n → (get (pack t) k).toNat = (Words.word t k).toNat % 2 ^ 32
  /-- Stored limbs with the same limbs are equal. -/
  ext : ∀ a b, (∀ k < n, get a k = get b k) → a = b

/-- Stored limbs compare field by field. -/
instance [Limbs n] : DecidableEq (Limbs.T n) := Limbs.decEq

namespace Limbs

variable [Limbs n]

/-- The integer that the limbs write. -/
def val (a : T n) : Nat := num n (get a) 0

/-- Stored limbs fit. -/
theorem fits (a : T n) (k : Nat) : Fits n (get a) k := fits_of_lt fun _ _ => get_lt a _

/-- The integer of the limbs is below `2 ^ (32 n)`. -/
theorem val_lt (a : T n) : val a < 2 ^ (32 * n) := num_lt (fits a 0)

/-- The limbs of fitting words write their integer. -/
theorem val_pack {t : Words.W n} (h : Fits n (Words.word t) 0) :
    val (pack (n := n) t) = num n (Words.word t) 0 := by
  have hl := lt_of_fits h
  refine num_congr fun i hi => UInt64.toNat_inj.mp ?_
  rw [get_pack _ _ (by omega), Nat.mod_eq_of_lt (hl i hi)]

/-- Limbs with the same integer are equal. -/
theorem val_injective : Function.Injective (val : T n → Nat) := by
  intro a b h
  apply ext
  intro k hk
  simpa using eq_of_num_eq (fits a 0) (fits b 0) h k hk

/-- The digits of `x` in base `2 ^ 32`. -/
@[inline] def digit (x : Nat) (i : Nat) : UInt64 := (x / 2 ^ (32 * i) % 2 ^ 32).toUInt64

/-- A digit is the integer of 32 bits at its place. -/
theorem digit_toNat (x i : Nat) : (digit x i).toNat = x / 2 ^ (32 * i) % 2 ^ 32 := by
  have := Nat.mod_lt (x / 2 ^ (32 * i)) (Nat.two_pow_pos 32)
  rw [digit, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

/-- The digits of `x` from place `k` write `x / 2 ^ (32 k)` mod `2 ^ (32 m)`. -/
theorem num_digit (x : Nat) (m k : Nat) : num m (digit x) k = x / 2 ^ (32 * k) % 2 ^ (32 * m) := by
  induction m generalizing k with
  | zero => simp [num, Nat.mod_one]
  | succ m ih =>
    rw [num_succ, ih, radix_succ m, Nat.mod_mul, radix_succ k, Nat.mul_comm (2 ^ 32) (2 ^ (32 * k)),
      ← Nat.div_div_eq_div_mul, digit_toNat]

/-- The digits fit. -/
theorem fits_digit (x : Nat) (m k : Nat) : Fits m (digit x) k :=
  fits_of_lt fun _ _ => by
    rw [digit_toNat]
    exact Nat.mod_lt _ (by decide)

/-- The limbs of `x mod 2 ^ (32 n)`. -/
@[inline] def ofNat (x : Nat) : T n :=
  pack (Words.load (n := n) (digit x) 0)

/-- The limbs of `x` write `x mod 2 ^ (32 n)`. -/
theorem val_ofNat (x : Nat) : val (ofNat (n := n) x) = x % 2 ^ (32 * n) := by
  rw [ofNat, val_pack ((load_spec _ _).1.mpr (fits_digit x n 0)), (load_spec _ _).2, num_digit]
  simp

end Limbs

/-! ## The product in two parts -/

section Parts

/-- Zeros load as the words of zero. -/
theorem load_zero : Words.load (n := n) (fun _ => 0) 0 = Words.zero :=
  Words.ext _ _ fun i hi => by rw [Words.word_load _ _ _ hi, Words.word_zero]

variable [Limbs n]

/-- `m` rows of the CIOS product from row `k`, from the words `acc` with `0` above them. -/
@[inline] def mulRows (m : Nat) [Words m] (p : Nat → UInt64) (pinv : UInt64) (a b : Nat → UInt64)
    (k : Nat) (acc : Nat → UInt64) : Words.W n × UInt64 :=
  Words.fold (n := m) (step p pinv a b) k (Words.load (n := n) acc 0, 0)

/-- The first `k` rows of the CIOS product, as stored limbs.

The word above them is `0` when `2 p ≤ R`, so the limbs hold the whole state. -/
@[inline] def mulLow (k : Nat) [Words k] (p : Nat → UInt64) (pinv : UInt64)
    (a b : Nat → UInt64) : Limbs.T n :=
  Limbs.pack (mulRows (n := n) k p pinv a b 0 fun _ => 0).1

/-- The rows of the CIOS product from row `k`, from the limbs `lo` of the rows before them.

The final reduction follows, and its result goes to `out`. -/
@[inline] def mulHigh (m : Nat) [Words m] (p : Nat → UInt64) (pinv : UInt64) (a b : Nat → UInt64)
    (k : Nat) (lo : Limbs.T n) {β : Type} (out : Words.W n → β) : β :=
  let st := mulRows (n := n) m p pinv a b k (Limbs.get lo)
  reduce p st.1 st.2 out

/-- Fitting words, stored as limbs and loaded back, are the same words. -/
theorem load_pack {t : Words.W n} (h : Fits n (Words.word t) 0) :
    Words.load (n := n) (Limbs.get (Limbs.pack (n := n) t)) 0 = t := by
  have hl := lt_of_fits h
  refine Words.ext _ _ fun i hi => UInt64.toNat_inj.mp ?_
  rw [Words.word_load _ _ _ hi, Nat.zero_add, Limbs.get_pack _ _ hi,
    Nat.mod_eq_of_lt (by simpa using hl i hi)]

/-- The product in two parts is the CIOS product, when `2 p ≤ R`.

The rows keep the state below `2 p`, so the word above the limbs of the first part is `0`. -/
theorem mulHigh_mulLow {k m : Nat} [Words k] [Words m] (hkm : k + m = n) {p : Nat → UInt64}
    {pinv : UInt64} (hp : Fits n p 0) (hpinv : (num n p 0 * pinv.toNat + 1) % 2 ^ 32 = 0)
    (hR : 2 * num n p 0 ≤ 2 ^ (32 * n)) {a : Nat → UInt64} (ha : Fits n a 0)
    (hA : num n a 0 < num n p 0) {b : Nat → UInt64} (hb : Fits n b 0) {β : Type}
    (out : Words.W n → β) :
    mulHigh m p pinv a b k (mulLow (n := n) k p pinv a b) out = mulWords p pinv a b out := by
  have hbi := lt_of_fits hb
  have hlow := loop_induct (fun _ st => Fits n (Words.word st.1) 0 ∧ value st < 2 * num n p 0)
    (step p pinv a b) k 0 ((Words.zero : Words.W n), 0) ⟨zero_spec.1, by
      simp only [value, zero_spec.2, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]
      have := pos_of_pinv hpinv
      omega⟩ fun i st _ hi ⟨hf, hv⟩ => by
      obtain ⟨fs, vs, _⟩ := step_spec hp hpinv ha hA b (i := i)
        (by have := hbi i (by omega); rwa [Nat.zero_add] at this) hf hv
      exact ⟨fs, vs⟩
  have e := loop_add (step p pinv a b) k m 0 ((Words.zero : Words.W n), 0)
  rw [hkm, Nat.zero_add] at e
  unfold mulHigh mulLow mulRows mulWords
  rw [load_zero, Words.fold_eq, Words.fold_eq, Words.fold_eq, e]
  generalize loop k (step p pinv a b) 0 ((Words.zero : Words.W n), 0) = st at hlow ⊢
  obtain ⟨hf, hv⟩ := hlow
  have htop : st.2 = 0 := by
    simp only [value] at hv
    have : 2 ^ (32 * n) * st.2.toNat < 2 ^ (32 * n) * 1 := by omega
    exact UInt64.toNat_inj.mp (Nat.lt_one_iff.mp (Nat.lt_of_mul_lt_mul_left this))
  rw [load_pack hf, show ((st.1, 0) : Words.W n × UInt64) = st from Prod.ext rfl htop.symm]

end Parts

end Generic

/-! ## Eight limbs -/

/-- An integer below `2 ^ 256`, as 8 limbs of 32 bits, the lowest first. -/
structure Limbs8 where
  l0 : UInt32
  l1 : UInt32
  l2 : UInt32
  l3 : UInt32
  l4 : UInt32
  l5 : UInt32
  l6 : UInt32
  l7 : UInt32
deriving DecidableEq, Inhabited

/-- The limb at an index, and `0` past the last. -/
@[inline] def Limbs8.get (a : Limbs8) : Nat → UInt64
  | 0 => a.l0.toUInt64
  | 1 => a.l1.toUInt64
  | 2 => a.l2.toUInt64
  | 3 => a.l3.toUInt64
  | 4 => a.l4.toUInt64
  | 5 => a.l5.toUInt64
  | 6 => a.l6.toUInt64
  | 7 => a.l7.toUInt64
  | _ => 0

/-- Eight limbs, stored in a structure of eight fields. -/
instance : Limbs 8 where
  T := Limbs8
  get := Limbs8.get
  pack t := ⟨t.1.toUInt32, t.2.1.toUInt32, t.2.2.1.toUInt32, t.2.2.2.1.toUInt32,
    t.2.2.2.2.1.toUInt32, t.2.2.2.2.2.1.toUInt32, t.2.2.2.2.2.2.1.toUInt32,
    t.2.2.2.2.2.2.2.1.toUInt32⟩
  decEq := inferInstanceAs (DecidableEq Limbs8)
  get_lt a k := by
    unfold Limbs8.get
    split <;> first | exact UInt32.toNat_lt _ | decide
  get_pack t k hk := by
    have e (x : UInt64) : x.toUInt32.toUInt64.toNat = x.toNat % 2 ^ 32 := by
      rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
    match k, hk with
    | 0, _ => exact e _
    | 1, _ => exact e _
    | 2, _ => exact e _
    | 3, _ => exact e _
    | 4, _ => exact e _
    | 5, _ => exact e _
    | 6, _ => exact e _
    | 7, _ => exact e _
  ext a b h := by
    have g (k : Nat) (hk : k < 8) := h k hk
    cases a
    cases b
    simp only [Limbs8.mk.injEq]
    exact ⟨UInt32.toUInt64_inj.mp (g 0 (by decide)), UInt32.toUInt64_inj.mp (g 1 (by decide)),
      UInt32.toUInt64_inj.mp (g 2 (by decide)), UInt32.toUInt64_inj.mp (g 3 (by decide)),
      UInt32.toUInt64_inj.mp (g 4 (by decide)), UInt32.toUInt64_inj.mp (g 5 (by decide)),
      UInt32.toUInt64_inj.mp (g 6 (by decide)), UInt32.toUInt64_inj.mp (g 7 (by decide))⟩

/-! ## Twelve limbs -/

/-- An integer below `2 ^ 384`, as 12 limbs of 32 bits, the lowest first. -/
structure Limbs12 where
  l0 : UInt32
  l1 : UInt32
  l2 : UInt32
  l3 : UInt32
  l4 : UInt32
  l5 : UInt32
  l6 : UInt32
  l7 : UInt32
  l8 : UInt32
  l9 : UInt32
  l10 : UInt32
  l11 : UInt32
deriving DecidableEq, Inhabited

/-- The limb at an index, and `0` past the last. -/
@[inline] def Limbs12.get (a : Limbs12) : Nat → UInt64
  | 0 => a.l0.toUInt64
  | 1 => a.l1.toUInt64
  | 2 => a.l2.toUInt64
  | 3 => a.l3.toUInt64
  | 4 => a.l4.toUInt64
  | 5 => a.l5.toUInt64
  | 6 => a.l6.toUInt64
  | 7 => a.l7.toUInt64
  | 8 => a.l8.toUInt64
  | 9 => a.l9.toUInt64
  | 10 => a.l10.toUInt64
  | 11 => a.l11.toUInt64
  | _ => 0

/-- Twelve limbs, stored in a structure of twelve fields. -/
instance : Limbs 12 where
  T := Limbs12
  get := Limbs12.get
  pack t := ⟨t.1.toUInt32, t.2.1.toUInt32, t.2.2.1.toUInt32, t.2.2.2.1.toUInt32,
    t.2.2.2.2.1.toUInt32, t.2.2.2.2.2.1.toUInt32, t.2.2.2.2.2.2.1.toUInt32,
    t.2.2.2.2.2.2.2.1.toUInt32, t.2.2.2.2.2.2.2.2.1.toUInt32,
    t.2.2.2.2.2.2.2.2.2.1.toUInt32, t.2.2.2.2.2.2.2.2.2.2.1.toUInt32,
    t.2.2.2.2.2.2.2.2.2.2.2.1.toUInt32⟩
  decEq := inferInstanceAs (DecidableEq Limbs12)
  get_lt a k := by
    unfold Limbs12.get
    split <;> first | exact UInt32.toNat_lt _ | decide
  get_pack t k hk := by
    have e (x : UInt64) : x.toUInt32.toUInt64.toNat = x.toNat % 2 ^ 32 := by
      rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
    match k, hk with
    | 0, _ => exact e _
    | 1, _ => exact e _
    | 2, _ => exact e _
    | 3, _ => exact e _
    | 4, _ => exact e _
    | 5, _ => exact e _
    | 6, _ => exact e _
    | 7, _ => exact e _
    | 8, _ => exact e _
    | 9, _ => exact e _
    | 10, _ => exact e _
    | 11, _ => exact e _
  ext a b h := by
    have g (k : Nat) (hk : k < 12) := h k hk
    cases a
    cases b
    simp only [Limbs12.mk.injEq]
    exact ⟨UInt32.toUInt64_inj.mp (g 0 (by decide)), UInt32.toUInt64_inj.mp (g 1 (by decide)),
      UInt32.toUInt64_inj.mp (g 2 (by decide)), UInt32.toUInt64_inj.mp (g 3 (by decide)),
      UInt32.toUInt64_inj.mp (g 4 (by decide)), UInt32.toUInt64_inj.mp (g 5 (by decide)),
      UInt32.toUInt64_inj.mp (g 6 (by decide)), UInt32.toUInt64_inj.mp (g 7 (by decide)),
      UInt32.toUInt64_inj.mp (g 8 (by decide)), UInt32.toUInt64_inj.mp (g 9 (by decide)),
      UInt32.toUInt64_inj.mp (g 10 (by decide)), UInt32.toUInt64_inj.mp (g 11 (by decide))⟩

/-! ## The modulus -/

section Core

variable {n : Nat} [Words n] [Limbs n]

/-- The Montgomery product of the limbs `a` and `b`, for the modulus of limbs `p`.

The compiler makes one copy for each limb count, with the code unrolled. -/
@[specialize] def mulCore (a b : Limbs.T n) (p : @& Limbs.T n) (pinv : UInt64) : Limbs.T n :=
  mulWords (Limbs.get p) pinv (Limbs.get a) (Limbs.get b) Limbs.pack

/-- The product of the limbs is the CIOS product. -/
theorem mulCore_eq (a b : Limbs.T n) (p : Limbs.T n) (pinv : UInt64) :
    mulCore a b p pinv = mulWords (Limbs.get p) pinv (Limbs.get a) (Limbs.get b) Limbs.pack := rfl

end Core

/-- An odd modulus `p` below `R = 2 ^ (32 n)`, with the constants of its Montgomery arithmetic.

The limbs of `p` are stored like the limbs of an element, so the code reads each one as a field. -/
structure Modulus (n : Nat) [Words n] [Limbs n] where
  /-- The modulus. -/
  p : Nat
  /-- The limbs of the modulus. -/
  pLimbs : Limbs.T n
  /-- `-p⁻¹ mod 2 ^ 32`. -/
  pinv : UInt64
  /-- `R mod p`, the form of `1`. -/
  r1 : Limbs.T n
  /-- `R ^ 2 mod p`, which puts an integer into Montgomery form. -/
  r2 : Limbs.T n
  /-- `p - 2`, the exponent of the inverse. -/
  pm2 : Limbs.T n
  /-- The limbs write the modulus. -/
  pLimbs_spec : Limbs.val pLimbs = p
  /-- `p pinv = -1` mod `2 ^ 32`. -/
  pinv_spec : (p * pinv.toNat + 1) % 2 ^ 32 = 0
  /-- The form of `1`. -/
  r1_spec : Limbs.val r1 = 2 ^ (32 * n) % p
  /-- The constant that puts an integer into Montgomery form. -/
  r2_spec : Limbs.val r2 = 2 ^ (32 * n) * 2 ^ (32 * n) % p
  /-- The exponent of the inverse. -/
  pm2_spec : Limbs.val pm2 = p - 2
  /-- The Montgomery product of the limbs `a`, below `p`, and `b`.

  By default it is the CIOS product, unrolled whole. -/
  mul : Limbs.T n → Limbs.T n → Limbs.T n := fun a b => mulCore a b pLimbs pinv
  /-- The product is the CIOS product. -/
  mul_spec : ∀ a b, Limbs.val a < p →
      mul a b = mulWords (Limbs.get pLimbs) pinv (Limbs.get a) (Limbs.get b) Limbs.pack := by
    intros
    exact EthLib.Cryptography.Montgomery.mulCore_eq ..

end Montgomery

open Montgomery in
/-- An integer mod `M.p` in Montgomery form.

The limbs hold `a R mod p` for the integer `a` that the element stands for.

They are below `p`, so each element has exactly one form. -/
structure Montgomery {n : Nat} [Words n] [Limbs n] (M : Modulus n) where
  /-- `a R mod p`. -/
  limbs : Limbs.T n
  /-- The form is below `p`. -/
  lt : Limbs.val limbs < M.p
deriving DecidableEq

namespace Montgomery

variable {n : Nat} [Words n] [Limbs n] {M : Modulus n}

/-- The limbs of the modulus fit. -/
theorem Modulus.fits (M : Modulus n) : Fits n (Limbs.get M.pLimbs) 0 :=
  Limbs.fits M.pLimbs 0

/-- The limbs of the modulus write it. -/
theorem Modulus.num_eq (M : Modulus n) : num n (Limbs.get M.pLimbs) 0 = M.p := M.pLimbs_spec

/-- The modulus is positive. -/
theorem Modulus.pos (M : Modulus n) : 0 < M.p := pos_of_pinv M.pinv_spec

/-- `R mod p` is below `p`. -/
theorem Modulus.r1_lt (M : Modulus n) : Limbs.val M.r1 < M.p := by
  rw [M.r1_spec]
  exact Nat.mod_lt _ M.pos

/-- `R ^ 2 mod p` is below `p`. -/
theorem Modulus.r2_lt (M : Modulus n) : Limbs.val M.r2 < M.p := by
  rw [M.r2_spec]
  exact Nat.mod_lt _ M.pos

/-- The Montgomery product of the limbs `a`, below `p`, and `b`. -/
theorem mulLimbs_spec (M : Modulus n) (a : Limbs.T n) (ha : Limbs.val a < M.p) (b : Limbs.T n) :
    Limbs.val (n := n)
        (mulWords (Limbs.get M.pLimbs) M.pinv (Limbs.get a) (Limbs.get b) Limbs.pack) < M.p ∧
      2 ^ (32 * n) * Limbs.val (n := n)
          (mulWords (Limbs.get M.pLimbs) M.pinv (Limbs.get a) (Limbs.get b) Limbs.pack) % M.p =
        Limbs.val a * Limbs.val b % M.p := by
  obtain ⟨hf, hl, he⟩ := mulWords_spec M.fits (by rw [M.num_eq]; exact M.pinv_spec)
    (Limbs.fits a 0) (by rw [M.num_eq]; exact ha) (Limbs.fits b 0)
  rw [mulWords_out, Limbs.val_pack hf]
  rw [M.num_eq] at hl he
  exact ⟨hl, he⟩

/-- The Montgomery product of `a`, below `p`, and `b`: `a b R⁻¹ mod p`. -/
@[inline] def mulLimbs (M : Modulus n) (a : Limbs.T n) (ha : Limbs.val a < M.p) (b : Limbs.T n) :
    Montgomery M :=
  ⟨M.mul a b, by rw [M.mul_spec a b ha]; exact (mulLimbs_spec M a ha b).1⟩

/-- Zero. -/
@[inline] def zero : Montgomery M :=
  ⟨Limbs.pack Words.zero, by rw [Limbs.val_pack zero_spec.1, zero_spec.2]; exact M.pos⟩

@[inline] instance : Inhabited (Montgomery M) := ⟨zero⟩

/-- One, whose form is `R mod p`. -/
@[inline] def one : Montgomery M :=
  ⟨M.r1, M.r1_lt⟩

/-- The sum of the limbs `a` and `b`, below `p`, is `a + b mod p`. -/
theorem addLimbs_spec (M : Modulus n) (a b : Limbs.T n) (ha : Limbs.val a < M.p)
    (hb : Limbs.val b < M.p) :
    Limbs.val (n := n) (reduce (Limbs.get M.pLimbs)
        (Words.mac (Words.load (n := n) (Limbs.get a) 0) (Limbs.get b) 1 0 0).1
        (Words.mac (Words.load (n := n) (Limbs.get a) 0) (Limbs.get b) 1 0 0).2 Limbs.pack) =
      (Limbs.val a + Limbs.val b) % M.p := by
  have o : (1 : UInt64).toNat < 2 ^ 32 := by decide
  have z : (0 : UInt64).toNat < 2 ^ 32 := by decide
  obtain ⟨fl, el⟩ := load_spec (n := n) (Limbs.get a) 0
  obtain ⟨fs, cs, es⟩ := Words.mac_spec _ (Limbs.get b) 1 0 0 (fl.mpr (Limbs.fits a 0))
    (Limbs.fits b 0) o z
  rw [el, UInt64.toNat_one, UInt64.toNat_zero, Nat.mul_one, Nat.add_zero] at es
  have hv : value (Words.mac (Words.load (n := n) (Limbs.get a) 0) (Limbs.get b) 1 0 0) <
      2 * num n (Limbs.get M.pLimbs) 0 := by
    simp only [value, M.num_eq]
    unfold Limbs.val at ha hb
    omega
  obtain ⟨fr, er⟩ := reduce_spec M.fits
    (top := (Words.mac (Words.load (n := n) (Limbs.get a) 0) (Limbs.get b) 1 0 0).2) fs hv
  rw [reduce_out, Limbs.val_pack fr, er, M.num_eq]
  simp only [value]
  unfold Limbs.val
  rw [es]

/-- The sum of the limbs `a` and `b`, reduced once by the modulus of limbs `p`.

The compiler makes one copy for each limb count, with the code unrolled. -/
@[specialize] def addCore (a b : Limbs.T n) (p : @& Limbs.T n) : Limbs.T n :=
  let s := Words.mac (Words.load (n := n) (Limbs.get a) 0) (Limbs.get b) 1 0 0
  reduce (Limbs.get p) s.1 s.2 Limbs.pack

/-- `a + b mod p`. -/
@[inline] def add (a b : Montgomery M) : Montgomery M :=
  ⟨addCore a.limbs b.limbs M.pLimbs, by
    rw [addCore, addLimbs_spec M a.limbs b.limbs a.lt b.lt]
    exact Nat.mod_lt _ M.pos⟩

/-- `a - b` when `a ≥ b`, else `a - b + p`, for the limbs `a` and `b` and the limbs `p`.

The compiler makes one copy for each limb count, with the code unrolled. -/
@[specialize] def subCore (a b : Limbs.T n) (p : @& Limbs.T n) : Limbs.T n :=
  let d := Words.subb (Words.load (n := n) (Limbs.get a) 0) (Limbs.get b) 0 0
  if d.2 = 0 then Limbs.pack d.1 else Limbs.pack (Words.mac d.1 (Limbs.get p) 1 0 0).1

/-- `a - b` when `a ≥ b`, else `a - b + p`, for the limbs `a` and `b`. -/
@[inline] def subLimbs (M : Modulus n) (a b : Limbs.T n) : Limbs.T n :=
  subCore a b M.pLimbs

/-- The difference of the limbs `a` and `b` below `p` is `a - b` mod `p`. -/
theorem subLimbs_spec (M : Modulus n) {a b : Limbs.T n} (ha : Limbs.val a < M.p)
    (hb : Limbs.val b < M.p) :
    Limbs.val (subLimbs M a b) = (Limbs.val a + M.p - Limbs.val b) % M.p := by
  have z1 : (0 : UInt64).toNat ≤ 1 := by decide
  have o : (1 : UInt64).toNat < 2 ^ 32 := by decide
  have z : (0 : UInt64).toNat < 2 ^ 32 := by decide
  obtain ⟨fl, el⟩ := load_spec (n := n) (Limbs.get a) 0
  obtain ⟨fd, bd, ed⟩ := Words.subb_spec _ (Limbs.get b) 0 0 (fl.mpr (Limbs.fits a 0))
    (Limbs.fits b 0) z1
  rw [el, UInt64.toNat_zero, Nat.add_zero] at ed
  have hR := num_lt fd
  have hP := M.pos
  have hpR : M.p ≤ 2 ^ (32 * n) := by
    rw [← M.num_eq]
    exact Nat.le_of_lt (num_lt M.fits)
  unfold Limbs.val at ha hb ⊢
  unfold subLimbs subCore
  dsimp only
  split
  · rename_i h
    have h' : (Words.subb (Words.load (n := n) (Limbs.get a) 0) (Limbs.get b) 0 0).2.toNat = 0 :=
      by rw [h]; rfl
    rw [← Limbs.val, Limbs.val_pack fd]
    rw [h', Nat.mul_zero, Nat.add_zero] at ed
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · rename_i h
    have h' : (Words.subb (Words.load (n := n) (Limbs.get a) 0) (Limbs.get b) 0 0).2.toNat = 1 :=
      by
        have : (Words.subb (Words.load (n := n) (Limbs.get a) 0) (Limbs.get b) 0 0).2.toNat ≠ 0 :=
          fun h0 => h (UInt64.toNat_inj.mp h0)
        omega
    rw [h', Nat.mul_one] at ed
    obtain ⟨fs, cs, es⟩ := Words.mac_spec _ (Limbs.get M.pLimbs) 1 0 0 fd M.fits o z
    rw [UInt64.toNat_one, UInt64.toNat_zero, Nat.mul_one, Nat.add_zero, M.num_eq] at es
    rw [← Limbs.val, Limbs.val_pack fs]
    generalize Words.subb (Words.load (n := n) (Limbs.get a) 0) (Limbs.get b) 0 0 = d at *
    generalize Words.mac d.1 (Limbs.get M.pLimbs) 1 0 0 = s at *
    have hs := num_lt fs
    generalize 2 ^ (32 * n) = R at *
    have hc : s.2.toNat = 1 := by
      rcases Nat.lt_or_ge s.2.toNat 1 with h1 | h1
      · rw [show s.2.toNat = 0 by omega, Nat.mul_zero] at es
        omega
      · rcases Nat.lt_or_ge s.2.toNat 2 with h2 | h2
        · omega
        · have : R * 2 ≤ R * s.2.toNat := Nat.mul_le_mul_left _ h2
          omega
    rw [hc, Nat.mul_one] at es
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- `a - b mod p`. -/
@[inline] def sub (a b : Montgomery M) : Montgomery M :=
  ⟨subLimbs M a.limbs b.limbs, by
    rw [subLimbs_spec M a.lt b.lt]
    exact Nat.mod_lt _ M.pos⟩

/-- `-a mod p`. -/
@[inline] def neg (a : Montgomery M) : Montgomery M :=
  sub zero a

/-- `a b mod p`, by the Montgomery product of the two forms. -/
@[inline] def mul (a b : Montgomery M) : Montgomery M :=
  mulLimbs M a.limbs a.lt b.limbs

/-- The element that stands for `x mod p`.

The Montgomery product with `R ^ 2 mod p` turns `x` into `x R mod p`. -/
@[inline] def ofNat (x : Nat) : Montgomery M :=
  mulLimbs M M.r2 M.r2_lt (Limbs.ofNat (x % M.p))

/-- The integer of the words `f k` to `f (k + m - 1)`, two at a time.

Pairs halve the operations on large integers. -/
def numPairs (f : Nat → UInt64) : Nat → Nat → Nat
  | 0, _ => 0
  | 1, k => (f k).toNat
  | m + 2, k => (f k + (f (k + 1) <<< 32)).toNat + 2 ^ 64 * numPairs f m (k + 2)

/-- Two at a time, fitting words write their integer. -/
theorem numPairs_eq {f : Nat → UInt64} {m k : Nat} (h : Fits m f k) :
    numPairs f m k = num m f k := by
  induction m using Nat.strongRecOn generalizing k with
  | _ m ih =>
    match m, h with
    | 0, _ => rfl
    | 1, _ => simp [numPairs, num]
    | m + 2, h =>
      have h0 := h.1
      have h1 := h.2.1
      have hp : (f k + (f (k + 1) <<< 32)).toNat = (f k).toNat + 2 ^ 32 * (f (k + 1)).toNat := by
        rw [UInt64.toNat_add, UInt64.toNat_shiftLeft]
        simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      rw [numPairs, ih m (by omega) h.2.2, hp, num_succ, num_succ]
      omega

/-- The integer below `p` that the element stands for.

The Montgomery product with `1` turns `a R` into `a`. -/
@[inline] def toNat (a : Montgomery M) : Nat :=
  numPairs (Limbs.get (mulLimbs M a.limbs a.lt (Limbs.ofNat 1)).limbs) n 0

/-- The integer of an element is the integer of its product with `1`. -/
theorem toNat_eq_val (a : Montgomery M) :
    toNat a = Limbs.val (mulLimbs M a.limbs a.lt (Limbs.ofNat 1)).limbs :=
  numPairs_eq (Limbs.fits _ 0)

/-- `a ^ k`, by square and multiply.

The compiler makes one copy for each modulus, so each product is a direct call. -/
@[specialize M] def pow (a : Montgomery M) (k : Nat) : Montgomery M :=
  if k = 0 then one
  else
    let half := pow (mul a a) (k / 2)
    if k % 2 = 1 then mul a half else half
termination_by k
decreasing_by omega

/-- `t` followed by `k` new entries: `last * a`, `last * a ^ 2`, up to `last * a ^ k`.

When `last` is `a ^ m`, the new entries are `a ^ (m + 1)` to `a ^ (m + k)`.

The last power is an argument, so the builder never reads the array back.

The compiler makes one copy for each modulus, so each product is a direct call. -/
@[specialize M] def powTableAux (a : Montgomery M) :
    Nat → Montgomery M → Array (Montgomery M) → Array (Montgomery M)
  | 0, _, t => t
  | k + 1, last, t =>
    let next := mul last a
    powTableAux a k next (t.push next)

/-- Each product adds one entry. -/
theorem size_powTableAux (a : Montgomery M) :
    ∀ (k : Nat) (last : Montgomery M) (t : Array (Montgomery M)),
      (powTableAux a k last t).size = t.size + k
  | 0, _, _ => rfl
  | k + 1, last, t => by
    rw [powTableAux, size_powTableAux a k, Array.size_push]
    omega

/-- The powers `a ^ 0` to `a ^ 15`. -/
@[inline] def powTable (a : Montgomery M) : Vector (Montgomery M) 16 :=
  ⟨powTableAux a 15 one #[one], size_powTableAux a 15 one #[one]⟩

/-- `acc ^ 16 * a ^ d` for a digit `d` below 16, with the powers `t` of `a`. -/
@[inline] def window (t : Vector (Montgomery M) 16) (acc : Montgomery M) (d : UInt32)
    (digit : d.toNat < 16) : Montgomery M :=
  let s := mul acc acc
  let s := mul s s
  let s := mul s s
  let s := mul s s
  mul s t[d.toNat]

/-- The top four bits of a word are a digit below 16. -/
theorem topDigit_lt (w : UInt32) : (w >>> 28).toNat < 16 := by
  rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have := w.toNat_lt
  simp only [UInt32.reduceToNat, Nat.reduceMod]
  omega

/-- The low four bits of a word are a digit below 16. -/
theorem lowDigit_lt (w : UInt32) : (w &&& 15).toNat < 16 := by
  rw [UInt32.toNat_and]
  exact Nat.lt_succ_of_le Nat.and_le_right

/-- `acc ^ (2 ^ 32) * a ^ w`, four bits of `w` at a time, with the powers `t` of `a`. -/
@[inline] def powWord (t : Vector (Montgomery M) 16) (acc : Montgomery M) (w : UInt32) :
    Montgomery M :=
  let acc := window t acc (w >>> 28) (topDigit_lt w)
  let acc := window t acc (w >>> 24 &&& 15) (lowDigit_lt _)
  let acc := window t acc (w >>> 20 &&& 15) (lowDigit_lt _)
  let acc := window t acc (w >>> 16 &&& 15) (lowDigit_lt _)
  let acc := window t acc (w >>> 12 &&& 15) (lowDigit_lt _)
  let acc := window t acc (w >>> 8 &&& 15) (lowDigit_lt _)
  let acc := window t acc (w >>> 4 &&& 15) (lowDigit_lt _)
  window t acc (w &&& 15) (lowDigit_lt _)

/-- `acc ^ (2 ^ (32 k)) * a ^ e`, for the integer `e` of the low `k` limbs of `l`.

The limbs go from the highest, with the powers `t` of `a`.

The compiler makes one copy for each modulus, so each product is a direct call. -/
@[specialize M] def powDigits (t : Vector (Montgomery M) 16) (l : Limbs.T n) :
    Nat → Montgomery M → Montgomery M
  | 0, acc => acc
  | k + 1, acc => powDigits t l k (powWord t acc (Limbs.get l k).toUInt32)

/-- `a ^ e` for the integer `e` that the limbs write, by a window of four bits. -/
@[inline] def powLimbs (a : Montgomery M) (e : Limbs.T n) : Montgomery M :=
  powDigits (powTable a) e n one

/-- The inverse of `a`, and `0` for `0`, by Fermat's little theorem: `a ^ (p - 2)`.

It is the inverse only when `p` is prime. -/
@[inline] def inv (a : Montgomery M) : Montgomery M :=
  powLimbs a M.pm2

/-- The four bytes of `b` from `i`, read big-endian.

A byte past the end reads as `0`. -/
@[inline] def wordBE (b : ByteArray) (i : Nat) : UInt32 :=
  (b.data.getD i 0).toUInt32 * 16777216 + (b.data.getD (i + 1) 0).toUInt32 * 65536 +
    (b.data.getD (i + 2) 0).toUInt32 * 256 + (b.data.getD (i + 3) 0).toUInt32

/-- Limb `i` of the `4 m` bytes of `b` from `off`, read big-endian, where limb `0` is the lowest. -/
@[inline] def limbBE (m : Nat) (b : ByteArray) (off i : Nat) : UInt64 :=
  (wordBE b (off + 4 * (m - 1 - i))).toUInt64

/-- The element of the `4 n` bytes of `b` from `off`, read big-endian.

It is `none` when they write an integer of at least `p`. -/
@[inline] def ofBytesBE (b : ByteArray) (off : Nat) : Option (Montgomery M) :=
  let t := Words.load (n := n) (limbBE n b off) 0
  if ltWords t (Limbs.get M.pLimbs) then
    some (mulLimbs M M.r2 M.r2_lt (Limbs.pack t))
  else none

/-- The four bytes of a limb, the most significant first. -/
def limbBytes (x : UInt32) : List UInt8 :=
  [(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

/-- The bytes of the low `k` limbs of `f`, big-endian. -/
def bytesBE : Nat → (Nat → UInt64) → List UInt8
  | 0, _ => []
  | k + 1, f => limbBytes (f k).toUInt32 ++ bytesBE k f

/-- The bytes of `acc`, then the four bytes of a limb, the most significant first. -/
@[inline] def pushLimb (acc : ByteArray) (x : UInt32) : ByteArray :=
  (((acc.push (x >>> 24).toUInt8).push (x >>> 16).toUInt8).push (x >>> 8).toUInt8).push x.toUInt8

/-- The bytes of `acc`, then those of the low `k` limbs of `f`, the highest limb first. -/
@[specialize] def pushLimbs (f : Nat → UInt64) : Nat → ByteArray → ByteArray
  | 0, acc => acc
  | k + 1, acc => pushLimbs f k (pushLimb acc (f k).toUInt32)

/-- Pushing `k` limbs adds `4 k` bytes. -/
theorem size_pushLimbs (f : Nat → UInt64) (k : Nat) (acc : ByteArray) :
    (pushLimbs f k acc).size = acc.size + 4 * k := by
  induction k generalizing acc with
  | zero => rfl
  | succ k ih =>
    rw [pushLimbs, ih]
    simp only [pushLimb, ByteArray.size_push]
    omega

/-- The integer that the element stands for, as `4 n` bytes, big-endian. -/
@[inline] def toBytesBE (a : Montgomery M) : ByteArray :=
  pushLimbs (Limbs.get (mulLimbs M a.limbs a.lt (Limbs.ofNat 1)).limbs) n
    (ByteArray.emptyWithCapacity (4 * n))

/-- An element has `4 n` bytes. -/
theorem toBytesBE_size (a : Montgomery M) : (toBytesBE a).size = 4 * n := by
  rw [toBytesBE, size_pushLimbs, show (ByteArray.emptyWithCapacity (4 * n)).size = 0 from rfl,
    Nat.zero_add]

instance : Zero (Montgomery M) := ⟨zero⟩
instance : One (Montgomery M) := ⟨one⟩
instance : Add (Montgomery M) := ⟨add⟩
instance : Sub (Montgomery M) := ⟨sub⟩
instance : Neg (Montgomery M) := ⟨neg⟩
instance : Mul (Montgomery M) := ⟨mul⟩
instance : Inv (Montgomery M) := ⟨inv⟩
instance : Pow (Montgomery M) Nat := ⟨pow⟩
instance : NatCast (Montgomery M) := ⟨ofNat⟩

end Montgomery

-- The limb arithmetic unrolls to long straight-line code once the limb count is fixed.
--
-- Unfolded on symbolic limbs, it grows quickly, so proofs use the specification lemmas.
attribute [irreducible] Montgomery.mulCore Montgomery.addCore Montgomery.subCore

end EthLib.Cryptography
