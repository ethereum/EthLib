module

/-!
# Montgomery arithmetic: words of 32 bits

Numbers are written in words of 32 bits, and each word is held in 64 bits.

The carry and the borrow of one word build the operations on several.

A class gives the words of each limb count, unrolled at compile time.
-/

@[expose] public section

namespace EthLib.Cryptography.Montgomery

/-! ## Words of 32 bits -/

/-- The low 32 bits and the carry of `t + a * b + c`. -/
@[inline] def mac (t a b c : UInt64) : UInt64 × UInt64 :=
  -- Each product of two limbs fits in 64 bits, so the code needs no wider product.
  --
  -- `(C,S)` of CIOS: `S` the low word and `C` the carry.
  let s := t + a * b + c
  (s &&& 0xFFFFFFFF, s >>> 32)

/-- The two words of `mac` write `t + a b + c`, when every input is below `2 ^ 32`. -/
theorem Internal.mac_spec {t a b c : UInt64} (ht : t.toNat < 2 ^ 32) (ha : a.toNat < 2 ^ 32)
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

-- The lemmas of the internal namespace serve the Montgomery modules and their proofs alone.
open Internal

/-- The low 32 bits of `x - y - b`, and the borrow out of them. -/
@[inline] def sbb (x y b : UInt64) : UInt64 × UInt64 :=
  let d := x - y - b
  (d &&& 0xFFFFFFFF, d >>> 63)

/-- The two words of `sbb` write `x - y - b`, with the borrow as a multiple of `2 ^ 32`. -/
theorem Internal.sbb_spec {x y b : UInt64} (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32)
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

/-- The lowest word, then the others above it. -/
theorem Internal.num_succ (n : Nat) (f : Nat → UInt64) (k : Nat) :
    num (n + 1) f k = (f k).toNat + 2 ^ 32 * num n f (k + 1) := rfl

/-- `n + 1` words fit when the lowest one and the others fit. -/
theorem Internal.fits_succ {n : Nat} {f : Nat → UInt64} {k : Nat} :
    Fits (n + 1) f k ↔ (f k).toNat < 2 ^ 32 ∧ Fits n f (k + 1) := Iff.rfl

/-- Words that agree write the same integer. -/
theorem Internal.num_congr {n : Nat} {f g : Nat → UInt64} {j k : Nat}
    (h : ∀ i < n, f (j + i) = g (k + i)) : num n f j = num n g k := by
  induction n generalizing j k with
  | zero => rfl
  | succ n ih =>
    rw [num_succ, num_succ, show f j = g k from h 0 (by omega)]
    rw [@ih (j + 1) (k + 1) fun i hi => by
      rw [Nat.add_right_comm j 1 i, Nat.add_right_comm k 1 i]
      exact h (i + 1) (by omega)]

/-- Words that agree fit together. -/
theorem Internal.fits_congr {n : Nat} {f g : Nat → UInt64} {j k : Nat}
    (h : ∀ i < n, f (j + i) = g (k + i)) : Fits n f j ↔ Fits n g k := by
  induction n generalizing j k with
  | zero => exact Iff.rfl
  | succ n ih =>
    rw [fits_succ, fits_succ, show f j = g k from h 0 (by omega)]
    rw [@ih (j + 1) (k + 1) fun i hi => by
      rw [Nat.add_right_comm j 1 i, Nat.add_right_comm k 1 i]
      exact h (i + 1) (by omega)]

/-- The words fit when each one is below `2 ^ 32`. -/
theorem Internal.fits_of_lt {n : Nat} {f : Nat → UInt64} {k : Nat}
    (h : ∀ i < n, (f (k + i)).toNat < 2 ^ 32) : Fits n f k := by
  induction n generalizing k with
  | zero => trivial
  | succ n ih =>
    refine ⟨h 0 (by omega), ih fun i hi => ?_⟩
    rw [Nat.add_right_comm]
    exact h (i + 1) (by omega)

/-- After its first word, a word followed by `w` reads as `w`. -/
theorem Internal.num_cons {n : Nat} (h : UInt64) (w : Nat → UInt64) (k : Nat) :
    num n (cons h w) (k + 1) = num n w k :=
  num_congr fun i _ => by
    simp only [cons, Nat.add_right_comm k 1 i, Nat.add_one_ne_zero, ↓reduceIte,
      Nat.add_sub_cancel]

/-- After its first word, a word followed by `w` fits as `w`. -/
theorem Internal.fits_cons {n : Nat} (h : UInt64) (w : Nat → UInt64) (k : Nat) :
    Fits n (cons h w) (k + 1) ↔ Fits n w k :=
  fits_congr fun i _ => by
    simp only [cons, Nat.add_right_comm k 1 i, Nat.add_one_ne_zero, ↓reduceIte,
      Nat.add_sub_cancel]

/-- The integer of a word `h` followed by words `w`. -/
theorem Internal.num_cons_zero {n : Nat} (h : UInt64) (w : Nat → UInt64) :
    num (n + 1) (cons h w) 0 = h.toNat + 2 ^ 32 * num n w 0 := by
  rw [num_succ, num_cons]
  rfl

/-- A word followed by `w` fits when the word and `w` fit. -/
theorem Internal.fits_cons_zero {n : Nat} {h : UInt64} {w : Nat → UInt64} :
    Fits (n + 1) (cons h w) 0 ↔ h.toNat < 2 ^ 32 ∧ Fits n w 0 := by
  rw [fits_succ, fits_cons]
  rfl

/-- `2 ^ (32 (n + 1))` is `2 ^ 32` times `2 ^ (32 n)`. -/
theorem Internal.radix_succ (n : Nat) : 2 ^ (32 * (n + 1)) = 2 ^ 32 * 2 ^ (32 * n) := by
  rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]

/-- Words that fit write an integer below `2 ^ (32 n)`. -/
theorem Internal.num_lt {n : Nat} {f : Nat → UInt64} {k : Nat} (h : Fits n f k) :
    num n f k < 2 ^ (32 * n) := by
  induction n generalizing k with
  | zero => exact Nat.one_pos
  | succ n ih =>
    have := ih h.2
    rw [num_succ, radix_succ]
    have := h.1
    omega

/-- The top word of `n + 1` words weighs `2 ^ (32 n)`. -/
theorem Internal.num_snoc (n : Nat) (f : Nat → UInt64) (k : Nat) :
    num (n + 1) f k = num n f k + 2 ^ (32 * n) * (f (k + n)).toNat := by
  induction n generalizing k with
  | zero => simp [num]
  | succ n ih =>
    rw [num_succ, ih, num_succ, radix_succ, Nat.add_right_comm k 1 n, Nat.mul_add,
      Nat.mul_assoc, show f (k + (n + 1)) = f (k + n + 1) from rfl]
    omega

/-- An invariant that each step keeps holds after the steps. -/
theorem Internal.loop_induct {σ : Type} (P : Nat → σ → Prop) (f : Nat → σ → σ) (n k : Nat) (s : σ)
    (h0 : P k s) (hs : ∀ i s, k ≤ i → i < k + n → P i s → P (i + 1) (f i s)) :
    P (k + n) (loop n f k s) := by
  induction n generalizing k s with
  | zero => exact h0
  | succ n ih =>
    rw [loop, show k + (n + 1) = k + 1 + n by omega]
    exact ih (k + 1) (f k s) (hs k s (Nat.le_refl k) (by omega) h0)
      (fun i s hi hi' => hs i s (by omega) (by omega))

/-- `k + m` steps are `k` steps, then `m` steps from the index after them. -/
theorem Internal.loop_add {σ : Type} (f : Nat → σ → σ) (k m i : Nat) (s : σ) :
    loop (k + m) f i s = loop m f (i + k) (loop k f i s) := by
  induction k generalizing i s with
  | zero => rw [Nat.zero_add, Nat.add_zero]; rfl
  | succ k ih =>
    rw [show k + 1 + m = k + m + 1 by omega, loop, ih, loop, show i + 1 + k = i + (k + 1) by omega]

/-! ## Unrolled words

The code is written once for every limb count.
-/

/-- Words of `n` limbs, each held in 64 bits, with the operations of the product.

The instances for `0` and `n + 1` limbs build them, so a fixed count unrolls at compile time.

Each operation carries the equation of its value, proved once from the instance below it. -/
class Words (n : Nat) where
  /-- The words. -/
  W : Type
  /-- The word at an index, and `0` past the last. -/
  word : W → Nat → UInt64
  /-- The words of `0`. -/
  zero : W
  -- Each operation reads its inputs through a function of the limb index.
  --
  -- So a modulus given by a match on the index folds to immediate constants.
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
  -- CIOS: `(C,S) := t[s] + C`, `t[s-1] := S`, `t[s] := t[s+1] + C`.
  --
  -- Here the word above the others holds `t[s]` and `t[s+1]`.
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
  -- CIOS, the multiplication loop over `j` from `0` to `s - 1`: `(C,S) := t[j] + a[j]*b[i] + C`.
  --
  -- Then `t[j] := S`.
  let x := mac t.1 (a k) b c
  -- The next words take the carry `C`.
  let r := Words.mac t.2 a b x.2 (k + 1)
  ((x.1, r.1), r.2)

/-- `t + m p + c` with `top` above it, on `n + 1` words: the low word, then the others. -/
@[inline] def shS (t : UInt64 × inst.W) (p : Nat → UInt64) (m c : UInt64) (k : Nat)
    (top : UInt64) : (UInt64 × (UInt64 × inst.W)) × UInt64 :=
  -- The reduction loop: `(C,S) := t[j] + m*n[j] + C`, `t[j-1] := S`.
  let x := mac t.1 m (p k) c
  -- The next words take the carry `C`.
  let r := Words.sh t.2 p m x.2 (k + 1) top
  ((x.1, r.1), r.2)

/-- `(t + m p + R top) / 2 ^ 32` on `n + 1` words, when the low word of the sum is `0`. -/
@[inline] def redS (t : UInt64 × inst.W) (p : Nat → UInt64) (m top : UInt64) :
    (UInt64 × inst.W) × UInt64 :=
  -- CIOS, with the shift integrated: `(C,S) := t[0] + m*n[0]`.
  --
  -- The low word of the sum is `0`, so only its carry goes on.
  let x := mac t.1 m (p 0) 0
  -- The loop over `j` from `1` to `s - 1`: `(C,S) := t[j] + m*n[j] + C`, `t[j-1] := S`.
  --
  -- Then the top words.
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
theorem Internal.macS_spec (t : UInt64 × inst.W) (a : Nat → UInt64) (b c : UInt64) (k : Nat)
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
theorem Internal.shS_spec (t : UInt64 × inst.W) (p : Nat → UInt64) (m c : UInt64) (k : Nat)
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
theorem Internal.redS_spec (t : UInt64 × inst.W) (p : Nat → UInt64) (m top : UInt64)
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
theorem Internal.subbS_spec (t : UInt64 × inst.W) (p : Nat → UInt64) (br : UInt64) (k : Nat)
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
  -- The words are a pair, which the compiler erases, so each word stays in a register.
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

/-- The words of fitting words are below `2 ^ 32`. -/
theorem Internal.lt_of_fits {n : Nat} {f : Nat → UInt64} {k : Nat} (h : Fits n f k) :
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
theorem Internal.load_spec (a : Nat → UInt64) (k : Nat) :
    (Fits n (Words.word (Words.load (n := n) a k)) 0 ↔ Fits n a k) ∧
      num n (Words.word (Words.load (n := n) a k)) 0 = num n a k := by
  have h : ∀ i < n, Words.word (Words.load (n := n) a k) (0 + i) = a (k + i) :=
    fun i hi => by rw [Nat.zero_add]; exact Words.word_load _ _ _ hi
  exact ⟨fits_congr h, num_congr h⟩

/-- The integer of `n` limbs, mod `2 ^ 32`, is the integer of its low limb. -/
theorem Internal.num_mod {f : Nat → UInt64} {k : Nat} (hn : 0 < n) (h : Fits n f k) :
    num n f k % 2 ^ 32 = (f k).toNat := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [num_succ]
  have := h.1
  omega

/-- `2 ^ (32 n)` is a multiple of `2 ^ 32` for `n > 0`. -/
theorem Internal.radix_mod (hn : 0 < n) : ∃ q, 2 ^ (32 * n) = 2 ^ 32 * q := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ⟨_, radix_succ m⟩

end Generic

end EthLib.Cryptography.Montgomery
