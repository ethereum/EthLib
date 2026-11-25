module

public import EthLib.Cryptography.Montgomery.Product

/-!
# Montgomery arithmetic

Arithmetic mod an odd modulus `p` below `R = 2 ^ (32 n)`, on `n` limbs of 32 bits.

An element `a` is stored in Montgomery form, as `a R mod p`.

Its product is the CIOS method of Koç, Acar and Kaliski, [IEEE Micro 16(3)][cios].

[cios]: https://doi.org/10.1109/40.502403
-/

@[expose] public section

namespace EthLib.Cryptography

open Montgomery.Internal

namespace Montgomery

/-! ## The modulus

Every operation keeps its result below `p`, and the theorems here prove those bounds.

The proofs that the operations agree with the integers mod `p` come with the other properties.
-/

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
theorem Internal.numPairs_eq {f : Nat → UInt64} {m k : Nat} (h : Fits m f k) :
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
theorem Internal.size_powTableAux (a : Montgomery M) :
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
theorem Internal.topDigit_lt (w : UInt32) : (w >>> 28).toNat < 16 := by
  rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have := w.toNat_lt
  simp only [UInt32.reduceToNat, Nat.reduceMod]
  omega

/-- The low four bits of a word are a digit below 16. -/
theorem Internal.lowDigit_lt (w : UInt32) : (w &&& 15).toNat < 16 := by
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

/-- The bytes of `acc`, then the four bytes of a limb, the most significant first. -/
@[inline] def pushLimb (acc : ByteArray) (x : UInt32) : ByteArray :=
  (((acc.push (x >>> 24).toUInt8).push (x >>> 16).toUInt8).push (x >>> 8).toUInt8).push x.toUInt8

/-- The bytes of `acc`, then those of the low `k` limbs of `f`, the highest limb first. -/
@[specialize] def pushLimbs (f : Nat → UInt64) : Nat → ByteArray → ByteArray
  | 0, acc => acc
  | k + 1, acc => pushLimbs f k (pushLimb acc (f k).toUInt32)

/-- Pushing `k` limbs adds `4 k` bytes. -/
theorem Internal.size_pushLimbs (f : Nat → UInt64) (k : Nat) (acc : ByteArray) :
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
