module

public import EthLib.Cryptography.Secp256k1.Sqrt
public import EthLib.Cryptography.Proofs.Secp256k1.Montgomery
public import EthLib.Cryptography.Proofs.Secp256k1.Field

/-!
# Proofs: the square root of secp256k1

The chain of squarings and products computes `a^((p + 1) / 4)`.

So the square root is the power of Euler's criterion, followed by its check.

The square root then succeeds exactly on the squares, and returns a root.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

namespace Montgomery

/-- An element is the element built from its own words. -/
private theorem mk_raw (a : Montgomery) : (⟨⟨a.raw.w0, a.raw.w1, a.raw.w2, a.raw.w3⟩, a.lt⟩ :
    Montgomery) = a := rfl

/-- `n` steps that each square a multiplicative reading raise it to the power `2^n`.

The step is a variable here, so no check ever reads the words of its result. -/
private theorem read_repeatWords {R : Type} [Monoid R] (f : Montgomery → R)
    (step : Montgomery → Montgomery) (hstep : ∀ a, f (step a) = f a ^ 2) (n : Nat)
    (w0 w1 w2 w3 : UInt64) (h : (Raw.mk w0 w1 w2 w3).val < Fp.modulus) :
    f (repeatWords step n w0 w1 w2 w3 h) = f ⟨⟨w0, w1, w2, w3⟩, h⟩ ^ ((2 : Nat) ^ n) := by
  induction n generalizing w0 w1 w2 w3 with
  | zero =>
    rw [repeatWords]
    exact (pow_one _).symm
  | succ n ih =>
    rw [repeatWords, ih, mk_raw, hstep, ← pow_mul, Nat.pow_succ']

/-- `n` squarings raise a multiplicative reading to the power `2^n`. -/
private theorem read_squareTimes {R : Type} [Monoid R] (f : Montgomery → R)
    (readMul : ∀ a b, f (a * b) = f a * f b) (n : Nat) (a : Montgomery) :
    f (squareTimes n a) = f a ^ ((2 : Nat) ^ n) := by
  rw [squareTimes, read_repeatWords f square
    (fun b => by rw [square_eq_mul, readMul, pow_two]), mk_raw]

/-- The chain raises a multiplicative reading to the power `(p + 1) / 4`. -/
private theorem read_sqrtCandidate {R : Type} [Monoid R] (f : Montgomery → R)
    (readMul : ∀ a b, f (a * b) = f a * f b) (a : Montgomery) :
    f (sqrtCandidate a) = f a ^ ((Fp.modulus + 1) / 4) := by
  simp only [sqrtCandidate, readMul, read_squareTimes f readMul, ← pow_mul, ← pow_add,
    ← pow_succ]
  rfl

/-- The chain on the Montgomery form of `a` reads back as `a^((p + 1) / 4)`. -/
theorem toFin_sqrtCandidate (a : Fp) :
    toFin (sqrtCandidate (ofFin a)) = a.pow ((Fp.modulus + 1) / 4) := by
  apply Fp.toZMod.injective
  rw [Fp.toZMod_pow a ((Fp.modulus + 1) / 4) (by decide)]
  have h := read_sqrtCandidate (fun x => Fp.toZMod (toFin x))
    (fun x y => by rw [toFin_mul, map_mul]) (ofFin a)
  rw [toFin_ofFin] at h
  exact h

end Montgomery

namespace Fp

/-- The square root is the power of Euler's criterion, `a^((p + 1) / 4)`.

It is kept when it squares to `a`. -/
theorem sqrt_eq_pow (a : Fp) :
    a.sqrt = (let c := a.pow ((modulus + 1) / 4); if c * c = a then some c else none) := by
  simp only [sqrt, Montgomery.sqrt]
  rw [← Montgomery.toFin_sqrtCandidate a]
  generalize Montgomery.sqrtCandidate (Montgomery.ofFin a) = c
  -- The check in Montgomery form is the check on `Fp`, since reading back is injective.
  have hc : Montgomery.toFin c * Montgomery.toFin c = a ↔
      Montgomery.square c = Montgomery.ofFin a := by
    rw [← Montgomery.toFin_mul, ← Montgomery.square_eq_mul, ← Montgomery.toFin_ofFin a,
      Montgomery.toFin_injective.eq_iff, Montgomery.toFin_ofFin]
  by_cases h : Montgomery.square c = Montgomery.ofFin a
  · simp only [h, hc.mpr h, ite_true, Option.map_some]
  · simp only [h, mt hc.mp h, ite_false, Option.map_none]

/-- A root that the square root returns squares to its input. -/
theorem sqrt_mul_self {a c : Fp} (h : a.sqrt = some c) : toZMod c * toZMod c = toZMod a := by
  rw [sqrt_eq_pow] at h
  simp only at h
  split_ifs at h with hc
  obtain rfl := Option.some.inj h
  rw [← map_mul, hc]

/-- The square root finds a root of every square. -/
theorem sqrt_isSome {a : Fp} {b : ZMod modulus} (h : b * b = toZMod a) : ∃ c, a.sqrt = some c := by
  rw [sqrt_eq_pow]
  refine ⟨_, ite_eq_left (toZMod.injective ?_)⟩
  -- With `a = b^2`, the candidate `a^((p + 1) / 4)` squares to `b^(p + 1)`, which is `b^2`.
  have h4 := modulus_mod_four
  rw [map_mul, toZMod_pow _ _ (by decide), ← h, ← pow_two, ← pow_mul, ← pow_two, ← pow_mul]
  by_cases hb : b = 0
  · subst hb
    rw [zero_pow (by omega), zero_pow (by omega)]
  · rw [show 2 * ((modulus + 1) / 4 * 2) = (modulus - 1) + 2 by omega, pow_add,
      ZMod.pow_card_sub_one_eq_one hb, one_mul]

/-- The square root fails exactly on the non-squares. -/
theorem sqrt_eq_none_iff {a : Fp} : a.sqrt = none ↔ ∀ b : ZMod modulus, b * b ≠ toZMod a := by
  constructor
  · intro h b hb
    obtain ⟨c, hc⟩ := sqrt_isSome hb
    rw [h] at hc
    cases hc
  · intro h
    cases hs : a.sqrt with
    | none => rfl
    | some c => exact absurd (sqrt_mul_self hs) (h (toZMod c))

end Fp

end EthLib.Cryptography.Secp256k1
