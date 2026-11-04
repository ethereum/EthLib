module

public import EthLib.Cryptography.Hash.Blake2b

/-!
# Proofs: `Hash.Blake2b`

The constants and the rounds of F, against [RFC 7693](https://www.rfc-editor.org/rfc/rfc7693).

- The IV is what §2.6 derives from the square roots of the first eight primes.
- Each row of the message schedule is a permutation of the 16 word indices.
- Round `i` uses row `i mod 10`, and a run of rounds splits into two runs.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Blake2b

/-! ## The constants -/

/-- Word `i` of the IV is `floor(2^64 * frac(sqrt(p)))`, for `p` the `(i + 1)`-th prime, RFC 7693 §2.6.

- The primes are 2, 3, 5, 7, 11, 13, 17 and 19.
- Let `n = floor(sqrt(p))` and `s = 2^64 * n + IV[i]`.
- The word is right exactly when `s = floor(2^64 * sqrt(p))`.
- That is `s^2 <= 2^128 * p < (s + 1)^2`. -/
theorem IV_sqrt (i : Fin 8) :
    let p := #v[2, 3, 5, 7, 11, 13, 17, 19][i]
    let s := 2 ^ 64 * #v[1, 1, 2, 2, 3, 3, 4, 4][i] + IV[i].toNat
    s ^ 2 ≤ 2 ^ 128 * p ∧ 2 ^ 128 * p < (s + 1) ^ 2 := by
  revert i
  decide +kernel

/-- Each row of the message schedule is a permutation of the indices 0 to 15, RFC 7693 §2.7.

So each round reads every message word exactly once. -/
theorem SIGMA_perm (i : Fin 10) : SIGMA[i].toList.Perm (List.finRange 16) := by
  revert i
  decide +kernel

/-! ## The rounds -/

/-- Round `i + 10` is round `i`, RFC 7693 §2.7.

The schedule has 10 rows, so rounds 10 and 11 of BLAKE2b reuse rows 0 and 1. -/
theorem round_add_ten (m v : Vector UInt64 16) (i : Nat) : round m (i + 10) v = round m i v := by
  simp only [round, Nat.add_mod_right]

/-- Running `a + b` rounds is running `a` rounds, then the `b` rounds after them. -/
theorem roundsFrom_add (m v : Vector UInt64 16) (start a b : Nat) :
    roundsFrom m start (a + b) v = roundsFrom m (start + a) b (roundsFrom m start a v) := by
  induction a generalizing start v with
  | zero => simp [roundsFrom]
  | succ a ih =>
    -- Peel the first round off both sides, then apply the induction hypothesis.
    rw [Nat.add_right_comm, roundsFrom, ih, roundsFrom]
    congr 1
    omega

end EthLib.Cryptography.Hash.Blake2b
