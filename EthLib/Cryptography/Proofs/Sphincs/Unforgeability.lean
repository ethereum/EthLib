module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.AdversaryCalls
public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.SearchGame
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Main

/-!
# Proofs: leanSPHINCS as EthLib computes it is unforgeable

The theorem holds in the random oracle model, for one key and at most `2^30` signing requests.

Take an adversary whose experiment makes at most `q >= 1` hash calls.

It forges a signature with probability at most `q / 2^127`.

The bound is the model's theorem in `Security/`.

The bridge in `Unforgeability/Bridge/` carries it to EthLib.

Two more theorems charge only the adversary's own hash calls, and take a bound on its requests.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open ENNReal EthLib.Cryptography.Sphincs.Constants

/-- leanSPHINCS as EthLib computes it is strongly unforgeable in the random oracle model.

Take an adversary whose experiment makes at most `q >= 1` hash calls in every run.

It forges with probability at most `q / 2^127`.

`q` counts the calls of key generation and of every signing request too. -/
theorem unforgeable : HasClassicalSecurityBits 127 := fun q hq adversary hbound =>
  -- The game runs EthLib's key generation, signing and verification.
  --
  -- Their hash `H` is a query to the oracle.
  --
  -- The security proof in `Security/` reasons over a model of the scheme with the same calls.
  --
  -- The bridge in `Unforgeability/Bridge/` compares EthLib with it:
  --
  -- - EthLib's bytes, addresses, keys and signatures are the model's.
  -- - Each hashing routine of EthLib is the model's, call for call or under every answer function.
  -- - An EthLib forgery is a model forgery of a translated adversary.
  -- - A signing request costs the model at most what it costs EthLib.
  --   So the budget `q` carries over.
  (forgeAdvantage_le adversary).trans
    (SphincsSecurity.h26_layered q hq (translate adversary)
      (hasHashQueryBound_translate_self adversary q hbound))

/-- leanSPHINCS as EthLib computes it is strongly unforgeable, with the adversary's calls as budget.

Take an adversary with at most `q` hash calls of its own and `r` signing requests in every run.

It forges with probability at most `(q + C) / 2^127`, where `C` bounds the scheme's calls.

At the model's cap of 1,182,000,000 requests, `C` is about `2^63.7`.

So the bound is never below about `2^-63.3`. -/
theorem unforgeable_adversary : HasAdversarySecurityBits 127 := fun q r adversary hbound =>
  -- The scheme's calls add a constant: 264193 for key generation and 491 for verification.
  --
  -- Each signing request adds at most `470595 + 3 * 2^32`.
  --
  -- That holds when every counter search runs to its end.
  unforgeable (q + schemeCalls r) (by unfold schemeCalls keyGenCalls; omega) adversary
    (hasHashQueryBound_of_adversary adversary q r hbound)

/-- leanSPHINCS as EthLib computes it is strongly unforgeable, with long searches charged apart.

Take an adversary with at most `q` hash calls of its own and `r` signing requests in every run.

Take a bound `1 <= T <= 2^32` on the counter searches.

It forges with probability at most `(q + C_T) / 2^127 + (q + C) * (1 - p)^T`.

`p` is the chance that one counter gives a codeword: `CODE_SIZE / 2^128`, about `2^-13.84`.

`C_T` charges each request its searches up to `T` counters, and one request all `2^32`.

`C` bounds the scheme's calls with every search run to its end. -/
theorem forgeAdvantage_le_capped (T : Nat) (hT₁ : 1 ≤ T) (hT : T ≤ MAX_COUNTER_TRIALS)
    (q r : Nat) (adversary : Adversary) (h : HasAdversaryQueryBound adversary q r) :
    forgeAdvantage adversary ≤
      ((q + cappedCalls T r : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) +
        ((q + schemeCalls r : Nat) : ℝ≥0∞) *
          (((2 ^ 128 - CODE_SIZE : ℕ) : ℝ≥0∞) / 2 ^ 128) ^ T :=
  -- The wrapped adversary forges within the first budget, and the rest is the long searches.
  (forgeAdvantage_le_capSearches T hT₁ hT adversary q r h).trans (add_le_add
    (unforgeable (q + cappedCalls T r) (by unfold cappedCalls keyGenCalls; omega)
      (capSearches T adversary) (hasHashQueryBound_capSearches T adversary q r h)) le_rfl)

/-- With uniform digests, `2^22` counters all miss the code with probability at most `2^-327`. -/
theorem searchMiss_pow_searchCap_le :
    (((2 ^ 128 - CODE_SIZE : ℕ) : ℝ) / 2 ^ 128) ^ searchCap ≤ 1 / (2 ^ 200 * 2 ^ 127) := by
  have hcast : (((2 ^ 128 - CODE_SIZE : ℕ) : ℝ)) / 2 ^ 128 = 1 - (CODE_SIZE : ℝ) / 2 ^ 128 := by
    rw [Nat.cast_sub (by norm_num [CODE_SIZE] : CODE_SIZE ≤ 2 ^ 128), Nat.cast_pow,
      Nat.cast_ofNat, sub_div, div_self (by positivity)]
  rw [hcast]
  set p : ℝ := (CODE_SIZE : ℝ) / 2 ^ 128
  -- The expected number of codewords among the counters is above 256.
  have hmean : (256 : ℝ) ≤ 2 ^ 22 * p := by
    simp only [p, CODE_SIZE]
    norm_num
  have hp : 0 ≤ 1 - p := by
    simp only [p, CODE_SIZE]
    norm_num
  -- `e^256` is above `2.5^256`, which is above `2^327`.
  have hexp : (2 : ℝ) ^ 200 * 2 ^ 127 ≤ Real.exp 256 := by
    have h1 : (5 / 2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h2 : (5 / 2 : ℝ) ^ 128 ≤ Real.exp 1 ^ 128 := pow_le_pow_left₀ (by norm_num) h1 _
    calc (2 : ℝ) ^ 200 * 2 ^ 127 = 2 ^ 160 * 2 ^ 167 := by norm_num
      _ ≤ (5 / 2) ^ 128 * (5 / 2) ^ 128 :=
        mul_le_mul (by norm_num) (by norm_num) (by positivity) (by positivity)
      _ ≤ Real.exp 1 ^ 128 * Real.exp 1 ^ 128 := mul_le_mul h2 h2 (by positivity) (by positivity)
      _ = Real.exp 256 := by rw [← pow_add, ← Real.exp_nat_mul]; norm_num
  calc (1 - p) ^ searchCap
      ≤ Real.exp (-p) ^ searchCap :=
        pow_le_pow_left₀ hp (by linarith [Real.add_one_le_exp (-p)]) _
    _ = Real.exp (-(2 ^ 22 * p)) := by
        rw [← Real.exp_nat_mul, searchCap]
        congr 1
        push_cast
        ring
    _ ≤ Real.exp (-256) := Real.exp_le_exp.mpr (by linarith)
    _ = 1 / Real.exp 256 := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / (2 ^ 200 * 2 ^ 127) := one_div_le_one_div_of_le (by positivity) hexp

/-- Up to `2^200` calls, the long-search term is at most `1 / 2^127`. -/
theorem longSearches_le (n : ℕ) (hn : n ≤ 2 ^ 200) :
    (n : ℝ≥0∞) * (((2 ^ 128 - CODE_SIZE : ℕ) : ℝ≥0∞) / 2 ^ 128) ^ searchCap ≤
      1 / ((2 ^ 127 : ℕ) : ℝ≥0∞) := by
  -- Both sides are images of real numbers.
  have hε : ((2 ^ 128 - CODE_SIZE : ℕ) : ℝ≥0∞) / 2 ^ 128 =
      ENNReal.ofReal ((((2 ^ 128 - CODE_SIZE : ℕ) : ℝ)) / 2 ^ 128) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have hb : 1 / ((2 ^ 127 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (1 / 2 ^ 127) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
      show ((2 : ℝ) ^ 127) = ((2 ^ 127 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  rw [hε, hb, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (n : ℝ) * ((((2 ^ 128 - CODE_SIZE : ℕ) : ℝ)) / 2 ^ 128) ^ searchCap
      ≤ 2 ^ 200 * (1 / (2 ^ 200 * 2 ^ 127)) :=
        mul_le_mul (by exact_mod_cast hn) searchMiss_pow_searchCap_le (by positivity)
          (by positivity)
    _ = 1 / 2 ^ 127 := by field_simp

/-- leanSPHINCS as EthLib computes it is strongly unforgeable, with long searches charged apart.

Take an adversary with at most `q` hash calls of its own and `r` signing requests in every run.

It forges with probability at most `(q + C + 1) / 2^127`.

`C` charges each request its searches up to `2^22` counters, and one request all `2^32`.

At `2^30` requests, `C` is about `2^53.6`, so the bound is never below about `2^-73.4`. -/
theorem unforgeable_capped : HasCappedSecurityBits 127 := by
  intro q r adversary h
  have hT₁ : 1 ≤ searchCap := by unfold searchCap; norm_num
  have hT : searchCap ≤ MAX_COUNTER_TRIALS := by unfold searchCap MAX_COUNTER_TRIALS; norm_num
  by_cases hN : q + schemeCalls r ≤ 2 ^ 200
  · -- Below `2^200` calls, the long searches add at most `1 / 2^127`.
    --
    -- The adversary is wrapped to stop once an answer shows a search longer than `2^22` counters.
    --
    -- The request that shows it is charged all `3 * 2^32` counters.
    --
    -- A longer search leaves `2^22` missed counters in the oracle's cache, which is unlikely.
    refine (forgeAdvantage_le_capped searchCap hT₁ hT q r adversary h).trans ?_
    refine (add_le_add le_rfl (longSearches_le _ hN)).trans ?_
    rw [ENNReal.div_add_div_same, Nat.cast_add (q + cappedCalls searchCap r) 1, Nat.cast_one]
  · -- Above, the bound is at least 1.
    have hbig : 2 ^ 127 ≤ q + cappedCalls searchCap r + 1 := by
      unfold schemeCalls signCalls keyGenCalls verifyCalls MAX_COUNTER_TRIALS at hN
      unfold cappedCalls searchCap keyGenCalls verifyCalls MAX_COUNTER_TRIALS
      norm_num at hN ⊢
      omega
    refine (prEvent_le_one _).trans ?_
    rw [ENNReal.le_div_iff_mul_le (by simp) (by simp), one_mul]
    exact_mod_cast hbig

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
