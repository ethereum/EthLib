/-
Copyright (c) 2026 Trail of Bits.
Released under CC0 1.0 Universal as described in the file LICENSE.
Authors: Trail of Bits
-/

module
public import EthereumXMSSHypertree.HashInputs

/-!
# EthLib counter retry semantics

The source search evaluates successive additive counter randomizers and stops at its first
accepted digest. These are deterministic finite counter semantics, without an IID sampling law.
The randomizer injectivity argument is adapted from EthLib Proofs.Xmss.CodewordSearch at
commit 67b306b8f93f34b8fbd0ef3fb912e2519e5d8658 (CC0-1.0), without its security imports.
-/

public section

namespace EthereumXMSSHypertree

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

/-- The exact integer encoded in source randomizer trial `c`. -/
theorem trialRandomizer_value (base : Randomizer) (c : Nat) :
    EthLib.Base.bytesToUint (trialRandomizer base c) =
      (EthLib.Base.bytesToUint base + c) % 2 ^ 128 := by
  simp only [trialRandomizer, EthLib.Base.bytesToUint_uintToBytes, RANDOMIZER_LEN]
  omega

/-- Distinct legal source counters give distinct randomizers. -/
theorem trialRandomizer_injective (base : Randomizer) {j j' : Nat}
    (hj : j < 2 ^ 32) (hj' : j' < 2 ^ 32)
    (h : trialRandomizer base j = trialRandomizer base j') : j = j' := by
  have hvalue := congrArg EthLib.Base.bytesToUint h
  simp only [trialRandomizer_value] at hvalue
  have hb := EthLib.Base.bytesToUint_lt base
  simp only [RANDOMIZER_LEN] at hb
  omega

/-- The monadic source makes the current test before deciding whether to recurse. -/
theorem findCodeword_step {m : Type → Type} [Monad m]
    (H : ByteArray → m (Vector UInt8 32)) (pp : PublicParam) (layer : Layer) (e : UInt32)
    (msg : ByteArray) (base : Randomizer) (c fuel : Nat) :
    Internal.findCodeword H pp layer e msg base c (fuel + 1) = (do
      let rho := trialRandomizer base c
      match ← codeword? <$> messageDigest H pp layer e msg rho with
      | some x => pure (some (rho, x))
      | none => Internal.findCodeword H pp layer e msg base (c + 1) fuel) := by
  simp only [Internal.findCodeword, EthLib.Cryptography.Wots.findFirst]
  congr 1
  funext result
  cases result <;> rfl

/-- A deterministic source digest's acceptance test at one counter. -/
@[expose] def retryAccept (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (base : Randomizer) (c : Nat) :=
  codeword? ((messageDigest (pureHash H) pp layer e msg (trialRandomizer base c)).run)

/-- The exact source search, observed in the identity monad. -/
@[expose] def retryOutcome (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (base : Randomizer) (c fuel : Nat) :=
  (Internal.findCodeword (pureHash H) pp layer e msg base c fuel).run

/-- With no trials remaining the source returns failure. -/
theorem retryOutcome_zero (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (base : Randomizer) (c : Nat) :
    retryOutcome H pp layer e msg base c 0 = none := rfl

/-- One source trial either succeeds immediately or advances exactly one counter. -/
theorem retryOutcome_succ (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (base : Randomizer) (c fuel : Nat) :
    retryOutcome H pp layer e msg base c (fuel + 1) =
      match retryAccept H pp layer e msg base c with
      | some x => some (trialRandomizer base c, x)
      | none => retryOutcome H pp layer e msg base (c + 1) fuel := by
  cases ht : codeword? ((messageDigest (pureHash H) pp layer e msg
    (trialRandomizer base c)).run) <;>
    simp [retryOutcome, Internal.findCodeword, EthLib.Cryptography.Wots.findFirst, retryAccept, ht]

/-- Failure means every trial in the exact ordered interval failed. -/
theorem retryOutcome_none_iff (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (base : Randomizer) (c fuel : Nat) :
    retryOutcome H pp layer e msg base c fuel = none ↔
      ∀ j, c ≤ j → j < c + fuel → retryAccept H pp layer e msg base j = none := by
  induction fuel generalizing c with
  | zero =>
    simp only [retryOutcome_zero, Nat.add_zero, true_iff]
    intro j hj hj'
    omega
  | succ fuel ih =>
    rw [retryOutcome_succ]
    cases ht : retryAccept H pp layer e msg base c with
    | none =>
      simp only [ih]
      constructor
      · intro h j hj hj'
        by_cases heq : j = c
        · simpa [heq] using ht
        · exact h j (by omega) (by omega)
      · intro h j hj hj'
        exact h j (by omega) (by omega)
    | some x =>
      simp only [Option.some_ne_none, false_iff]
      intro h
      have := h c (by omega) (by omega)
      simp [ht] at this

/-- A successful source search returns its first accepted trial and no later trial. -/
theorem retryOutcome_first (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (base : Randomizer) (c fuel : Nat)
    {rho : Randomizer} {x : Vector (Fin CHAIN_LENGTH) V}
    (h : retryOutcome H pp layer e msg base c fuel = some (rho, x)) :
    ∃ j, c ≤ j ∧ j < c + fuel ∧ rho = trialRandomizer base j ∧
      retryAccept H pp layer e msg base j = some x ∧
      ∀ k, c ≤ k → k < j → retryAccept H pp layer e msg base k = none := by
  induction fuel generalizing c with
  | zero => simp [retryOutcome_zero] at h
  | succ fuel ih =>
    rw [retryOutcome_succ] at h
    cases ht : retryAccept H pp layer e msg base c with
    | none =>
      simp only [ht] at h
      obtain ⟨j, hj, hj', hrho, hx, hbefore⟩ := ih (c + 1) h
      refine ⟨j, by omega, by omega, hrho, hx, ?_⟩
      intro k hk hk'
      by_cases heq : k = c
      · simpa [heq] using ht
      · exact hbefore k (by omega) hk'
    | some y =>
      simp only [ht, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hrho, rfl⟩ := h
      exact ⟨c, by omega, by omega, hrho.symm, ht, fun k hk hk' => by omega⟩

/-- Once the first trial succeeds, later fuel cannot change its result. -/
theorem retryOutcome_early_stop (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (base : Randomizer) (c fuel : Nat)
    {x : Vector (Fin CHAIN_LENGTH) V} (h : retryAccept H pp layer e msg base c = some x) :
    retryOutcome H pp layer e msg base c (fuel + 1) =
      some (trialRandomizer base c, x) := by
  rw [retryOutcome_succ, h]

/-- A first accepted counter inside the fuel interval is returned exactly. -/
theorem retryOutcome_at_first (H : ByteArray → Vector UInt8 32) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (base : Randomizer) (c fuel j : Nat)
    {x : Vector (Fin CHAIN_LENGTH) V} (hlo : c ≤ j) (hhi : j < c + fuel)
    (hx : retryAccept H pp layer e msg base j = some x)
    (hbefore : ∀ k, c ≤ k → k < j → retryAccept H pp layer e msg base k = none) :
    retryOutcome H pp layer e msg base c fuel = some (trialRandomizer base j, x) := by
  induction fuel generalizing c with
  | zero => omega
  | succ fuel ih =>
    by_cases heq : j = c
    · subst j
      exact retryOutcome_early_stop H pp layer e msg base c fuel hx
    · rw [retryOutcome_succ, hbefore c (by omega) (by omega)]
      exact ih (c + 1) (by omega) (by omega) (fun k hk hk' => hbefore k (by omega) hk')

/-- Distinct legal counters give distinct full source digest inputs, for a fixed message. -/
theorem retryInput_injective (pp : PublicParam) (layer : Layer) (e : UInt32)
    (msg : ByteArray) (base : Randomizer) {j j' : Nat}
    (hj : j < MAX_RANDOMIZER_TRIALS) (hj' : j' < MAX_RANDOMIZER_TRIALS)
    (h : thInput pp (addrMsg layer e) (msg ++ packBytes (trialRandomizer base j)) =
      thInput pp (addrMsg layer e) (msg ++ packBytes (trialRandomizer base j'))) : j = j' := by
  have hpayload := (thInput_inj h).2.2
  have hrho := (EthLib.Cryptography.HashSig.byteArray_append_inj hpayload rfl).2
  exact trialRandomizer_injective base hj hj' (packBytes_injective hrho)

/-- The zero-based source counter `c` represents `c + 1` attempted digests. -/
theorem retry_attempt_count {c : Nat} (hc : c < MAX_RANDOMIZER_TRIALS) :
    1 ≤ c + 1 ∧ c + 1 ≤ MAX_RANDOMIZER_TRIALS := by omega

end EthereumXMSSHypertree
