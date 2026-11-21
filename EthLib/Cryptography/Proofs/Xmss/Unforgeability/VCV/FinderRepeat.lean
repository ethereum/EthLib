module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.CachedCodeword

/-!
# Repeating a previously observed codeword

The leanXMSS draft in "WOTS+C", paragraphs "Codewords" and "Signing", uses the first valid digest.

For a fixed valid codeword, exactly one low half can produce its digits.

A cached valid reply stops the search even when it contains different digits.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.CachedCodeword

open Constants HashSig OracleSpec OracleComp AcceptedScan
open scoped ENNReal

/-- A fresh full hash repeats the digits of a given valid digest with probability one over 2^128. -/
theorem prEvent_repeat_word (target : Digest) {code : Vector (Fin CHAIN_LENGTH) V}
    (valid : codeword? target = some code) :
    Pr{let w ← $ᵗ HashOutput}[digits w = some code] = (1 : ℝ≥0∞) / 2 ^ 128 := by
  have same (d : Digest) : codeword? d = some code ↔ d = target :=
    ⟨fun h => eq_of_codeword h valid, fun h => h ▸ valid⟩
  unfold digits
  simp_rw [same]
  rw [prEvent_halfOf_ofOutput (fun d => d = target)]
  simp

/-- The selected digits repeat a known codeword exactly according to this warm-cache recurrence. -/
theorem prEvent_repeat_codeword (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (base : Randomizer) (c fuel : Nat) (within : c + fuel ≤ 2 ^ 32)
    (cache : HashSpec.QueryCache) (target : Digest) {code : Vector (Fin CHAIN_LENGTH) V}
    (valid : codeword? target = some code) :
    Pr{let z ← (simulateQ HashSpec.randomOracle
      (Internal.findCodeword hash pp l e msg base c fuel)).run cache}[
        z.1.map Prod.snd = some code] =
      ((List.range' c fuel).map (trialRandomizer base)).foldr (fun rho tail =>
        match cache (trialInput pp l e msg rho) with
        | some w => if w ∈ accepted then (if digits w = some code then 1 else 0) else tail
        | none => (1 : ℝ≥0∞) / 2 ^ 128 + (1 - (CODE_SIZE : ℝ≥0∞) / 2 ^ 128) * tail) 0 := by
  classical
  let selected (u : Option (Randomizer × HashOutput)) :=
    (u.bind fun pair => (digits pair.2).map fun d => (pair.1, d)).map Prod.snd = some code
  have observed (rho : Randomizer) (w : HashOutput) :
      selected (some (rho, w)) ↔ digits w = some code := by
    cases h : digits w <;> simp [selected, h]
  have hit (rho : Randomizer) : Pr{let w ← $ᵗ HashOutput}[w ∈ accepted ∧ selected (some (rho, w))] =
      (1 : ℝ≥0∞) / 2 ^ 128 := by
    have event : (fun w : HashOutput => w ∈ accepted ∧ selected (some (rho, w))) =
        (fun w => digits w = some code) := by
      funext w
      apply propext
      rw [observed]
      exact ⟨And.right, fun h => ⟨by simp [mem_accepted, h], h⟩⟩
    change prEvent ((fun w : HashOutput => w ∈ accepted ∧ selected (some (rho, w))) <$>
      ($ᵗ HashOutput)) = _
    rw [event]
    exact prEvent_repeat_word target valid
  rw [findCodeword_eq_scan, simulateQ_map, StateT.run_map]
  simp only [prEvent_norm]
  change Pr{let z ← (simulateQ HashSpec.randomOracle
    (scanWithAnswer accepted (trialInput pp l e msg)
      ((List.range' c fuel).map (trialRandomizer base)))).run cache}[selected z.1] = _
  rw [prEvent_scanWithAnswer accepted _ _ (trials_nodup pp l e msg base c fuel within)]
  unfold answerProbability
  simp only [hit, prEvent_not_eq_one_sub, prEvent_accepted]
  have empty : ¬selected none := by simp [selected]
  simp only [empty, ↓reduceIte]
  congr 1
  funext rho tail
  cases cache (trialInput pp l e msg rho) with
  | some w => simp only [observed]
  | none => rfl

end EthLib.Cryptography.Xmss.Unforgeability.VCV.CachedCodeword
