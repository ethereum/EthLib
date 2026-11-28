module

public import EthLib.Cryptography.Proofs.Wots.CachedSearch
public import EthLib.Cryptography.Proofs.Xmss.MapMonad
public import EthLib.Cryptography.Proofs.Xmss.CodewordSearch

/-!
# The codeword chosen from a warm hash cache

The leanXMSS draft in "WOTS+C" tries randomizers in counter order.

An occupied hash entry fixes whether the search stops at that trial.

A fresh trial uses the low 16 bytes of its full hash reply.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.CachedCodeword

open Constants HashSig OracleSpec OracleComp AcceptedScan
open scoped ENNReal

/-- Read and return every byte of the underlying public hash. -/
abbrev hash := queryH (m := OracleComp HashSpec)

/-- The complete bytes of one message-digest trial in either layer. -/
@[expose] def trialInput (pp : PublicParam) (l : Layer) (e : UInt32)
    (msg : ByteArray) (rho : Randomizer) : HashInput :=
  (thInput pp (addrMsg l e) (msg ++ packBytes rho)).data.toList

/-- The codeword depends only on the low half of the full word. -/
@[expose] def digits (w : HashOutput) := codeword? (halfOf 0 (ofOutput w))

/-- These are exactly the full hash words that stop the finder. -/
noncomputable def accepted : Finset HashOutput := Finset.univ.filter fun w => (digits w).isSome

/-- A word stops the finder precisely when its digest decodes. -/
theorem mem_accepted (w : HashOutput) : w ∈ accepted ↔ (digits w).isSome := by
  simp [accepted]

/-- The probability that a fresh full word stops the finder is the code size over 2^128. -/
theorem prEvent_accepted :
    Pr{let w ← $ᵗ HashOutput}[w ∈ accepted] = (CODE_SIZE : ℝ≥0∞) / 2 ^ 128 := by
  have h := prEvent_halfOf_ofOutput (fun d => (codeword? d).isSome)
  rw [card_codeword] at h
  have member : (fun w : HashOutput => w ∈ accepted) =
      (fun w => (codeword? (halfOf 0 (ofOutput w))).isSome = true) := by
    funext w
    apply propext
    exact mem_accepted w
  change prEvent ((fun w : HashOutput => w ∈ accepted) <$> ($ᵗ HashOutput)) = _
  rw [member]
  exact h

private theorem trial_eq (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (rho : Randomizer) :
    codeword? <$> messageDigest hash pp l e msg rho =
      digits <$> QueryImpl.id' HashSpec (trialInput pp l e msg rho) := by
  unfold digits
  simp [messageDigest, th, hash, queryH, HashSig.oracleHash, trialInput, Functor.map_map]

/-- The finder and scan return the same result and preserve the same cache. -/
theorem findCodeword_eq_scan (pp : PublicParam) (l : Layer) (e : UInt32)
    (msg : ByteArray) (base : Randomizer) (c fuel : Nat) :
    Internal.findCodeword hash pp l e msg base c fuel =
      (fun result : Option (Randomizer × HashOutput) => result.bind fun pair =>
        (digits pair.2).map fun d => (pair.1, d)) <$>
      scanWithAnswer accepted (trialInput pp l e msg)
        ((List.range' c fuel).map (trialRandomizer base)) := by
  rw [Internal.findCodeword_eq]
  have h := Wots.findFirst_eq_scanWithAnswer (QueryImpl.id' HashSpec) (trialInput pp l e msg)
    (trialRandomizer base) digits accepted (fun _ => by simp [accepted]) c fuel
  simp only [trial_eq]
  simpa using h

/-- Selecting just the randomizer preserves the query order and all cache changes. -/
theorem findCodeword_position (pp : PublicParam) (l : Layer) (e : UInt32)
    (msg : ByteArray) (base : Randomizer) (c fuel : Nat) :
    Option.map Prod.fst <$> Internal.findCodeword hash pp l e msg base c fuel =
      scan accepted (trialInput pp l e msg) ((List.range' c fuel).map (trialRandomizer base)) := by
  rw [Internal.findCodeword_eq]
  have h := Wots.findFirst_position_eq_scan (QueryImpl.id' HashSpec) (trialInput pp l e msg)
    (trialRandomizer base) digits accepted (fun _ => by simp [accepted]) c fuel
  simp only [trial_eq]
  simpa using h

/-- Forward public hashes to the canonical game, where the caller also has private random draws. -/
@[expose] def forward : QueryImpl HashSpec (OracleComp OracleWorld) :=
  fun b => liftM (OracleWorld.query (.inr b))

/-- The actual finder in the canonical game makes exactly the lifted public hash calls. -/
theorem findCodeword_world (pp : PublicParam) (l : Layer) (e : UInt32)
    (msg : ByteArray) (base : Randomizer) (c fuel : Nat) :
    simulateQ forward (Internal.findCodeword hash pp l e msg base c fuel) =
      Internal.findCodeword (queryH (m := OracleComp OracleWorld)) pp l e msg base c fuel := by
  rw [findCodeword_map_monad (simulateQ forward) (fun a => simulateQ_pure _ a)
    (fun a f => simulateQ_bind _ a f)]
  congr 1

/-- Every permitted counter tests a distinct full hash input. -/
theorem trials_nodup (pp : PublicParam) (l : Layer) (e : UInt32)
    (msg : ByteArray) (base : Randomizer) (c fuel : Nat) (within : c + fuel ≤ 2 ^ 32) :
    (((List.range' c fuel).map (trialRandomizer base)).map (trialInput pp l e msg)).Nodup := by
  rw [List.map_map]
  apply List.Nodup.map_on _ (List.nodup_range' 1 (by decide) : (List.range' c fuel).Nodup)
  intro x hx y hy same
  have inputs := (thInput_inj (ByteArray.ext (Array.toList_inj.mp same))).2.2
  have rho := packBytes_injective (HashSig.byteArray_append_inj inputs rfl).2
  obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx
  obtain ⟨j, hj, rfl⟩ := List.mem_range'.mp hy
  exact trialRandomizer_inj base (by omega) (by omega) rho

/-- A warm accepted reply selects its randomizer and a warm rejection advances to the next trial.

A fresh input stops with the uniform probability of a decodable full hash word. -/
theorem prEvent_selected (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (base target : Randomizer) (c fuel : Nat) (within : c + fuel ≤ 2 ^ 32)
    (cache : HashSpec.QueryCache) :
    Pr{let z ← (simulateQ HashSpec.randomOracle
      (Internal.findCodeword hash pp l e msg base c fuel)).run cache}[
        z.1.map Prod.fst = some target] =
      ((List.range' c fuel).map (trialRandomizer base)).foldr (fun rho tail =>
        match cache (trialInput pp l e msg rho) with
        | some w => if w ∈ accepted then (if rho = target then 1 else 0) else tail
        | none => ((CODE_SIZE : ℝ≥0∞) / 2 ^ 128) * (if rho = target then 1 else 0) +
            (1 - (CODE_SIZE : ℝ≥0∞) / 2 ^ 128) * tail) 0 := by
  have h := congrArg (fun p => (simulateQ HashSpec.randomOracle p).run cache)
    (findCodeword_position pp l e msg base c fuel)
  simp only [simulateQ_map, StateT.run_map] at h
  trans Pr{let z ← (simulateQ HashSpec.randomOracle
      (scan accepted (trialInput pp l e msg)
        ((List.range' c fuel).map (trialRandomizer base)))).run cache}[
        z.1 = some target]
  · rw [← h]
    simp [prEvent_norm]
  · rw [← prEvent_accepted]
    convert probability_eq_fold accepted _ _ (trials_nodup pp l e msg base c fuel within)
        cache target using 1
    congr 1
    funext rho tail
    cases cache (trialInput pp l e msg rho) with
    | some w =>
      by_cases hit : w ∈ accepted <;> by_cases here : rho = target <;>
        simp only [hit, here, ite_true, ite_false]
    | none => simp only [SampleableType.prEvent_uniformSample]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.CachedCodeword
