module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Domains

/-!
# Guessing the master seed

A hash input names a seed when it is a key-generation input of that seed.

A seed derivation names its seed for any public seed and any domain.

The inputs that give `PK.seed` and `SK.prf` also name their seed.

Each input names at most one seed.

So a fixed input names a uniform 256-bit seed with probability at most `1 / 2^256`.

This module also defines one step of an adaptive strategy that guesses the seed.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Security.SeedGuess

variable [Params]

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 10000

/-- The input names the seed: it derives a key from the seed, or it is `leanSPHINCS || seed || d`.

The domain byte `d` is 0 for `PK.seed` and 1 for `SK.prf`. -/
def SeedHit (input : HashInput) (seed : MasterSeed) : Prop :=
  (∃ parameter domain, keygenHashInput parameter domain seed = input) ∨
    ∃ domain, keySeedInput seed domain = input

/-- An input names at most one seed. -/
theorem seedHit_unique {input : HashInput} {seed seed' : MasterSeed}
    (h : SeedHit input seed) (h' : SeedHit input seed') : seed = seed' := by
  rcases h with ⟨parameter, domain, rfl⟩ | ⟨domain, rfl⟩ <;>
    rcases h' with ⟨parameter', domain', heq⟩ | ⟨domain', heq⟩
  · exact (keygenInput_injective heq.symm).2.2
  · exact absurd heq (keySeedInput_ne_keygenHashInput _ _ _ _ _)
  · exact absurd heq.symm (keySeedInput_ne_keygenHashInput _ _ _ _ _)
  · exact (bytesLE_injective (List.append_cancel_left (List.append_inj' heq rfl).1)).symm

/-- The seed that an input names, or `none` if the input names no seed. -/
noncomputable def parseSeed (input : HashInput) : Option MasterSeed :=
  if h : ∃ seed, SeedHit input seed then some (Classical.choose h) else none

theorem parseSeed_eq_some_iff (input : HashInput) (seed : MasterSeed) :
    parseSeed input = some seed ↔ SeedHit input seed := by
  classical
  unfold parseSeed
  split
  next h =>
    constructor
    · intro heq
      cases Option.some.inj heq
      exact Classical.choose_spec h
    · intro hseed
      exact congrArg some (seedHit_unique (Classical.choose_spec h) hseed)
  next h =>
    constructor
    · simp
    · intro hseed
      exact False.elim (h ⟨seed, hseed⟩)

/-- A fixed input names a uniform seed with probability at most `1 / 2^256`. -/
theorem seedHit_probability_le (input : HashInput) :
    Pr{let x ← sampleMasterSeed}[(SeedHit input) x] ≤ 1 / (2 : ℝ≥0∞) ^ 256 := by
  classical
  let := SampleableType.ofFintype MasterSeed
  rw [show sampleMasterSeed = ($ᵗ MasterSeed : ProbComp MasterSeed) from rfl,
    SampleableType.prEvent_uniformSample]
  have hcard : (Finset.univ.filter (SeedHit input)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro seed hseed seed' hseed'
    exact seedHit_unique (Finset.mem_filter.mp hseed).2 (Finset.mem_filter.mp hseed').2
  rw [show Fintype.card MasterSeed = 2 ^ 256 by simp, Nat.cast_pow, Nat.cast_ofNat]
  exact ENNReal.div_le_div_right (by exact_mod_cast hcard) _

/-- One step of an adaptive guessing strategy.

It holds the input that it tests, and its next state for each answer of the test. -/
structure Trial (σ : Type) where
  input : HashInput
  next : Bool → σ

end SphincsSecurity.Security.SeedGuess
