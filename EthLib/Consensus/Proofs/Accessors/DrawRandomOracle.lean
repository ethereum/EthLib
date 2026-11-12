module

public import EthLib.Consensus.Proofs.Accessors.DrawProbability
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-!
# Proofs: balance-weighted draws with a cached random oracle

The oracle answers in place of the SHA-256 call that gives a draw its random bytes.

A draw whose input is absent from the cache has the acceptance probability of a uniform digest.

These probabilities hold for the oracle only; no theorem bounds the draw when SHA-256 answers.

The seed is fixed, and freshness is a condition on the hashed input of the draw's block of draws.

No theorem here covers seed derivation or the whole proposer search.
-/

@[expose] public section

namespace EthLib.Consensus

open Base OracleComp OracleSpec ENNReal

/-- The proposer draw with its hash call exposed to a shared oracle. -/
def queryProposerDraw (preset : Preset) (fork : Base.Fork) (seed : Bytes32) (i : Nat)
    (balance : Gwei) : OracleComp (ByteArray →ₒ Bytes32) (Except AccessorError Bool) :=
  (fun random => drawAccepts preset fork random i balance) <$>
    liftM ((ByteArray →ₒ Bytes32).query (drawInput seed (i / drawsPerHash fork)))

/-- Answering the exposed hash call with SHA-256 gives the specified proposer draw. -/
theorem evalWithAnswerFn_queryProposerDraw (preset : Preset) (fork : Base.Fork) (seed : Bytes32)
    (i : Nat) (balance : Gwei) :
    evalWithAnswerFn (QueryImpl.ofFn Cryptography.Hash.Sha256.hash32)
      (queryProposerDraw preset fork seed i balance) = proposerDraw preset fork seed i balance := by
  rfl

private theorem run_queryProposerDraw_of_fresh (preset : Preset) (fork : Base.Fork)
    (seed : Bytes32) (i : Nat) (balance : Gwei) (cache : (ByteArray →ₒ Bytes32).QueryCache)
    (fresh : cache (drawInput seed (i / drawsPerHash fork)) = none) :
    (simulateQ (ByteArray →ₒ Bytes32).randomOracle
      (queryProposerDraw preset fork seed i balance)).run cache =
      (fun random => (drawAccepts preset fork random i balance,
        cache.cacheQuery (drawInput seed (i / drawsPerHash fork)) random)) <$> ($ᵗ Bytes32) := by
  simp only [queryProposerDraw, simulateQ_map, simulateQ_spec_query, StateT.run_map,
    randomOracle.run_eq, fresh, map_bind, map_pure]
  rw [map_eq_bind_pure_comp]
  rfl

/-- Before Electra, a fresh draw input accepts with probability `(⌊e * (2^8 - 1) / M⌋ + 1) / 2^8`.

It needs `0 < M`, `e ≤ M` and `M * (2^8 - 1) < 2^64`, where `M` is the largest effective balance.

Other inputs may already have answers in the shared cache. -/
theorem prEvent_queryProposerDraw_of_before_pectra (preset : Preset) (fork : Base.Fork)
    (before : ¬ .pectra ≤ fork) (seed : Bytes32) (i : Nat) (e : Gwei)
    (cache : (ByteArray →ₒ Bytes32).QueryCache)
    (fresh : cache (drawInput seed (i / drawsPerHash fork)) = none)
    (positive : 0 < preset.MAX_EFFECTIVE_BALANCE.toNat)
    (balance : e.toNat ≤ preset.MAX_EFFECTIVE_BALANCE.toNat)
    (fits : preset.MAX_EFFECTIVE_BALANCE.toNat * (2 ^ 8 - 1) < 2 ^ 64) :
    Pr{let z ← (simulateQ (ByteArray →ₒ Bytes32).randomOracle
      (queryProposerDraw preset fork seed i e)).run cache}[z.1 = .ok true] =
      ((e.toNat * (2 ^ 8 - 1) / preset.MAX_EFFECTIVE_BALANCE.toNat + 1 : Nat) : ℝ≥0∞) /
        2 ^ 8 := by
  rw [run_queryProposerDraw_of_fresh preset fork seed i e cache fresh, prEvent_map]
  exact prEvent_drawAccepts_uniform_of_before_pectra preset fork before i e positive balance fits

/-- From Electra, a fresh draw input accepts with probability `(⌊e * (2^16 - 1) / M⌋ + 1) / 2^16`.

It needs `0 < M`, `e ≤ M` and `M * (2^16 - 1) < 2^64`, where `M` is the largest effective balance.

Other inputs may already have answers in the shared cache. -/
theorem prEvent_queryProposerDraw_of_pectra (preset : Preset) (fork : Base.Fork)
    (electra : .pectra ≤ fork) (seed : Bytes32) (i : Nat) (e : Gwei)
    (cache : (ByteArray →ₒ Bytes32).QueryCache)
    (fresh : cache (drawInput seed (i / drawsPerHash fork)) = none)
    (positive : 0 < preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat)
    (balance : e.toNat ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat)
    (fits : preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat * (2 ^ 16 - 1) < 2 ^ 64) :
    Pr{let z ← (simulateQ (ByteArray →ₒ Bytes32).randomOracle
      (queryProposerDraw preset fork seed i e)).run cache}[z.1 = .ok true] =
      ((e.toNat * (2 ^ 16 - 1) / preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat + 1 : Nat) : ℝ≥0∞) /
        2 ^ 16 := by
  rw [run_queryProposerDraw_of_fresh preset fork seed i e cache fresh, prEvent_map]
  exact prEvent_drawAccepts_uniform_of_pectra preset fork electra i e positive balance fits

/-- Two distinct inputs absent from the shared cache both accept with the product probability.

The factors are the acceptance probabilities of two uniform digests.

This does not cover two draws that share an input, and so read one digest. -/
theorem prEvent_queryProposerDraw_pair_of_fresh (preset : Preset) (fork : Base.Fork)
    (seed : Bytes32) (i j : Nat) (e f : Gwei) (cache : (ByteArray →ₒ Bytes32).QueryCache)
    (different : drawInput seed (i / drawsPerHash fork) ≠ drawInput seed (j / drawsPerHash fork))
    (leftFresh : cache (drawInput seed (i / drawsPerHash fork)) = none)
    (rightFresh : cache (drawInput seed (j / drawsPerHash fork)) = none) :
    Pr{let z ← (simulateQ (ByteArray →ₒ Bytes32).randomOracle (do
      let left ← queryProposerDraw preset fork seed i e
      let right ← queryProposerDraw preset fork seed j f
      pure (left, right))).run cache}[z.1.1 = .ok true ∧ z.1.2 = .ok true] =
      Pr{let random ← $ᵗ Bytes32}[drawAccepts preset fork random i e = .ok true] *
        Pr{let random ← $ᵗ Bytes32}[drawAccepts preset fork random j f = .ok true] := by
  -- Caching the first answer leaves the second, distinct input fresh.
  have after (random : Bytes32) :
      (cache.cacheQuery (drawInput seed (i / drawsPerHash fork)) random)
        (drawInput seed (j / drawsPerHash fork)) = none := by
    rw [QueryCache.cacheQuery_of_ne _ _ different.symm, rightFresh]
  have secondRun (random : Bytes32) := run_queryProposerDraw_of_fresh preset fork seed j f
    (cache.cacheQuery (drawInput seed (i / drawsPerHash fork)) random) (after random)
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [run_queryProposerDraw_of_fresh preset fork seed i e cache leftFresh]
  simp only [bind_map_left]
  simp_rw [secondRun]
  simp only [bind_map_left]
  simpa only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def] using
    prEvent_bind_bind_and ($ᵗ Bytes32) ($ᵗ Bytes32)
    (fun random => drawAccepts preset fork random i e = .ok true)
    (fun random => drawAccepts preset fork random j f = .ok true)

end EthLib.Consensus
