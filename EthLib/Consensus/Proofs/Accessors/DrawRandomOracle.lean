module

public import EthLib.Consensus.Proofs.Accessors.DrawProbability
public import EthLib.Cryptography.Proofs.RandomOracleTable

/-!
# Proofs: balance-weighted draws with a cached random oracle

The oracle answers in place of the SHA-256 call that gives a draw its random bytes.

A draw whose input is absent from the cache has the acceptance probability of a uniform digest.

These probabilities hold for the oracle only; no theorem bounds the draw when SHA-256 answers.

The seed is fixed.

A draw is fresh when the input its block of draws hashes has no answer in the cache yet.

With fresh inputs and bounded balances, the first draws of one seed have independent outcomes.

The same draw serves the proposer, the sync committee and the payload timeliness committee.

The balance of each draw is given: the shuffle that picks the candidates is not modelled.

The cache may hold other answers, such as those of shuffle inputs.

The draws are made whether or not an earlier one accepts.

A search that stops at its first acceptance reads a prefix of them.

No theorem here covers seed derivation.
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

/-- The first `n` draws of one seed, each with its hash call exposed to a shared oracle.

Draw `i` weighs a candidate whose effective balance is the `i`-th given balance. -/
def queryDraws (preset : Preset) (fork : Base.Fork) (seed : Bytes32) (balance : Nat → Gwei)
    (n : Nat) : OracleComp (ByteArray →ₒ Bytes32) (List (Except AccessorError Bool)) :=
  (List.range n).mapM fun i => queryProposerDraw preset fork seed i (balance i)

/-- Answering the exposed hash calls with SHA-256 gives the specified draws. -/
theorem evalWithAnswerFn_queryDraws (preset : Preset) (fork : Base.Fork) (seed : Bytes32)
    (balance : Nat → Gwei) (n : Nat) :
    evalWithAnswerFn (QueryImpl.ofFn Cryptography.Hash.Sha256.hash32)
      (queryDraws preset fork seed balance n) =
      (List.range n).map fun i => proposerDraw preset fork seed i (balance i) := by
  unfold queryDraws
  induction (List.range n) with
  | nil => rfl
  | cons x L ih =>
    rw [List.mapM_cons, List.map_cons, ← evalWithAnswerFn_queryProposerDraw, ← ih]
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]

/-- Draws that share a uniform digest per block are equal in distribution to independent draws.

Each draw reads its own positions of the digest, and no two draws of one block share a position.

The table has one more cell than there are draws, so every block and every draw has a cell. -/
private theorem evalDistEq_uniformSample_blocks {β : Type} (n d k : Nat)
    (h : Nat → Bytes32 → β) (H : Nat → (Fin k → UInt8) → β) (pos : Nat → Fin k → Fin 32)
    (reads : ∀ i random, h i random = H i fun j => random[(pos i j).val])
    (apart : ∀ i i' j j', i / d = i' / d → pos i j = pos i' j' → i = i' ∧ j = j') :
    ((fun T : Fin (n + 1) → Bytes32 => (List.range n).map fun i =>
      h i (T ⟨i / d % (n + 1), Nat.mod_lt _ n.succ_pos⟩)) <$> ($ᵗ (Fin (n + 1) → Bytes32))) =ᵈ
      ((fun S : Fin (n + 1) → Bytes32 => (List.range n).map fun i =>
        h i (S ⟨i % (n + 1), Nat.mod_lt _ n.succ_pos⟩)) <$> ($ᵗ (Fin (n + 1) → Bytes32))) := by
  let cell (i : Nat) : Fin (n + 1) := ⟨i % (n + 1), Nat.mod_lt _ n.succ_pos⟩
  let block (i : Nat) : Fin (n + 1) := ⟨i / d % (n + 1), Nat.mod_lt _ n.succ_pos⟩
  let common (W : Fin (n + 1) × Fin k → UInt8) : List β :=
    (List.range n).map fun i => H i fun j => W (cell i, j)
  -- Both tables of digests give a uniform table of the bytes that the draws read.
  have side (place : Nat → Fin (n + 1))
      (distinct : Function.Injective fun a : Fin (n + 1) × Fin k => (place a.1.val, pos a.1 a.2)) :
      ((fun T : Fin (n + 1) → Bytes32 => (List.range n).map fun i => h i (T (place i))) <$>
        ($ᵗ (Fin (n + 1) → Bytes32))) =ᵈ (common <$> ($ᵗ (Fin (n + 1) × Fin k → UInt8))) := by
    refine EvalDistEq.trans (EvalDistEq.of_eq ?_)
      ((evalDistEq_uniformSample_table_reads distinct).map common)
    rw [Functor.map_map]
    congr 1
    funext T
    refine List.map_congr_left fun i hi => ?_
    have small : i < n + 1 := by have := List.mem_range.mp hi; omega
    have same : (cell i).val = i := Nat.mod_eq_of_lt small
    rw [reads]
    simp only [same]
  refine (side block ?_).trans (side cell ?_).symm
  · rintro ⟨a, j⟩ ⟨b, l⟩ equal
    simp only [Prod.mk.injEq, block, Fin.mk.injEq] at equal
    rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt),
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) b.isLt)] at equal
    obtain ⟨first, second⟩ := apart _ _ _ _ equal.1 equal.2
    exact Prod.ext (Fin.ext first) second
  · rintro ⟨a, j⟩ ⟨b, l⟩ equal
    simp only [Prod.mk.injEq, cell, Fin.mk.injEq] at equal
    rw [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at equal
    obtain ⟨cells, places⟩ := equal
    exact Prod.ext (Fin.ext cells) (apart _ _ _ _ (by rw [cells]) places).2

/-- Each draw reads one byte of its digest before Electra and two bytes from Electra.

No two draws of one block read the same byte. -/
private theorem drawAccepts_reads (preset : Preset) (fork : Base.Fork) (balance : Nat → Gwei) :
    ∃ (k : Nat) (H : Nat → (Fin k → UInt8) → Except AccessorError Bool)
      (pos : Nat → Fin k → Fin 32),
      (∀ i random, drawAccepts preset fork random i (balance i) =
        H i fun j => random[(pos i j).val]) ∧
      ∀ i i' j j', i / drawsPerHash fork = i' / drawsPerHash fork → pos i j = pos i' j' →
        i = i' ∧ j = j' := by
  by_cases electra : .pectra ≤ fork
  · refine ⟨2, fun i bytes => drawAccepts preset fork (Vector.ofFn fun t : Fin 32 =>
      if t.val = i % 16 * 2 then bytes 0 else bytes 1) i (balance i),
      fun i j => ⟨i % 16 * 2 + j.val, by have := Nat.mod_lt i (show 16 > 0 by decide); omega⟩,
      fun i random => ?_, fun i i' j j' blocks places => ?_⟩
    · simp only [drawAccepts, electra, ↓reduceIte, Vector.getElem_ofFn]
      simp
    · simp only [drawsPerHash, electra, ↓reduceIte, Fin.mk.injEq] at blocks places
      have left := Nat.mod_add_div i 16
      have right := Nat.mod_add_div i' 16
      have := j.isLt
      have := j'.isLt
      exact ⟨by omega, Fin.ext (by omega)⟩
  · refine ⟨1, fun i bytes => drawAccepts preset fork (Vector.replicate 32 (bytes 0)) i (balance i),
      fun i _ => ⟨i % 32, Nat.mod_lt i (by decide)⟩, fun i random => ?_,
      fun i i' j j' blocks places => ?_⟩
    · simp only [drawAccepts, electra, ↓reduceIte, Vector.getElem_replicate]
    · simp only [drawsPerHash, electra, ↓reduceIte, Fin.mk.injEq] at blocks places
      have left := Nat.mod_add_div i 32
      have right := Nat.mod_add_div i' 32
      exact ⟨by omega, Subsingleton.elim _ _⟩

/-- The first `n` draws of one seed behave as draws on independent uniform digests.

This holds when no draw input of the seed has an answer in the shared cache yet.

It needs at most `2^64` draws, as many as the 64-bit counter of the search allows.

The draws of one block read one answer at disjoint bytes, so they stay independent. -/
theorem run_queryDraws_evalDistEq (preset : Preset) (fork : Base.Fork) (seed : Bytes32)
    (balance : Nat → Gwei) (n : Nat) (cache : (ByteArray →ₒ Bytes32).QueryCache)
    (bounded : n ≤ 2 ^ 64)
    (fresh : ∀ i < n, cache (drawInput seed (i / drawsPerHash fork)) = none) :
    ((simulateQ (ByteArray →ₒ Bytes32).randomOracle
      (queryDraws preset fork seed balance n)).run' cache) =ᵈ
      (List.range n).mapM fun i =>
        (fun random => drawAccepts preset fork random i (balance i)) <$> ($ᵗ Bytes32) := by
  obtain ⟨k, H, pos, reads, apart⟩ := drawAccepts_reads preset fork balance
  let block (i : Nat) : Fin (n + 1) := ⟨i / drawsPerHash fork % (n + 1), Nat.mod_lt _ n.succ_pos⟩
  let cell (i : Nat) : Fin (n + 1) := ⟨i % (n + 1), Nat.mod_lt _ n.succ_pos⟩
  -- Draws of one block hash one input, and distinct blocks below `2^64` hash distinct inputs.
  have same : ∀ i ∈ List.range n, ∀ j ∈ List.range n,
      drawInput seed (i / drawsPerHash fork) = drawInput seed (j / drawsPerHash fork) ↔
        block i = block j := by
    intro i hi j hj
    have left : i / drawsPerHash fork < n := lt_of_le_of_lt (Nat.div_le_self _ _)
      (List.mem_range.mp hi)
    have right : j / drawsPerHash fork < n := lt_of_le_of_lt (Nat.div_le_self _ _)
      (List.mem_range.mp hj)
    rw [drawInput_eq_iff (by omega) (by omega), Fin.ext_iff]
    simp only [block, Nat.mod_eq_of_lt (Nat.lt_succ_of_lt left),
      Nat.mod_eq_of_lt (Nat.lt_succ_of_lt right), true_and]
  have distinct : ((List.range n).map cell).Nodup := by
    refine List.Nodup.map_on (fun i hi j hj equal => ?_) List.nodup_range
    have left := List.mem_range.mp hi
    have right := List.mem_range.mp hj
    simpa [cell, Fin.ext_iff, Nat.mod_eq_of_lt (Nat.lt_succ_of_lt left),
      Nat.mod_eq_of_lt (Nat.lt_succ_of_lt right)] using equal
  refine (run_mapM_query_evalDistEq (fun i => drawInput seed (i / drawsPerHash fork)) block
    (fun i random => drawAccepts preset fork random i (balance i)) (List.range n) same
    cache).trans ((EvalDistEq.of_eq ?_).trans ((evalDistEq_uniformSample_blocks n
      (drawsPerHash fork) k _ H pos reads apart).trans
      (mapM_uniformSample_evalDistEq cell
        (fun i random => drawAccepts preset fork random i (balance i)) (List.range n)
        distinct).symm))
  congr 1
  funext T
  refine List.map_congr_left fun i hi => ?_
  rw [fresh i (List.mem_range.mp hi)]
  rfl

/-- The first `n` draws have the product chance, from the chance of each draw to accept.

Each draw must return a verdict rather than fail. -/
private theorem prEvent_queryDraws_of_chance (preset : Preset) (fork : Base.Fork) (seed : Bytes32)
    (balance : Nat → Gwei) (n : Nat) (cache : (ByteArray →ₒ Bytes32).QueryCache)
    (bounded : n ≤ 2 ^ 64)
    (fresh : ∀ i < n, cache (drawInput seed (i / drawsPerHash fork)) = none)
    (chance : Nat → ℝ≥0∞)
    (verdict : ∀ i < n, ∀ random, ∃ b, drawAccepts preset fork random i (balance i) = .ok b)
    (accepts : ∀ i < n,
      Pr{let random ← $ᵗ Bytes32}[drawAccepts preset fork random i (balance i) = .ok true] =
        chance i)
    (outcome : Nat → Bool) :
    Pr{let z ← (simulateQ (ByteArray →ₒ Bytes32).randomOracle
      (queryDraws preset fork seed balance n)).run' cache}[
        z = (List.range n).map fun i => .ok (outcome i)] =
      ∏ i ∈ Finset.range n, if outcome i then chance i else 1 - chance i := by
  rw [(run_queryDraws_evalDistEq preset fork seed balance n cache bounded fresh).prEvent_eq,
    prEvent_mapM_eq_map, ← List.toFinset_range, List.prod_toFinset _ List.nodup_range]
  refine congrArg List.prod (List.map_congr_left fun i hi => ?_)
  have small := List.mem_range.mp hi
  rw [prEvent_map]
  cases outcome i with
  | true => exact accepts i small
  | false =>
    rw [← accepts i small, ← OracleComp.prEvent_not_eq_one_sub]
    refine prEvent_congr _ _ _ fun random => ?_
    obtain ⟨b, result⟩ := verdict i small random
    cases b <;> simp [result]

/-- Before Electra, the first `n` draws of one seed have independent outcomes.

Here `e_i` is the balance of draw `i` and `M` the largest effective balance.

Draw `i` accepts with chance `(⌊e_i * (2^8 - 1) / M⌋ + 1) / 2^8`, whatever earlier draws gave.

So each pattern of outcomes has the product chance.

It needs `0 < M`, each `e_i ≤ M` and `M * (2^8 - 1) < 2^64`.

It also needs at most `2^64` draws, and no draw input of the seed in the shared cache. -/
theorem prEvent_queryDraws_of_before_pectra (preset : Preset) (fork : Base.Fork)
    (before : ¬ .pectra ≤ fork) (seed : Bytes32) (balance : Nat → Gwei) (n : Nat)
    (cache : (ByteArray →ₒ Bytes32).QueryCache) (bounded : n ≤ 2 ^ 64)
    (fresh : ∀ i < n, cache (drawInput seed (i / drawsPerHash fork)) = none)
    (positive : 0 < preset.MAX_EFFECTIVE_BALANCE.toNat)
    (balances : ∀ i < n, (balance i).toNat ≤ preset.MAX_EFFECTIVE_BALANCE.toNat)
    (fits : preset.MAX_EFFECTIVE_BALANCE.toNat * (2 ^ 8 - 1) < 2 ^ 64) (outcome : Nat → Bool) :
    Pr{let z ← (simulateQ (ByteArray →ₒ Bytes32).randomOracle
      (queryDraws preset fork seed balance n)).run' cache}[
        z = (List.range n).map fun i => .ok (outcome i)] =
      ∏ i ∈ Finset.range n,
        let chance : ℝ≥0∞ := ((balance i).toNat * (2 ^ 8 - 1) /
          preset.MAX_EFFECTIVE_BALANCE.toNat + 1 : Nat) / 2 ^ 8
        if outcome i then chance else 1 - chance :=
  prEvent_queryDraws_of_chance preset fork seed balance n cache bounded fresh _
    (fun i small random => ⟨_, drawAccepts_eq_of_before_pectra preset fork before random i _ fits
      (balances i small)⟩)
    (fun i small => prEvent_drawAccepts_uniform_of_before_pectra preset fork before i _ positive
      (balances i small) fits) outcome

/-- From Electra, the first `n` draws of one seed have independent outcomes.

Here `e_i` is the balance of draw `i` and `M` the largest effective balance.

Draw `i` accepts with chance `(⌊e_i * (2^16 - 1) / M⌋ + 1) / 2^16`, whatever earlier draws gave.

So each pattern of outcomes has the product chance.

It needs `0 < M`, each `e_i ≤ M` and `M * (2^16 - 1) < 2^64`.

It also needs at most `2^64` draws, and no draw input of the seed in the shared cache. -/
theorem prEvent_queryDraws_of_pectra (preset : Preset) (fork : Base.Fork)
    (electra : .pectra ≤ fork) (seed : Bytes32) (balance : Nat → Gwei) (n : Nat)
    (cache : (ByteArray →ₒ Bytes32).QueryCache) (bounded : n ≤ 2 ^ 64)
    (fresh : ∀ i < n, cache (drawInput seed (i / drawsPerHash fork)) = none)
    (positive : 0 < preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat)
    (balances : ∀ i < n, (balance i).toNat ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat)
    (fits : preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat * (2 ^ 16 - 1) < 2 ^ 64)
    (outcome : Nat → Bool) :
    Pr{let z ← (simulateQ (ByteArray →ₒ Bytes32).randomOracle
      (queryDraws preset fork seed balance n)).run' cache}[
        z = (List.range n).map fun i => .ok (outcome i)] =
      ∏ i ∈ Finset.range n,
        let chance : ℝ≥0∞ := ((balance i).toNat * (2 ^ 16 - 1) /
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat + 1 : Nat) / 2 ^ 16
        if outcome i then chance else 1 - chance :=
  prEvent_queryDraws_of_chance preset fork seed balance n cache bounded fresh _
    (fun i small random => ⟨_, drawAccepts_eq_of_pectra preset fork electra random i _ fits
      (balances i small)⟩)
    (fun i small => prEvent_drawAccepts_uniform_of_pectra preset fork electra i _ positive
      (balances i small) fits) outcome

end EthLib.Consensus
