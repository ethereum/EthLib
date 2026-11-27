module

public import EthLib.Consensus.Proofs.Accessors.SearchRandomOracle
public import EthLib.Consensus.Proofs.ShufflePermutation

/-!
# Proofs: the proposer draw before Gloas ends with high probability in the random oracle model

The proposer of a slot is the first candidate whose draw accepts.

It is found whenever a balance-weighted search of one member succeeds, so that bound applies.

The bound holds for the oracle only; no theorem bounds the draw when SHA-256 answers.
-/

@[expose] public section

namespace EthLib.Consensus

open Base OracleComp OracleSpec ENNReal

/-- The proposer search, with the verdict of each draw given.

Draw `i` reads the candidate at position `order (i mod n)`, among `n` candidates.

The first candidate that a draw accepts is the proposer.

A verdict that is an error stops the search with that error.

The draw counter is a 64-bit integer, so the search fails when it would reach `2^64`. -/
def proposerOfVerdicts (verdict : Nat → Except AccessorError Bool)
    (indices : Array ValidatorIndex) (order : Nat → Nat) (i : Nat) :
    Except AccessorError ValidatorIndex := do
  if ← verdict i then return indices.getD (order (i % indices.size)) 0
  if next : i + 1 < 2 ^ 64 then proposerOfVerdicts verdict indices order (i + 1)
  else throw (.arith .overflow)
termination_by 2 ^ 64 - i

variable {preset : Preset} {fork : Base.Fork}

/-- The proposer search is the search on the verdicts of its draws.

Each candidate must name a validator, whose effective balance the draw weighs. -/
theorem proposerSearch_eq_proposerOfVerdicts {validators : Array Validator}
    {indices : Array ValidatorIndex} {balances : Array Gwei} {order : Nat → Nat}
    {seed : Bytes32} (nonempty : 0 < indices.size)
    (positions : ∀ place < indices.size, order place < indices.size)
    (weights : ∀ k (lt : k < indices.size), ∃ validator,
      validators[indices[k].toNat]? = some validator ∧
        balances.getD k 0 = validator.effectiveBalance) (i : Nat) :
    proposerSearch preset fork validators indices order seed i =
      proposerOfVerdicts (fun j => proposerDraw preset fork seed j
        (balances.getD (order (j % indices.size)) 0)) indices order i := by
  obtain ⟨left, leftEq⟩ : ∃ left, left = 2 ^ 64 - i := ⟨_, rfl⟩
  induction left using Nat.strongRecOn generalizing i with
  | _ left ih =>
  rw [proposerSearch, proposerOfVerdicts]
  have inside := positions _ (Nat.mod_lt i nonempty)
  obtain ⟨validator, registered, weight⟩ := weights _ inside
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside, Option.getD_some,
    registered, weight]
  simp only [bind, Except.bind]
  cases proposerDraw preset fork seed i validator.effectiveBalance with
  | error e => rfl
  | ok accepted =>
    cases accepted
    · simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases next : i + 1 < 2 ^ 64
      · simp only [next, ↓reduceDIte]
        exact ih _ (leftEq ▸ Nat.sub_lt_sub_left (by omega) (Nat.lt_succ_self i)) _ rfl
      · simp only [next, ↓reduceDIte]
    · rfl

/-- The proposer search reads only the verdicts from its current draw number up to `2^64`. -/
private theorem proposerOfVerdicts_congr {verdict other : Nat → Except AccessorError Bool}
    {indices : Array ValidatorIndex} {order : Nat → Nat} :
    ∀ left, ∀ {i : Nat}, left = 2 ^ 64 - i → i < 2 ^ 64 →
      (∀ j, i ≤ j → j < 2 ^ 64 → verdict j = other j) →
      proposerOfVerdicts verdict indices order i = proposerOfVerdicts other indices order i := by
  intro left
  induction left using Nat.strongRecOn with
  | _ left ih =>
  intro i leftEq small same
  rw [proposerOfVerdicts.eq_1 verdict, proposerOfVerdicts.eq_1 other, same i le_rfl small]
  cases other i with
  | error e => rfl
  | ok accepted =>
    simp only [bind, Except.bind]
    cases accepted
    · simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases next : i + 1 < 2 ^ 64
      · simp only [next, ↓reduceDIte]
        exact ih _ (leftEq ▸ Nat.sub_lt_sub_left (by omega) (Nat.lt_succ_self i)) rfl next
          fun j low high => same j (by omega) high
      · simp only [next, ↓reduceDIte]
    · rfl

/-- A search of one member that succeeds finds the proposer, from the same verdicts.

The converse fails at the last draw: there the proposer search accepts, and the search fails. -/
theorem proposerOfVerdicts_of_searchOfVerdicts {verdict : Nat → Except AccessorError Bool}
    {indices : Array ValidatorIndex} {order : Nat → Nat}
    {bound : (#[] : Array ValidatorIndex).size ≤ 1} {i : Nat} {result : Vector ValidatorIndex 1}
    (found : searchOfVerdicts verdict indices order 1 #[] bound i = .ok result) :
    proposerOfVerdicts verdict indices order i = .ok result[0] := by
  obtain ⟨left, leftEq⟩ : ∃ left, left = 2 ^ 64 - i := ⟨_, rfl⟩
  induction left using Nat.strongRecOn generalizing i with
  | _ left ih =>
  rw [searchOfVerdicts] at found
  rw [proposerOfVerdicts]
  simp only [Array.size_empty, Nat.zero_ne_one, ↓reduceDIte, bind, Except.bind] at found
  simp only [bind, Except.bind]
  cases draw : verdict i with
  | error e => simp [draw] at found
  | ok accepted =>
    simp only [draw] at found ⊢
    split at found
    · rename_i next
      cases accepted
      · simp only [Bool.false_eq_true, ↓reduceIte] at found ⊢
        simp only [next, ↓reduceDIte]
        exact ih _ (leftEq ▸ Nat.sub_lt_sub_left (by omega) (Nat.lt_succ_self i)) found rfl
      · simp only [↓reduceIte] at found ⊢
        unfold searchOfVerdicts at found
        simp only [Array.size_push, Array.size_empty, Nat.zero_add, ↓reduceDIte] at found
        cases found
        rfl
    · simp [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at found

/-- The proposer search, with its hash calls exposed to a shared oracle.

It makes the `2^64` draws of the seed up front, then searches on their verdicts. -/
def queryProposerSearch (preset : Preset) (fork : Base.Fork) (indices : Array ValidatorIndex)
    (balances : Array Gwei) (order : Nat → Nat) (seed : Bytes32) :
    OracleComp (ByteArray →ₒ Bytes32) (Except AccessorError ValidatorIndex) :=
  -- The draws are those of a balance-weighted search on the same candidates.
  (fun draws => proposerOfVerdicts (fun i => draws.getD i (.ok false)) indices order 0) <$>
    queryDraws preset fork seed (fun i => balances.getD (order (i % indices.size)) 0) (2 ^ 64)

/-- Answering the exposed hash calls with SHA-256 gives the specified proposer search.

Each candidate must name a validator, whose effective balance the draw weighs. -/
theorem evalWithAnswerFn_queryProposerSearch {validators : Array Validator}
    {indices : Array ValidatorIndex} {balances : Array Gwei} {order : Nat → Nat}
    (seed : Bytes32) (nonempty : 0 < indices.size)
    (positions : ∀ place < indices.size, order place < indices.size)
    (weights : ∀ k (lt : k < indices.size), ∃ validator,
      validators[indices[k].toNat]? = some validator ∧
        balances.getD k 0 = validator.effectiveBalance) :
    evalWithAnswerFn (QueryImpl.ofFn Cryptography.Hash.Sha256.hash32)
      (queryProposerSearch preset fork indices balances order seed) =
      proposerSearch preset fork validators indices order seed 0 := by
  rw [proposerSearch_eq_proposerOfVerdicts nonempty positions weights, queryProposerSearch,
    map_eq_bind_pure_comp, evalWithAnswerFn_bind, evalWithAnswerFn_queryDraws]
  -- A `simp` here diverges on the range of `2^64` draws, so the rewrites are explicit.
  rw [Function.comp_apply, evalWithAnswerFn_pure]
  exact proposerOfVerdicts_congr _ rfl (Nat.two_pow_pos 64) fun j _ small =>
    getD_map_range _ _ small

/-- The proposer draw is the proposer search on the shuffled order.

Before Gloas it gives the proposer of a slot.

It needs at least one candidate, at most `2^40` of them, and each must name a validator. -/
theorem computeProposerIndex_eq_evalWithAnswerFn {state : BeaconState preset fork}
    {indices : Array ValidatorIndex} {balances : Array Gwei} {seed : Bytes32}
    (nonempty : 0 < indices.size) (few : indices.size ≤ 2 ^ 40)
    (weights : ∀ k (lt : k < indices.size), ∃ validator,
      state.validators.data[indices[k].toNat]? = some validator ∧
        balances.getD k 0 = validator.effectiveBalance) :
    computeProposerIndex state indices seed =
      evalWithAnswerFn (QueryImpl.ofFn Cryptography.Hash.Sha256.hash32)
        (queryProposerSearch preset fork indices balances
          (Shuffle.shuffledIndexBy
            (Shuffle.pivots preset.SHUFFLE_ROUND_COUNT.toNat seed indices.size) seed
            indices.size) seed) := by
  -- The shuffle keeps each position below the count.
  have positions : ∀ place < indices.size, Shuffle.shuffledIndexBy
      (Shuffle.pivots preset.SHUFFLE_ROUND_COUNT.toNat seed indices.size) seed indices.size place <
        indices.size :=
    fun place lt => Shuffle.shuffledIndex_lt lt
  rw [evalWithAnswerFn_queryProposerSearch seed nonempty positions weights]
  unfold computeProposerIndex
  simp only [Nat.pos_iff_ne_zero.mp nonempty, show indices.size < 2 ^ 64 by omega,
    show ¬2 ^ 40 < indices.size by omega, ↓reduceIte]

/-- The proposer search fails with probability at most `(1 - 2^-b)^(2^64 - 1)`.

Here `b` is the number of random bits that a draw reads.

It fails only when a balance-weighted search of one member fails, so that bound applies.

The seed, the candidates, their balances and their order are fixed before the draws are answered.

The bound holds for every order, so the shuffle that gives it is not modelled. -/
theorem prEvent_queryProposerSearch_fails_le (preset : Preset) (fork : Base.Fork)
    -- The products of a draw must fit in 64 bits, and the cap must be positive.
    (fits : DrawFits preset fork) (positive : 0 < drawCap preset fork)
    (indices : Array ValidatorIndex) (balances : Array Gwei) (order : Nat → Nat)
    (seed : Bytes32) (cache : (ByteArray →ₒ Bytes32).QueryCache)
    -- There must be at least one candidate.
    (nonempty : 0 < indices.size)
    -- Every balance read must be at most the cap.
    (capped : ∀ j < indices.size, (balances.getD (order j) 0).toNat ≤ drawCap preset fork)
    -- The cache must hold no draw input of the seed.
    (fresh : ∀ i < 2 ^ 64, cache (drawInput seed (i / drawsPerHash fork)) = none) :
    Pr{let z ← (simulateQ (ByteArray →ₒ Bytes32).randomOracle
      (queryProposerSearch preset fork indices balances order seed)).run' cache}[z.isOk = false] ≤
      (1 - (2 ^ drawBits fork : ℝ≥0∞)⁻¹) ^ (2 ^ 64 - 1) := by
  calc _ ≤ Pr{let z ← (simulateQ (ByteArray →ₒ Bytes32).randomOracle
        (querySearch preset fork indices balances order seed 1)).run' cache}[z.isOk = false] := by
        rw [queryProposerSearch, querySearch, simulateQ_map, simulateQ_map, StateT.run'_map',
          StateT.run'_map', prEvent_map, prEvent_map]
        -- On the same draws, a failed proposer search means a failed search of one member.
        refine prEvent_mono _ _ _ fun draws fails => ?_
        cases searched : searchOfVerdicts (fun i => draws.getD i (.ok false)) indices order 1 #[]
          (Nat.zero_le _) 0 with
        | error e => rfl
        | ok result =>
          rw [proposerOfVerdicts_of_searchOfVerdicts searched] at fails
          cases fails
    _ ≤ (1 : Nat) * (1 - (2 ^ drawBits fork : ℝ≥0∞)⁻¹) ^ ((2 ^ 64 - 1) / 1) :=
        prEvent_querySearch_fails_le preset fork fits positive indices balances order seed 1 cache
          nonempty capped fresh
    _ = _ := by simp

end EthLib.Consensus
