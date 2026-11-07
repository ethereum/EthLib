module

public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.Proofs.PayloadTimeliness
public import EthLib.Consensus.Proposers

/-!
# Proofs: the proposers of an epoch

The proposer of a slot is one of the candidates it is drawn from.

From Gloas each candidate is active and unslashed, so each proposer is too.

A balance-weighted selection of one proposer draws the same proposer as the proposer search.

So from Electra, the Gloas selection of a proposer agrees with the earlier draw.

Moving the lookahead shifts every proposer back by one epoch, and fills the last epoch anew.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {state : BeaconState preset fork}

/-- The proposer of a slot is one of its candidates. -/
theorem mem_of_computeSlotProposer {indices : Array ValidatorIndex} {seed : Bytes32}
    {proposer : ValidatorIndex} (computed : computeSlotProposer state indices seed = .ok proposer) :
    proposer ∈ indices := by
  unfold computeSlotProposer at computed
  split at computed
  · obtain ⟨selected, chosen, rest⟩ := bind_ok_iff.mp computed
    cases rest
    exact mem_of_computeBalanceWeightedSelection chosen _ (by simp)
  · exact mem_of_computeProposerIndex computed

/-- Each proposer of an epoch is one of the candidates. -/
theorem mem_of_computeProposerIndices {epoch : Epoch} {seed : Bytes32}
    {indices : Array ValidatorIndex}
    {proposers : Vector ValidatorIndex preset.SLOTS_PER_EPOCH.toNat}
    (computed : computeProposerIndices state epoch seed indices = .ok proposers) :
    ∀ proposer ∈ proposers.toList, proposer ∈ indices := by
  unfold computeProposerIndices at computed
  obtain ⟨start, -, drawn⟩ := bind_ok_iff.mp computed
  intro proposer member
  obtain ⟨i, inside, rfl⟩ := List.getElem_of_mem member
  have entry := vector_mapM_ok_getElem drawn (i := i) (by simpa using inside)
  obtain ⟨slot, -, slotProposer⟩ := bind_ok_iff.mp entry
  simpa using mem_of_computeSlotProposer slotProposer

/-- From Gloas, each candidate to propose is active and unslashed. -/
theorem proposerCandidates_spec (gloas : .glamsterdam ≤ fork) {epoch : Epoch}
    {index : ValidatorIndex} (member : index ∈ proposerCandidates state epoch) :
    index ∈ getActiveValidatorIndices state epoch ∧
      ∀ validator, state.validators.data[index.toNat]? = some validator →
        validator.slashed = false := by
  simp only [proposerCandidates, gloas, ↓reduceIte, Array.mem_filter, List.mem_toArray] at member
  refine ⟨member.1, fun validator found => ?_⟩
  have := member.2
  rw [found] at this
  simpa using this

/-- From Electra, the proposer draw of every fork is the draw on two random bytes. -/
theorem proposerDraw_of_pectra {fork' : Base.Fork} (electra : .pectra ≤ fork)
    (electra' : .pectra ≤ fork') (seed : Bytes32) (i : Nat) (balance : Gwei) :
    proposerDraw preset fork seed i balance = proposerDraw preset fork' seed i balance := by
  simp only [proposerDraw, drawAccepts, drawHash, drawsPerHash, electra, electra', ↓reduceIte]

/-- A selection of one candidate that succeeds draws the proposer that the proposer search draws.

The two walk the candidates in the same shuffled order, and draw on the same random bytes.

Each candidate must name a validator, whose effective balance the selection reads. -/
theorem proposerSearch_of_balanceWeightedSearch
    {validators : Array Validator} {indices : Array ValidatorIndex} {balances : Array Gwei}
    {shuffled : Array UInt64} {seed : Bytes32} (nonempty : 0 < indices.size)
    (positions : ∀ place < indices.size, (shuffled.getD place 0).toNat < indices.size)
    (weights : ∀ k (lt : k < indices.size), ∃ validator,
      validators[indices[k].toNat]? = some validator ∧
        balances.getD k 0 = validator.effectiveBalance) :
    ∀ {bound : (#[] : Array ValidatorIndex).size ≤ 1} {i : Nat}
      {random : { random // random = drawHash fork seed i }} {result : Vector ValidatorIndex 1},
      balanceWeightedSearch preset fork indices balances
          (fun place => (shuffled.getD place 0).toNat)
          seed 1 #[] bound i random = .ok result →
        proposerSearch preset fork validators indices shuffled seed i = .ok result[0] := by
  intro bound i random result found
  obtain ⟨left, leftEq⟩ : ∃ left, left = 2 ^ 64 - i := ⟨_, rfl⟩
  induction left using Nat.strongRecOn generalizing i random with
  | _ left ih =>
    unfold balanceWeightedSearch at found
    -- The carried hash is the hash of the block of the draw, so the draw is the proposer draw.
    have carried : drawAccepts preset fork random.1 i =
        proposerDraw preset fork seed i := by
      rw [random.2]
      rfl
    split at found
    · simp at *
    simp only [bind, Except.bind] at found
    have inside := positions _ (Nat.mod_lt i nonempty)
    obtain ⟨validator, registered, weight⟩ := weights _ inside
    have candidate : indices.getD (shuffled.getD (i % indices.size) 0).toNat 0 =
        indices[(shuffled.getD (i % indices.size) 0).toNat] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside, Option.getD_some]
    rw [weight, carried] at found
    rw [proposerSearch, candidate, registered]
    simp only [bind, Except.bind]
    cases draw : proposerDraw preset fork seed i validator.effectiveBalance with
    | error e => simp [draw] at found
    | ok accepted =>
      simp only [draw] at found ⊢
      split at found
      · rename_i next
        cases accepted
        · simp only [Bool.false_eq_true, ↓reduceIte] at found ⊢
          simp only [next, ↓reduceDIte]
          exact ih (2 ^ 64 - (i + 1)) (by omega) found rfl
        · simp only [↓reduceIte] at found ⊢
          unfold balanceWeightedSearch at found
          simp only [Array.size_push, Array.size_empty, Nat.zero_add, ↓reduceDIte] at found
          cases found
          rfl
      · simp [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at found

/-- A selection of one proposer that succeeds draws the proposer of the draw at the same fork.

So the Gloas proposer of a slot is the one that the Fulu rule draws from the same candidates. -/
theorem computeProposerIndex_of_computeBalanceWeightedSelection
    {indices : Array ValidatorIndex} {seed : Bytes32} {selected : Vector ValidatorIndex 1}
    (computed : computeBalanceWeightedSelection state indices seed 1 true = .ok selected) :
    computeProposerIndex state indices seed = .ok selected[0] := by
  unfold computeBalanceWeightedSelection at computed
  by_cases empty : indices.size = 0
  · simp [empty, bind, Except.bind, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw] at computed
  by_cases fits : indices.size < 2 ^ 64
  · simp only [empty, fits, ↓reduceIte, bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
    rename_i balances read
    split at computed
    · cases computed
    rename_i guard
    have small : indices.size ≤ 2 ^ 40 := Nat.le_of_not_lt fun large => guard (by simp [large])
    have sizeEq : indices.size.toUInt64.toNat = indices.size := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt fits]
    have onList := congrArg (Array.toList <$> ·) read
    rw [Array.toList_mapM] at onList
    change _ = Except.ok balances.toList at onList
    have sizes : balances.size = indices.size := by
      simpa using mapM_ok_length onList
    -- Both read the shuffled position of each draw.
    have agree : ∀ place < indices.size,
        Shuffle.shuffledIndex preset.SHUFFLE_ROUND_COUNT.toNat seed indices.size place =
          ((Shuffle.shuffledPositions preset.SHUFFLE_ROUND_COUNT.toNat seed indices.size).getD
            place 0).toNat := by
      intro place lt
      rw [Array.getD_eq_getD_getElem?, Shuffle.shuffledPositions_getElem lt, Option.getD_some,
        UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans (Shuffle.shuffledIndex_lt lt) fits)]
    rw [balanceWeightedSearch_congr (Nat.pos_of_ne_zero empty) agree] at computed
    unfold computeProposerIndex
    simp only [empty, fits, ↓reduceIte, computeShuffledPermutation_eq (by rw [sizeEq]; exact small),
      sizeEq, Except.mapError, bind, Except.bind]
    refine proposerSearch_of_balanceWeightedSearch (Nat.pos_of_ne_zero empty)
      (fun place lt => ?_) (fun k lt => ?_) computed
    · exact Shuffle.shuffledPositions_getD_lt fits lt
    · have entry := mapM_ok_getElem onList k (by simpa using lt)
      simp only [Array.getElem_toList] at entry
      cases found : getValidator state indices[k] with
      | error e => simp [found] at entry
      | ok validator =>
        simp only [found, Except.ok.injEq] at entry
        refine ⟨validator, ?_, ?_⟩
        · unfold getValidator at found
          split at found <;> simp_all
        · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega),
            Option.getD_some]
          simpa using entry.symm
  · simp [empty, fits, bind, Except.bind, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw] at computed

/-- From Gloas, each proposer of an epoch is active in it and is not slashed. -/
theorem getBeaconProposerIndices_spec (gloas : .glamsterdam ≤ fork) {epoch : Epoch}
    {proposers : Vector ValidatorIndex preset.SLOTS_PER_EPOCH.toNat}
    (computed : getBeaconProposerIndices state epoch = .ok proposers) :
    ∀ proposer ∈ proposers.toList, proposer ∈ getActiveValidatorIndices state epoch ∧
      ∀ validator, state.validators.data[proposer.toNat]? = some validator →
        validator.slashed = false := by
  obtain ⟨seed, -, drawn⟩ := bind_ok_iff.mp computed
  intro proposer member
  exact proposerCandidates_spec gloas (mem_of_computeProposerIndices drawn proposer member)

/-- Moving the lookahead shifts every proposer back by one epoch.

The last epoch holds the proposers of the epoch after the seed lookahead. -/
theorem processProposerLookahead_spec {fulu : .fusaka ≤ fork}
    {after : BeaconState preset fork} (computed : processProposerLookahead state fulu = .ok after) :
    ∃ epoch last, epoch.toNat =
        (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 ∧
      getBeaconProposerIndices state epoch = .ok last ∧
      ∀ (position : Nat) (inside : position < _),
        (after.proposerLookahead fulu)[position]'inside =
          if kept : position + preset.SLOTS_PER_EPOCH.toNat <
              (state.proposerLookahead fulu).size then
            (state.proposerLookahead fulu)[position + preset.SLOTS_PER_EPOCH.toNat]
          else last[position + preset.SLOTS_PER_EPOCH.toNat -
            (state.proposerLookahead fulu).size]'(by simp only [Vector.size] at kept ⊢; omega) := by
  unfold processProposerLookahead at computed
  obtain ⟨epoch, counted, rest⟩ := bind_ok_iff.mp computed
  obtain ⟨last, drawn, kept⟩ := bind_ok_iff.mp rest
  simp only [liftArith, mapError_ok_iff, bind_ok_iff, addChecked_ok_iff] at counted
  obtain ⟨middle, ⟨_, first⟩, _, second⟩ := counted
  have one : (1 : UInt64).toNat = 1 := rfl
  refine ⟨epoch, last, by omega, drawn, fun position inside => ?_⟩
  cases kept
  simp

end EthLib.Consensus
