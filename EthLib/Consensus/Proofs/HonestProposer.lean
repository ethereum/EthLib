module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.DataAvailability.Blob
public import EthLib.Consensus.HonestProposer

/-!
# Proofs: what an honest proposer computes

Before Heze, the Eth1 vote of a proposer is the data of the state or the data of a candidate block.

So it never moves the deposit count of the state back.

When the votes of the state hold a candidate, the vote is one of them with the most copies there.

In Electra, the pending deposit count is the number of deposits that block processing expects.

With a signature that passes its check, a block that carries the new state root is valid.

The state after it then has that root.

The on-chain aggregate joins the network aggregates in the order of their committees.

The signed header of a block carries the root of its body.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-- Two errors with one code come from one constructor. -/
theorem ProposerError.code_injective (e₁ e₂ : ProposerError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Each code is one more than the index of its constructor.
  have back : ∀ e : ProposerError, e.code.toNat - 1 = e.ctorIdx := by
    intro e
    cases e <;> rfl
  rw [← back e₁, ← back e₂, h]

/-! ## The Eth1 vote -/

/-- A vote that beats another has at least as many copies. -/
theorem count_le_of_beatsVote {votes : List Eth1Data} {vote best : Eth1Data}
    (beats : beatsVote votes vote best = true) : votes.count best ≤ votes.count vote := by
  simp only [beatsVote, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
    at beats
  omega

/-- A vote that does not beat another has at most as many copies. -/
theorem count_le_of_not_beatsVote {votes : List Eth1Data} {vote best : Eth1Data}
    (beats : beatsVote votes vote best = false) : votes.count vote ≤ votes.count best := by
  simp only [beatsVote, Bool.or_eq_false_iff, decide_eq_false_iff_not] at beats
  omega

/-- The walk for the most voted vote ends on a vote of the list.

That vote has at least the copies of the vote it starts from, and of each vote it passes. -/
theorem foldl_beatsVote {votes : List Eth1Data} :
    ∀ (rest : List Eth1Data) (best : Eth1Data), best ∈ votes → (∀ vote ∈ rest, vote ∈ votes) →
      let last := rest.foldl (fun best vote => if beatsVote votes vote best then vote else best)
        best
      last ∈ votes ∧ votes.count best ≤ votes.count last ∧
        ∀ vote ∈ rest, votes.count vote ≤ votes.count last
  | [], best, member, _ => ⟨member, Nat.le_refl _, by simp⟩
  | vote :: rest, best, member, inside => by
    have voteMember := inside vote (by simp)
    -- One step keeps a vote of the list, with at least the copies of both votes it compares.
    have step : (if beatsVote votes vote best then vote else best) ∈ votes ∧
        votes.count best ≤ votes.count (if beatsVote votes vote best then vote else best) ∧
        votes.count vote ≤ votes.count (if beatsVote votes vote best then vote else best) := by
      cases beats : beatsVote votes vote best with
      | true => exact ⟨voteMember, count_le_of_beatsVote beats, Nat.le_refl _⟩
      | false => exact ⟨member, Nat.le_refl _, count_le_of_not_beatsVote beats⟩
    obtain ⟨member', bestLe, voteLe⟩ := step
    obtain ⟨lastMember, middleLe, restLe⟩ :=
      foldl_beatsVote rest _ member' fun other mem => inside other (by simp [mem])
    refine ⟨lastMember, Nat.le_trans bestLe middleLe, ?_⟩
    intro other mem
    rcases List.mem_cons.mp mem with rfl | mem
    · exact Nat.le_trans voteLe middleLe
    · exact restLe other mem

/-- The most voted vote of an empty list is the default. -/
theorem mostVoted_nil (default : Eth1Data) : mostVoted [] default = default := rfl

/-- The most voted vote of a nonempty list is in the list, and no vote has more copies there. -/
theorem mostVoted_spec {votes : List Eth1Data} (nonempty : votes ≠ []) (default : Eth1Data) :
    mostVoted votes default ∈ votes ∧
      ∀ vote ∈ votes, votes.count vote ≤ votes.count (mostVoted votes default) := by
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  obtain ⟨member, firstLe, restLe⟩ :=
    foldl_beatsVote (votes := first :: rest) rest first (by simp) fun vote mem => by simp [mem]
  refine ⟨member, ?_⟩
  intro vote mem
  rcases List.mem_cons.mp mem with rfl | mem
  · exact firstLe
  · exact restLe vote mem

/-- A vote to consider is the Eth1 data of a candidate block of the chain.

Its deposit count is at least that of the state.

Each such block gives one. -/
theorem mem_votesToConsider_iff {Block : Type} {config : Config} {state : BeaconState preset fork}
    {before : fork < .hegota} {timestamp : Block → UInt64} {getEth1Data : Block → Eth1Data}
    {periodStart : UInt64} :
    ∀ {eth1Chain : List Block} {votes : List Eth1Data},
      votesToConsider config state before timestamp getEth1Data periodStart eth1Chain =
        .ok votes →
      ∀ vote, vote ∈ votes ↔ ∃ block ∈ eth1Chain, getEth1Data block = vote ∧
        isCandidateBlock config (timestamp block) periodStart = .ok true ∧
        (state.eth1Data before).depositCount ≤ vote.depositCount
  | [], votes, made, vote => by
    simp only [votesToConsider, pure, Except.pure, Except.ok.injEq] at made
    subst made
    simp
  | block :: rest, votes, made, vote => by
    unfold votesToConsider at made
    obtain ⟨candidate, candidated, made⟩ := bind_ok_iff.mp made
    obtain ⟨others, othered, made⟩ := bind_ok_iff.mp made
    have tail := mem_votesToConsider_iff othered vote
    split at made
    · rename_i kept
      simp only [pure, Except.pure, Except.ok.injEq] at made
      subst made
      rw [List.mem_cons, tail]
      constructor
      · rintro (rfl | ⟨other, mem, rest⟩)
        · exact ⟨block, by simp, rfl, by rw [candidated, kept.1], kept.2⟩
        · exact ⟨other, by simp [mem], rest⟩
      · rintro ⟨other, mem, named, isCandidate, counted⟩
        rcases List.mem_cons.mp mem with rfl | mem
        · exact .inl named.symm
        · exact .inr ⟨other, mem, named, isCandidate, counted⟩
    · rename_i dropped
      simp only [pure, Except.pure, Except.ok.injEq] at made
      subst made
      rw [tail]
      constructor
      · rintro ⟨other, mem, rest⟩
        exact ⟨other, by simp [mem], rest⟩
      · rintro ⟨other, mem, named, isCandidate, counted⟩
        rcases List.mem_cons.mp mem with rfl | mem
        · rw [candidated, Except.ok.injEq] at isCandidate
          exact absurd ⟨isCandidate, named ▸ counted⟩ dropped
        · exact ⟨other, mem, named, isCandidate, counted⟩

/-- From Electra, once the deposits of the contract are all processed, the vote is the state's. -/
theorem getEth1Vote_of_done {Block : Type} {config : Config} {state : BeaconState preset fork}
    {before : fork < .hegota} {timestamp : Block → UInt64} {getEth1Data : Block → Eth1Data}
    {eth1Chain : List Block} (electra : .pectra ≤ fork)
    (done : state.eth1DepositIndex before = state.depositRequestsStartIndex ⟨electra, before⟩) :
    getEth1Vote config state before timestamp getEth1Data eth1Chain =
      .ok (state.eth1Data before) := by
  simp [getEth1Vote, electra, done, pure, Except.pure]

/-- Otherwise the vote is the most voted of the votes of the state that are votes to consider.

With none of them, it is the last vote to consider, or the data of the state without one. -/
theorem getEth1Vote_of_not_done {Block : Type} {config : Config}
    {state : BeaconState preset fork} {before : fork < .hegota} {timestamp : Block → UInt64}
    {getEth1Data : Block → Eth1Data} {eth1Chain : List Block}
    (notDone : ∀ electra : .pectra ≤ fork,
      state.eth1DepositIndex before ≠ state.depositRequestsStartIndex ⟨electra, before⟩) :
    getEth1Vote config state before timestamp getEth1Data eth1Chain = (do
      let periodStart ← votingPeriodStartTime config state
      let votes ← votesToConsider config state before timestamp getEth1Data periodStart eth1Chain
      return mostVoted ((state.eth1DataVotes before).data.toList.filter (· ∈ votes))
        (votes.getLast?.getD (state.eth1Data before))) := by
  unfold getEth1Vote
  by_cases electra : Fork.pectra ≤ fork
  · simp [electra, notDone electra]
  · simp [electra]

/-- The Eth1 vote is the data of the state, or the Eth1 data of a candidate block of the chain.

That data has at least the deposit count of the state. -/
theorem getEth1Vote_eq_or_candidate {Block : Type} {config : Config}
    {state : BeaconState preset fork} {before : fork < .hegota} {timestamp : Block → UInt64}
    {getEth1Data : Block → Eth1Data} {eth1Chain : List Block} {vote : Eth1Data}
    (voted : getEth1Vote config state before timestamp getEth1Data eth1Chain = .ok vote) :
    vote = state.eth1Data before ∨ ∃ periodStart,
      votingPeriodStartTime config state = .ok periodStart ∧ ∃ block ∈ eth1Chain,
        getEth1Data block = vote ∧
        isCandidateBlock config (timestamp block) periodStart = .ok true ∧
        (state.eth1Data before).depositCount ≤ vote.depositCount := by
  by_cases done : ∃ electra : .pectra ≤ fork,
      state.eth1DepositIndex before = state.depositRequestsStartIndex ⟨electra, before⟩
  · obtain ⟨electra, done⟩ := done
    rw [getEth1Vote_of_done electra done, Except.ok.injEq] at voted
    exact .inl voted.symm
  · rw [getEth1Vote_of_not_done (fun electra eq => done ⟨electra, eq⟩)] at voted
    obtain ⟨periodStart, started, voted⟩ := bind_ok_iff.mp voted
    obtain ⟨votes, considered, voted⟩ := bind_ok_iff.mp voted
    simp only [pure, Except.pure, Except.ok.injEq] at voted
    subst voted
    have mem := mem_votesToConsider_iff considered
    -- A vote of the state that counts is a vote to consider.
    have candidate : ∀ vote ∈ votes, ∃ block ∈ eth1Chain, getEth1Data block = vote ∧
        isCandidateBlock config (timestamp block) periodStart = .ok true ∧
        (state.eth1Data before).depositCount ≤ vote.depositCount := fun vote member =>
      (mem vote).mp member
    by_cases empty : (state.eth1DataVotes before).data.toList.filter (· ∈ votes) = []
    · rw [empty, mostVoted_nil]
      cases last : votes.getLast? with
      | none => exact .inl rfl
      | some final =>
        exact .inr ⟨periodStart, started, candidate final (List.mem_of_getLast? last)⟩
    · have member := (mostVoted_spec empty (votes.getLast?.getD (state.eth1Data before))).1
      exact .inr ⟨periodStart, started, candidate _ (by simpa using (List.mem_filter.mp member).2)⟩

/-- The Eth1 vote never has a smaller deposit count than the data of the state. -/
theorem depositCount_le_of_getEth1Vote {Block : Type} {config : Config}
    {state : BeaconState preset fork} {before : fork < .hegota} {timestamp : Block → UInt64}
    {getEth1Data : Block → Eth1Data} {eth1Chain : List Block} {vote : Eth1Data}
    (voted : getEth1Vote config state before timestamp getEth1Data eth1Chain = .ok vote) :
    (state.eth1Data before).depositCount ≤ vote.depositCount := by
  rcases getEth1Vote_eq_or_candidate voted with rfl | ⟨_, _, _, _, _, _, counted⟩
  · exact UInt64.le_refl _
  · exact counted

/-- When a vote of the state is a vote to consider, the Eth1 vote is one of them.

No vote to consider has more copies among the votes of the state. -/
theorem getEth1Vote_most_voted {Block : Type} {config : Config}
    {state : BeaconState preset fork} {before : fork < .hegota} {timestamp : Block → UInt64}
    {getEth1Data : Block → Eth1Data} {eth1Chain : List Block} {vote : Eth1Data}
    {periodStart : UInt64} {votes : List Eth1Data}
    (notDone : ∀ electra : .pectra ≤ fork,
      state.eth1DepositIndex before ≠ state.depositRequestsStartIndex ⟨electra, before⟩)
    (started : votingPeriodStartTime config state = .ok periodStart)
    (considered :
      votesToConsider config state before timestamp getEth1Data periodStart eth1Chain = .ok votes)
    (voted : getEth1Vote config state before timestamp getEth1Data eth1Chain = .ok vote)
    {other : Eth1Data} (otherMem : other ∈ votes)
    (otherVoted : other ∈ (state.eth1DataVotes before).data.toList) :
    vote ∈ votes ∧ vote ∈ (state.eth1DataVotes before).data.toList ∧
      let valid := (state.eth1DataVotes before).data.toList.filter (· ∈ votes)
      valid.count other ≤ valid.count vote := by
  rw [getEth1Vote_of_not_done notDone] at voted
  simp only [started, considered, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at voted
  subst voted
  have otherValid : other ∈ (state.eth1DataVotes before).data.toList.filter (· ∈ votes) :=
    List.mem_filter.mpr ⟨otherVoted, by simpa using otherMem⟩
  obtain ⟨member, most⟩ :=
    mostVoted_spec (List.ne_nil_of_mem otherValid) (votes.getLast?.getD (state.eth1Data before))
  obtain ⟨inState, inVotes⟩ := List.mem_filter.mp member
  exact ⟨by simpa using inVotes, inState, most other otherValid⟩

/-! ## Pending deposits -/

/-- In Electra, the pending deposit count is at most the most deposits per block. -/
theorem getEth1PendingDepositCount_le (state : BeaconState preset fork)
    (electra : .pectra ≤ fork ∧ fork < .fusaka) :
    getEth1PendingDepositCount state electra ≤ preset.MAX_DEPOSITS := by
  unfold getEth1PendingDepositCount
  dsimp only
  split
  · exact Std.min_le_left
  · exact UInt64.zero_le

/-- In Electra, the pending deposit count is the number of deposits that the block must hold. -/
theorem expectedDepositCount_eq_getEth1PendingDepositCount (state : BeaconState preset fork)
    (electra : .pectra ≤ fork ∧ fork < .fusaka) :
    expectedDepositCount state (Nat.lt_trans electra.2 (by decide)) =
      .ok (getEth1PendingDepositCount state electra).toNat := by
  have notFulu : ¬Fork.fusaka ≤ fork := fun fulu =>
    Nat.lt_irrefl _ (Nat.lt_of_lt_of_le electra.2 fulu)
  unfold expectedDepositCount getEth1PendingDepositCount
  simp only [notFulu, electra.1, ite_false, dite_true]
  split <;> rfl

/-! ## The state root -/

/-- The new state root is the root of the state after the block with an empty signature.

The transition runs without the checks of the result. -/
theorem computeNewStateRoot_eq_ok_iff {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {state : BeaconState preset fork}
    {block : BeaconBlock preset fork} {root : Root} :
    computeNewStateRoot config checks engine state block = .ok root ↔
      ∃ post, stateTransition config checks engine state ⟨block, Vector.replicate 96 0⟩ false =
        .ok post ∧ SszType.hashTreeRoot post = .ok root := by
  unfold computeNewStateRoot
  simp only [bind_ok_iff, mapError_ok_iff]

/-- The block processing never reads the state root of the block. -/
theorem processBlock_stateRoot (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) (root : Root) :
    processBlock config checks engine state { block with stateRoot := root } =
      processBlock config checks engine state block := by
  cases block
  rfl

/-- A block that carries the new state root passes the full state transition, checks included.

Its signature must pass the check of the block signature, on the state at the slot of the block.

The state after it is the state whose root the block carries. -/
theorem stateTransition_of_computeNewStateRoot {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {state : BeaconState preset fork}
    {block : BeaconBlock preset fork} {root : Root}
    (computed : computeNewStateRoot config checks engine state block = .ok root)
    {signature : BLSSignature}
    (signed : ∀ slotted, processSlots config checks state block.slot = .ok slotted →
      verifyBlockSignature config checks slotted
        ⟨{ block with stateRoot := root }, signature⟩ = .ok true) :
    ∃ post, stateTransition config checks engine state
        ⟨{ block with stateRoot := root }, signature⟩ = .ok post ∧
      SszType.hashTreeRoot post = .ok root := by
  obtain ⟨post, transitioned, rooted⟩ := computeNewStateRoot_eq_ok_iff.mp computed
  refine ⟨post, ?_, rooted⟩
  unfold stateTransition at transitioned ⊢
  obtain ⟨slotted, slotsOk, applied⟩ := bind_ok_iff.mp transitioned
  -- Without the checks of the result, the block only runs.
  have processed : processBlock config checks engine slotted block = .ok post := by
    simp only [applySignedBlock, checkBlockSignature, checkStateRoot, bind, Except.bind, pure,
      Except.pure] at applied
    cases ran : processBlock config checks engine slotted block <;> simp_all
  simp only [slotsOk, bind, Except.bind]
  simp only [applySignedBlock, checkBlockSignature, checkStateRoot, signed slotted slotsOk, ensure,
    ite_true, processBlock_stateRoot, processed, bind, Except.bind, liftSsz, rooted,
    Except.mapError, pure, Except.pure]

/-! ## The signed block header -/

/-- The signed header of a block carries the root of its body and the signature of the block.

Its other fields are those of the block. -/
theorem signedHeader_eq_ok_iff {signed : SignedBeaconBlock preset fork}
    {header : SignedBeaconBlockHeader} :
    signed.signedHeader = .ok header ↔
      SszType.hashTreeRoot signed.message.body = .ok header.message.bodyRoot ∧
        header = ⟨⟨signed.message.slot, signed.message.proposerIndex, signed.message.parentRoot,
          signed.message.stateRoot, header.message.bodyRoot⟩, signed.signature⟩ := by
  unfold SignedBeaconBlock.signedHeader
  cases rooted : SszType.hashTreeRoot signed.message.body with
  | error e => simp [bind, Except.bind]
  | ok bodyRoot =>
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq]
    constructor
    · rintro rfl
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, eq⟩
      exact eq.symm

/-! ## The on-chain aggregate -/

/-- The committee of a network aggregate is the first committee whose bit it sets. -/
theorem committeeOfAggregate_eq_ok_iff {electra : .pectra ≤ fork}
    {aggregate : Attestation preset fork} {keyed : CommitteeIndex × Attestation preset fork} :
    committeeOfAggregate electra aggregate = .ok keyed ↔
      (getCommitteeIndices (aggregate.committeeBits electra)).head? = some keyed.1 ∧
        keyed.2 = aggregate := by
  unfold committeeOfAggregate
  split
  · rename_i index named
    rw [named]
    constructor
    · rintro ⟨⟩
      exact ⟨rfl, rfl⟩
    · rintro ⟨first, second⟩
      cases keyed
      simp_all
  · rename_i none_
    simp [none_]

/-- The order of the aggregates by their committee is transitive. -/
theorem committee_le_trans (a b c : CommitteeIndex × Attestation preset fork)
    (ab : decide (a.1 ≤ b.1) = true) (bc : decide (b.1 ≤ c.1) = true) : decide (a.1 ≤ c.1) = true :=
  decide_eq_true (UInt64.le_trans (of_decide_eq_true ab) (of_decide_eq_true bc))

/-- Any two aggregates compare by their committee, one way or the other. -/
theorem committee_le_total (a b : CommitteeIndex × Attestation preset fork) :
    (decide (a.1 ≤ b.1) || decide (b.1 ≤ a.1)) = true := by
  rcases UInt64.le_total a.1 b.1 with le | le <;> simp [le]

/-- The on-chain aggregate joins the network aggregates in the order of their committees.

There is an order of the aggregates, each with its first committee, sorted by that committee.

The aggregation bits are those of each aggregate in that order.

The signature is the aggregate of their signatures in that order, and the data is the first one's.
-/
theorem computeOnChainAggregate_spec {electra : .pectra ≤ fork}
    {networkAggregates : List (Attestation preset fork)} {attestation : Attestation preset fork}
    (joined : computeOnChainAggregate electra networkAggregates = .ok attestation) :
    ∃ ordered : List (CommitteeIndex × Attestation preset fork),
      (ordered.map (·.2)).Perm networkAggregates ∧
      ordered.Pairwise (fun a b => a.1 ≤ b.1) ∧
      (∀ keyed ∈ ordered,
        (getCommitteeIndices (keyed.2.committeeBits electra)).head? = some keyed.1) ∧
      attestation.aggregationBits.bits =
        (ordered.map (·.2.aggregationBits.bits)).foldl (· ++ ·) #[] ∧
      Signatures.aggregate (ordered.map fun entry => Base.packBytes entry.2.signature).toArray =
        .ok attestation.signature ∧
      ∃ first, ordered.head? = some first ∧ attestation.data = first.2.data := by
  unfold computeOnChainAggregate at joined
  obtain ⟨keyed, keyedOk, joined⟩ := bind_ok_iff.mp joined
  have seconds : keyed.map (·.2) = networkAggregates := by
    have := map_of_mapM_ok (p := (·.2)) (q := id)
      (fun x y step => (committeeOfAggregate_eq_ok_iff.mp step).2) keyedOk
    simpa using this
  have perm := List.mergeSort_perm keyed fun a b => decide (a.1 ≤ b.1)
  refine ⟨keyed.mergeSort fun a b => decide (a.1 ≤ b.1), ?_, ?_, ?_, ?_⟩
  · rw [← seconds]
    exact perm.map _
  · exact (List.pairwise_mergeSort committee_le_trans committee_le_total keyed).imp
      of_decide_eq_true
  · intro entry member
    obtain ⟨aggregate, -, step⟩ := mapM_ok_mem keyedOk entry (perm.mem_iff.mp member)
    have ⟨named, same⟩ := committeeOfAggregate_eq_ok_iff.mp step
    rw [same]
    exact named
  · dsimp only at joined
    split at joined
    · rename_i first headed
      split at joined
      · obtain ⟨signature, signed, joined⟩ := bind_ok_iff.mp joined
        simp only [pure, Except.pure, Except.ok.injEq] at joined
        subst joined
        exact ⟨rfl, mapError_ok_iff.mp signed, first, headed, rfl⟩
      · simp [throw, throwThe, MonadExceptOf.throw] at joined
    · simp [throw, throwThe, MonadExceptOf.throw] at joined

/-- The committee bits of the on-chain aggregate mark the committees of the network aggregates.

A bit is set exactly when it is the first committee bit set by some network aggregate. -/
theorem committeeBits_computeOnChainAggregate {electra : .pectra ≤ fork}
    {networkAggregates : List (Attestation preset fork)} {attestation : Attestation preset fork}
    (joined : computeOnChainAggregate electra networkAggregates = .ok attestation)
    (index : Fin preset.MAX_COMMITTEES_PER_SLOT.toNat) :
    (attestation.committeeBits electra).bits[index] = true ↔
      ∃ aggregate ∈ networkAggregates,
        (getCommitteeIndices (aggregate.committeeBits electra)).head? =
          some index.val.toUInt64 := by
  unfold computeOnChainAggregate at joined
  obtain ⟨keyed, keyedOk, joined⟩ := bind_ok_iff.mp joined
  have perm := List.mergeSort_perm keyed fun a b => decide (a.1 ≤ b.1)
  dsimp only at joined
  split at joined
  · split at joined
    · obtain ⟨signature, -, joined⟩ := bind_ok_iff.mp joined
      simp only [pure, Except.pure, Except.ok.injEq] at joined
      subst joined
      simp only [Fin.getElem_fin, Vector.getElem_ofFn, List.contains_iff_mem, List.mem_map]
      constructor
      · rintro ⟨entry, member, named⟩
        obtain ⟨aggregate, member', step⟩ := mapM_ok_mem keyedOk entry (perm.mem_iff.mp member)
        have ⟨first, same⟩ := committeeOfAggregate_eq_ok_iff.mp step
        exact ⟨aggregate, member', named ▸ first⟩
      · rintro ⟨aggregate, member, named⟩
        obtain ⟨entry, member', step⟩ := exists_mem_of_mapM_ok keyedOk member
        obtain ⟨first, -⟩ := committeeOfAggregate_eq_ok_iff.mp step
        exact ⟨entry, perm.mem_iff.mpr member', Option.some.inj (first.symm.trans named)⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at joined
  · simp [throw, throwThe, MonadExceptOf.throw] at joined

end EthLib.Consensus
