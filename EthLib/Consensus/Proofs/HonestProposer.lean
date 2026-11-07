module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.DataAvailability.Blob
public import EthLib.Consensus.HonestProposer
public import EthLib.Consensus.Proofs.Containers.Requests

/-!
# Proofs: what an honest proposer computes

Before Heze, the Eth1 vote of a proposer is the data of the state or the data of a candidate block.

So it never moves the deposit count of the state back.

When the votes of the state hold a candidate, the vote is one of them with the most copies there.

In Electra, the pending deposit count is the number of deposits that block processing expects.

With a signature that passes its check, a block that carries the new state root is valid.

The state after it then has that root.

The on-chain aggregate joins the network aggregates in the order of their committees.

Reading the requests of the execution layer inverts the list that the execution layer receives.

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

/-! ## Execution requests -/

/-- The first byte of a type byte followed by data is the type byte. -/
theorem getElem?_zero_cons_append (type : UInt8) (data : ByteArray) :
    (ByteArray.mk #[type] ++ data).data[0]? = some type := by
  rw [ByteArray.data_append, Array.getElem?_append_left (Nat.succ_pos 0)]
  rfl

/-- The bytes after the type byte are the data. -/
theorem extract_one_cons_append (type : UInt8) (data : ByteArray) :
    (ByteArray.mk #[type] ++ data).extract 1 (ByteArray.mk #[type] ++ data).size = data := by
  exact ByteArray.extract_append_eq_right (by rfl) ByteArray.size_append

/-- Bytes with a first byte are that byte followed by the rest. -/
theorem cons_append_extract_one {request : ByteArray} {type : UInt8}
    (first : request.data[0]? = some type) :
    ByteArray.mk #[type] ++ request.extract 1 request.size = request := by
  cases request with
  | mk bytes =>
    have positive : 0 < bytes.size := by
      cases bytes with
      | mk list => cases list with
        | nil => simp at first
        | cons _ _ => exact Nat.succ_pos _
    apply ByteArray.ext
    rw [ByteArray.data_append, ByteArray.data_extract]
    have whole := firstByte_append_tail bytes positive
    have named : bytes[0]?.getD 0 = type := by
      change bytes[0]? = some type at first
      rw [first]
      rfl
    rw [named] at whole
    exact whole

/-- Two lists of bytes, each strictly increasing, with the same members are equal. -/
theorem eq_of_pairwise_lt_of_mem_iff :
    ∀ {l₁ l₂ : List UInt8}, l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) →
      (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, same => absurd ((same b).mpr (by simp)) (by simp)
  | a :: _, [], _, _, same => absurd ((same a).mp (by simp)) (by simp)
  | a :: as, b :: bs, sorted₁, sorted₂, same => by
    rw [List.pairwise_cons] at sorted₁ sorted₂
    have heads : a = b := by
      rcases List.mem_cons.mp ((same a).mp (by simp)) with eq | mem
      · exact eq
      · rcases List.mem_cons.mp ((same b).mpr (by simp)) with eq | mem'
        · exact eq.symm
        · exact absurd (UInt8.lt_trans (sorted₂.1 a mem) (sorted₁.1 b mem')) (UInt8.lt_irrefl _)
    subst heads
    congr 1
    refine eq_of_pairwise_lt_of_mem_iff sorted₁.2 sorted₂.2 fun x => ?_
    constructor
    · intro mem
      rcases List.mem_cons.mp ((same x).mp (by simp [mem])) with rfl | mem'
      · exact absurd (sorted₁.1 _ mem) (UInt8.lt_irrefl _)
      · exact mem'
    · intro mem
      rcases List.mem_cons.mp ((same x).mpr (by simp [mem])) with rfl | mem'
      · exact absurd (sorted₂.1 _ mem) (UInt8.lt_irrefl _)
      · exact mem'

/-- The request types strictly increase. -/
theorem requestTypes_pairwise (fork : Fork) : (requestTypes fork).Pairwise (· < ·) := by
  unfold requestTypes
  split <;> decide

/-- The count and the SSZ bytes of the list of one type; a type of no list has an empty slot. -/
def requestSlot (requests : ExecutionRequests preset fork) (type : UInt8) :
    Nat × Except Err ByteArray :=
  if type = DEPOSIT_REQUEST_TYPE[0] then
    (requests.deposits.data.size, SszType.serialize requests.deposits)
  else if type = WITHDRAWAL_REQUEST_TYPE[0] then
    (requests.withdrawals.data.size, SszType.serialize requests.withdrawals)
  else if type = CONSOLIDATION_REQUEST_TYPE[0] then
    (requests.consolidations.data.size, SszType.serialize requests.consolidations)
  else if gloas : .glamsterdam ≤ fork then
    if type = BUILDER_DEPOSIT_REQUEST_TYPE[0] then
      ((requests.builderDeposits gloas).data.size,
        SszType.serialize (requests.builderDeposits gloas))
    else if type = BUILDER_EXIT_REQUEST_TYPE[0] then
      ((requests.builderExits gloas).data.size, SszType.serialize (requests.builderExits gloas))
    else (0, .ok .empty)
  else (0, .ok .empty)

/-- The lists of the requests, by type: the list of each request type in turn. -/
theorem typedLists_eq_map (requests : ExecutionRequests preset fork) :
    requests.typedLists = (requestTypes fork).map fun type =>
      ⟨#v[type], (requestSlot requests type).1, (requestSlot requests type).2⟩ := by
  unfold ExecutionRequests.typedLists requestTypes
  by_cases gloas : Fork.glamsterdam ≤ fork <;>
    simp [gloas, requestSlot, DEPOSIT_REQUEST_TYPE, WITHDRAWAL_REQUEST_TYPE,
      CONSOLIDATION_REQUEST_TYPE, BUILDER_DEPOSIT_REQUEST_TYPE, BUILDER_EXIT_REQUEST_TYPE]

/-- The list that the execution layer receives, by type. -/
theorem getExecutionRequestsList_eq (requests : ExecutionRequests preset fork) :
    getExecutionRequestsList requests =
      ((requestTypes fork).filter fun type => (requestSlot requests type).1 != 0).mapM
        fun type => do return ⟨#[type]⟩ ++ (← (requestSlot requests type).2) := by
  unfold getExecutionRequestsList
  rw [typedLists_eq_map, List.filter_map, List.mapM_map]
  rfl

/-- The empty requests have an empty list of each type. -/
theorem requestSlot_empty (type : UInt8) :
    requestSlot (ExecutionRequests.empty preset fork) type = (0, .ok .empty) := by
  unfold requestSlot
  have forkList : ∀ {α : Type} [SszType α] [LawfulSszType α] {limit : Nat},
      SszType.serialize (⟨#[], fun _ => Nat.zero_le _⟩ : ForkList .glamsterdam fork α limit) =
        .ok .empty := fun {_ _ _ _} => SszType.serialize_deserialize deserialize_forkList_empty
  have progressive : ∀ {α : Type} [SszType α] [LawfulSszType α],
      SszType.serialize (⟨#[]⟩ : ProgressiveList α) = .ok .empty :=
    fun {_ _ _} => SszType.serialize_deserialize deserialize_progressiveList_empty
  split_ifs <;> simp [ExecutionRequests.empty, forkList, progressive]

/-- Setting the list of one type changes only the slot of that type.

That slot then holds the bytes, with a count of zero exactly when the bytes are empty. -/
theorem setRequestList_slot {requests updated : ExecutionRequests preset fork} {type : UInt8}
    {data : ByteArray} (set : setRequestList requests type data = .ok updated) :
    (∀ other, other ≠ type → requestSlot updated other = requestSlot requests other) ∧
      (type ∈ requestTypes fork →
        ∃ count, (count = 0 ↔ data.size = 0) ∧ requestSlot updated type = (count, .ok data)) := by
  unfold setRequestList at set
  split_ifs at set with deposit withdrawal consolidation gloas builderDeposit builderExit
  · obtain ⟨list, read, made⟩ := bind_ok_iff.mp set
    simp only [pure, Except.pure, Except.ok.injEq] at made
    subst made
    have wrote := SszType.serialize_deserialize (mapError_ok_iff.mp read)
    refine ⟨fun other ne => ?_, fun _ => ⟨_, forkList_size_eq_zero_iff wrote, ?_⟩⟩
    · unfold requestSlot
      split_ifs <;> first | rfl | (exfalso; simp_all)
    · simp [requestSlot, DEPOSIT_REQUEST_TYPE,  deposit, wrote]
  · obtain ⟨list, read, made⟩ := bind_ok_iff.mp set
    simp only [pure, Except.pure, Except.ok.injEq] at made
    subst made
    have wrote := SszType.serialize_deserialize (mapError_ok_iff.mp read)
    refine ⟨fun other ne => ?_, fun _ => ⟨_, forkList_size_eq_zero_iff wrote, ?_⟩⟩
    · unfold requestSlot
      split_ifs <;> first | rfl | (exfalso; simp_all)
    · simp [requestSlot, DEPOSIT_REQUEST_TYPE, WITHDRAWAL_REQUEST_TYPE,  withdrawal, wrote]
  · obtain ⟨list, read, made⟩ := bind_ok_iff.mp set
    simp only [pure, Except.pure, Except.ok.injEq] at made
    subst made
    have wrote := SszType.serialize_deserialize (mapError_ok_iff.mp read)
    refine ⟨fun other ne => ?_, fun _ => ⟨_, forkList_size_eq_zero_iff wrote, ?_⟩⟩
    · unfold requestSlot
      split_ifs <;> first | rfl | (exfalso; simp_all)
    · simp [requestSlot, DEPOSIT_REQUEST_TYPE, WITHDRAWAL_REQUEST_TYPE, CONSOLIDATION_REQUEST_TYPE,
        consolidation, wrote]
  · obtain ⟨list, read, made⟩ := bind_ok_iff.mp set
    simp only [pure, Except.pure, Except.ok.injEq] at made
    subst made
    have wrote := SszType.serialize_deserialize (mapError_ok_iff.mp read)
    refine ⟨fun other ne => ?_, fun _ => ⟨_, progressiveList_size_eq_zero_iff wrote, ?_⟩⟩
    · unfold requestSlot
      split_ifs <;> first | rfl | (exfalso; simp_all)
    · simp [requestSlot, DEPOSIT_REQUEST_TYPE, WITHDRAWAL_REQUEST_TYPE, CONSOLIDATION_REQUEST_TYPE,
        BUILDER_DEPOSIT_REQUEST_TYPE, builderDeposit, gloas, wrote]
  · obtain ⟨list, read, made⟩ := bind_ok_iff.mp set
    simp only [pure, Except.pure, Except.ok.injEq] at made
    subst made
    have wrote := SszType.serialize_deserialize (mapError_ok_iff.mp read)
    refine ⟨fun other ne => ?_, fun _ => ⟨_, progressiveList_size_eq_zero_iff wrote, ?_⟩⟩
    · unfold requestSlot
      split_ifs <;> first | rfl | (exfalso; simp_all)
    · simp [requestSlot, DEPOSIT_REQUEST_TYPE, WITHDRAWAL_REQUEST_TYPE, CONSOLIDATION_REQUEST_TYPE,
        BUILDER_DEPOSIT_REQUEST_TYPE, BUILDER_EXIT_REQUEST_TYPE, builderExit, gloas, wrote]
  · simp only [pure, Except.pure, Except.ok.injEq] at set
    subst set
    refine ⟨fun _ _ => rfl, fun member => ?_⟩
    simp_all [requestTypes, DEPOSIT_REQUEST_TYPE, WITHDRAWAL_REQUEST_TYPE,
      CONSOLIDATION_REQUEST_TYPE, BUILDER_DEPOSIT_REQUEST_TYPE, BUILDER_EXIT_REQUEST_TYPE]
  · simp only [pure, Except.pure, Except.ok.injEq] at set
    subst set
    refine ⟨fun _ _ => rfl, fun member => ?_⟩
    simp_all [requestTypes, DEPOSIT_REQUEST_TYPE, WITHDRAWAL_REQUEST_TYPE,
      CONSOLIDATION_REQUEST_TYPE]

/-- One step of reading the requests succeeds exactly when its checks pass and its list decodes.

The entry needs a request type after the type before it, and data after its type byte. -/
theorem getExecutionRequestsFrom_cons_eq_ok_iff {previous : Option UInt8}
    {requests result : ExecutionRequests preset fork} {request : ByteArray}
    {rest : List ByteArray} :
    getExecutionRequestsFrom previous requests (request :: rest) = .ok result ↔
      ∃ type updated, request.data[0]? = some type ∧ type ∈ requestTypes fork ∧
        (request.extract 1 request.size).size ≠ 0 ∧ (∀ p, previous = some p → p < type) ∧
        setRequestList requests type (request.extract 1 request.size) = .ok updated ∧
        getExecutionRequestsFrom (some type) updated rest = .ok result := by
  rw [getExecutionRequestsFrom]
  generalize request.extract 1 request.size = data
  cases first : request.data[0]? with
  | none => simp [throw, throwThe, MonadExceptOf.throw]
  | some type =>
    by_cases member : type ∈ requestTypes fork
    · by_cases empty : data.size = 0
      · simp [member, empty, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
      · cases previous with
        | none => simp [member, empty, bind_ok_iff]
        | some p =>
          by_cases lt : p < type
          · simp [member, empty, lt, bind_ok_iff]
          · simp [member, empty, lt, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
    · simp [member, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- What reading the requests gives, when it succeeds.

The types of the entries strictly increase, and each entry has a request type and data.

The slot of each entry's type holds its data, with a nonzero count.

The slot of every other type is unchanged. -/
theorem getExecutionRequestsFrom_spec :
    ∀ {list : List ByteArray} {previous : Option UInt8}
      {requests result : ExecutionRequests preset fork},
      getExecutionRequestsFrom previous requests list = .ok result →
      (list.map (·.data[0]?.getD 0)).Pairwise (· < ·) ∧
      (∀ request ∈ list, ∃ type, request.data[0]? = some type ∧ type ∈ requestTypes fork ∧
        (∀ p, previous = some p → p < type) ∧ (request.extract 1 request.size).size ≠ 0 ∧
        ∃ count, count ≠ 0 ∧
          requestSlot result type = (count, .ok (request.extract 1 request.size))) ∧
      (∀ type, type ∉ list.map (·.data[0]?.getD 0) →
        requestSlot result type = requestSlot requests type)
  | [], _, _, _, read => by
    simp only [getExecutionRequestsFrom, pure, Except.pure, Except.ok.injEq] at read
    subst read
    simp
  | request :: rest, previous, requests, result, read => by
    obtain ⟨type, updated, first, member, nonempty, after, set, others⟩ :=
      getExecutionRequestsFrom_cons_eq_ok_iff.mp read
    obtain ⟨sorted, each, untouched⟩ := getExecutionRequestsFrom_spec others
    obtain ⟨kept, placed⟩ := setRequestList_slot set
    have head : request.data[0]?.getD 0 = type := by rw [first]; rfl
    -- Every later type comes after this one.
    have later : ∀ other ∈ rest.map (·.data[0]?.getD 0), type < other := by
      intro other mem
      obtain ⟨request', mem', rfl⟩ := List.mem_map.mp mem
      obtain ⟨type', first', -, after', -⟩ := each request' mem'
      rw [first']
      exact after' type rfl
    have notLater : type ∉ rest.map (·.data[0]?.getD 0) := fun mem =>
      UInt8.lt_irrefl _ (later type mem)
    refine ⟨?_, ?_, ?_⟩
    · rw [List.map_cons, head, List.pairwise_cons]
      exact ⟨later, sorted⟩
    · intro request' mem
      rcases List.mem_cons.mp mem with rfl | mem
      · obtain ⟨count, sized, slot⟩ := placed member
        refine ⟨type, first, member, after, nonempty, count, fun zero => nonempty (sized.mp zero),
          ?_⟩
        rw [untouched type notLater, slot]
      · obtain ⟨type', first', member', after', nonempty', slot'⟩ := each request' mem
        refine ⟨type', first', member', fun p named => ?_, nonempty', slot'⟩
        have : type' ∈ rest.map (·.data[0]?.getD 0) :=
          List.mem_map.mpr ⟨request', mem, by rw [first']; rfl⟩
        exact UInt8.lt_trans (after p named) (later type' this)
    · intro other notMem
      rw [List.map_cons, head, List.mem_cons, not_or] at notMem
      rw [untouched other notMem.2, kept other notMem.1]

/-- The members of the request types: three, and from Gloas five. -/
theorem mem_requestTypes {type : UInt8} :
    type ∈ requestTypes fork ↔ type = 0 ∨ type = 1 ∨ type = 2 ∨
      (.glamsterdam ≤ fork ∧ (type = 3 ∨ type = 4)) := by
  unfold requestTypes
  by_cases gloas : Fork.glamsterdam ≤ fork <;>
    simp [gloas, DEPOSIT_REQUEST_TYPE, WITHDRAWAL_REQUEST_TYPE, CONSOLIDATION_REQUEST_TYPE,
      BUILDER_DEPOSIT_REQUEST_TYPE, BUILDER_EXIT_REQUEST_TYPE]

/-- The bytes of a slot of a request type decode, so they can set the list of that type. -/
theorem setRequestList_of_requestSlot {requests start : ExecutionRequests preset fork}
    {type : UInt8} {data : ByteArray} (member : type ∈ requestTypes fork)
    (bytes : (requestSlot requests type).2 = .ok data) :
    ∃ updated, setRequestList start type data = .ok updated := by
  rcases mem_requestTypes.mp member with rfl | rfl | rfl | ⟨gloas, rfl | rfl⟩ <;>
    simp [requestSlot, DEPOSIT_REQUEST_TYPE, WITHDRAWAL_REQUEST_TYPE, CONSOLIDATION_REQUEST_TYPE,
      BUILDER_DEPOSIT_REQUEST_TYPE, BUILDER_EXIT_REQUEST_TYPE, *] at bytes <;>
    simp [setRequestList, DEPOSIT_REQUEST_TYPE, WITHDRAWAL_REQUEST_TYPE,
      CONSOLIDATION_REQUEST_TYPE, BUILDER_DEPOSIT_REQUEST_TYPE, BUILDER_EXIT_REQUEST_TYPE,
      SszType.deserialize_serialize bytes, bind, Except.bind, Except.mapError, pure, Except.pure, *]

/-- A slot of a request type with no request has empty bytes. -/
theorem requestSlot_bytes_of_count_eq_zero {requests : ExecutionRequests preset fork}
    {type : UInt8} (member : type ∈ requestTypes fork) (zero : (requestSlot requests type).1 = 0) :
    (requestSlot requests type).2 = .ok .empty := by
  rcases mem_requestTypes.mp member with rfl | rfl | rfl | ⟨gloas, rfl | rfl⟩ <;>
    simp [requestSlot, DEPOSIT_REQUEST_TYPE, WITHDRAWAL_REQUEST_TYPE, CONSOLIDATION_REQUEST_TYPE,
      BUILDER_DEPOSIT_REQUEST_TYPE, BUILDER_EXIT_REQUEST_TYPE, *] at zero ⊢
  · generalize requests.deposits = list at zero ⊢
    obtain ⟨data, bound⟩ := list
    obtain rfl : data = #[] := zero
    exact serialize_forkList_empty
  · generalize requests.withdrawals = list at zero ⊢
    obtain ⟨data, bound⟩ := list
    obtain rfl : data = #[] := zero
    exact serialize_forkList_empty
  · generalize requests.consolidations = list at zero ⊢
    obtain ⟨data, bound⟩ := list
    obtain rfl : data = #[] := zero
    exact serialize_forkList_empty
  · generalize requests.builderDeposits gloas = list at zero ⊢
    obtain ⟨data⟩ := list
    obtain rfl : data = #[] := zero
    exact serialize_progressiveList_empty
  · generalize requests.builderExits gloas = list at zero ⊢
    obtain ⟨data⟩ := list
    obtain rfl : data = #[] := zero
    exact serialize_progressiveList_empty

/-- Two requests whose slots of every request type hold the same bytes are equal. -/
theorem eq_of_requestSlot {requests other : ExecutionRequests preset fork}
    (same : ∀ type ∈ requestTypes fork, ∃ data, (requestSlot requests type).2 = .ok data ∧
      (requestSlot other type).2 = .ok data) : requests = other := by
  obtain ⟨d0, l0, r0⟩ := same 0 (mem_requestTypes.mpr (.inl rfl))
  obtain ⟨d1, l1, r1⟩ := same 1 (mem_requestTypes.mpr (.inr (.inl rfl)))
  obtain ⟨d2, l2, r2⟩ := same 2 (mem_requestTypes.mpr (.inr (.inr (.inl rfl))))
  simp [requestSlot, DEPOSIT_REQUEST_TYPE, WITHDRAWAL_REQUEST_TYPE,
    CONSOLIDATION_REQUEST_TYPE] at l0 r0 l1 r1 l2 r2
  have deposits := SszType.serialize_injective l0 r0
  have withdrawals := SszType.serialize_injective l1 r1
  have consolidations := SszType.serialize_injective l2 r2
  have builders : ∀ gloas : .glamsterdam ≤ fork,
      requests.builderDeposits gloas = other.builderDeposits gloas ∧
        requests.builderExits gloas = other.builderExits gloas := by
    intro gloas
    obtain ⟨d3, l3, r3⟩ := same 3 (mem_requestTypes.mpr (.inr (.inr (.inr ⟨gloas, .inl rfl⟩))))
    obtain ⟨d4, l4, r4⟩ := same 4 (mem_requestTypes.mpr (.inr (.inr (.inr ⟨gloas, .inr rfl⟩))))
    simp [requestSlot, DEPOSIT_REQUEST_TYPE, WITHDRAWAL_REQUEST_TYPE, CONSOLIDATION_REQUEST_TYPE,
      BUILDER_DEPOSIT_REQUEST_TYPE, BUILDER_EXIT_REQUEST_TYPE, gloas] at l3 r3 l4 r4
    exact ⟨SszType.serialize_injective l3 r3, SszType.serialize_injective l4 r4⟩
  cases requests
  cases other
  simp only at deposits withdrawals consolidations builders
  subst deposits withdrawals consolidations
  congr 1
  · funext gloas
    exact (builders gloas).1
  · funext gloas
    exact (builders gloas).2

/-- Each member of the left list of a pairing has a partner in the right list. -/
theorem exists_mem_of_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → ∀ {x}, x ∈ xs → ∃ y ∈ ys, R x y
  | _, _, .nil, _, mem => by simp at mem
  | _, _, .cons head tail, _, mem => by
    rcases List.mem_cons.mp mem with rfl | mem
    · exact ⟨_, List.mem_cons_self, head⟩
    · obtain ⟨y, mem', related⟩ := exists_mem_of_forall₂ tail mem
      exact ⟨y, List.mem_cons_of_mem _ mem', related⟩

/-- A pairing that names each left member by its partner maps the right list onto the left. -/
theorem map_eq_of_forall₂ {α β : Type} {f : β → α} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ (fun x y => f y = x) xs ys → ys.map f = xs
  | _, _, .nil => rfl
  | _, _, .cons head tail => by rw [List.map_cons, head, map_eq_of_forall₂ tail]

/-- A slot of a request type has no request exactly when its bytes are empty. -/
theorem requestSlot_count_eq_zero_iff {requests : ExecutionRequests preset fork} {type : UInt8}
    {data : ByteArray} (member : type ∈ requestTypes fork)
    (bytes : (requestSlot requests type).2 = .ok data) :
    (requestSlot requests type).1 = 0 ↔ data.size = 0 := by
  rcases mem_requestTypes.mp member with rfl | rfl | rfl | ⟨gloas, rfl | rfl⟩ <;>
    simp [requestSlot, DEPOSIT_REQUEST_TYPE, WITHDRAWAL_REQUEST_TYPE, CONSOLIDATION_REQUEST_TYPE,
      BUILDER_DEPOSIT_REQUEST_TYPE, BUILDER_EXIT_REQUEST_TYPE, *] at bytes ⊢
  · simpa using forkList_size_eq_zero_iff bytes
  · simpa using forkList_size_eq_zero_iff bytes
  · simpa using forkList_size_eq_zero_iff bytes
  · simpa using progressiveList_size_eq_zero_iff bytes
  · simpa using progressiveList_size_eq_zero_iff bytes

/-- The bytes of the slots of some request types, in increasing order, read back. -/
theorem getExecutionRequestsFrom_exists {requests : ExecutionRequests preset fork} :
    ∀ {types : List UInt8} {list : List ByteArray} {previous : Option UInt8}
      {start : ExecutionRequests preset fork},
      List.Forall₂ (fun type request => ∃ data, (requestSlot requests type).2 = .ok data ∧
        data.size ≠ 0 ∧ request = ⟨#[type]⟩ ++ data) types list →
      types.Pairwise (· < ·) →
      (∀ type ∈ types, type ∈ requestTypes fork ∧ ∀ p, previous = some p → p < type) →
      ∃ result, getExecutionRequestsFrom previous start list = .ok result
  | [], [], _, start, .nil, _, _ => ⟨start, rfl⟩
  | type :: types, request :: list, previous, start, .cons head tail, sorted, known => by
    obtain ⟨data, bytes, nonempty, rfl⟩ := head
    obtain ⟨member, after⟩ := known type (by simp)
    obtain ⟨updated, set⟩ := setRequestList_of_requestSlot (start := start) member bytes
    rw [List.pairwise_cons] at sorted
    obtain ⟨result, read⟩ := getExecutionRequestsFrom_exists (previous := some type)
      (start := updated) tail sorted.2 fun other mem =>
        ⟨(known other (by simp [mem])).1, fun p named => by
          cases named
          exact sorted.1 other mem⟩
    refine ⟨result, getExecutionRequestsFrom_cons_eq_ok_iff.mpr
      ⟨type, updated, getElem?_zero_cons_append type data, member, ?_, after, ?_, read⟩⟩
    · rw [extract_one_cons_append]
      exact nonempty
    · rw [extract_one_cons_append]
      exact set

/-- The requests read from a list are exactly the requests that give that list.

So reading inverts the list that the execution layer receives, and each list has one reading. -/
theorem getExecutionRequests_eq_ok_iff {list : List ByteArray}
    {requests : ExecutionRequests preset fork} :
    getExecutionRequests list = .ok requests ↔ getExecutionRequestsList requests = .ok list := by
  constructor
  · intro read
    obtain ⟨sorted, each, untouched⟩ := getExecutionRequestsFrom_spec read
    -- A request type without an entry keeps the empty list.
    have empty : ∀ type, type ∉ list.map (·.data[0]?.getD 0) →
        requestSlot requests type = (0, .ok .empty) := fun type notMem => by
      rw [untouched type notMem, requestSlot_empty]
    -- The types with a request are the types of the entries, in the same order.
    have types : (requestTypes fork).filter (fun type => (requestSlot requests type).1 != 0) =
        list.map (·.data[0]?.getD 0) := by
      refine eq_of_pairwise_lt_of_mem_iff
        ((requestTypes_pairwise fork).sublist List.filter_sublist) sorted fun type => ?_
      rw [List.mem_filter]
      constructor
      · rintro ⟨-, nonzero⟩
        by_contra notMem
        simp [empty type notMem] at nonzero
      · intro mem
        obtain ⟨request, mem', rfl⟩ := List.mem_map.mp mem
        obtain ⟨type, first, member, -, -, count, nonzero, slot⟩ := each request mem'
        rw [first]
        simp [member, slot, nonzero]
    rw [getExecutionRequestsList_eq, types, List.mapM_map]
    refine (mapM_eq_ok_map (g := id) fun request mem => ?_).trans (by rw [List.map_id])
    obtain ⟨type, first, -, -, -, count, -, slot⟩ := each request mem
    simp only [Function.comp, first, Option.getD_some, slot, bind, Except.bind, pure, Except.pure,
      id]
    rw [cons_append_extract_one first]
  · intro wrote
    rw [getExecutionRequestsList_eq] at wrote
    generalize filtered : (requestTypes fork).filter
      (fun type => (requestSlot requests type).1 != 0) = types at wrote
    -- Each entry is the type byte followed by the nonempty bytes of its slot.
    have entries : List.Forall₂ (fun type request => ∃ data,
        (requestSlot requests type).2 = .ok data ∧ data.size ≠ 0 ∧
          request = ⟨#[type]⟩ ++ data) types list := by
      refine (forall₂_mem_of_mapM_ok wrote).imp fun type request ⟨mem, step⟩ => ?_
      rw [← filtered, List.mem_filter] at mem
      cases bytes : (requestSlot requests type).2 with
      | error e => simp [bytes, bind, Except.bind] at step
      | ok data =>
        simp only [bytes, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at step
        refine ⟨data, rfl, fun zero => ?_, step.symm⟩
        have := (requestSlot_count_eq_zero_iff mem.1 bytes).mpr zero
        simp [this] at mem
    have sorted : types.Pairwise (· < ·) :=
      filtered ▸ (requestTypes_pairwise fork).sublist List.filter_sublist
    have known : ∀ type ∈ types, type ∈ requestTypes fork := fun type mem =>
      (List.mem_filter.mp (filtered ▸ mem)).1
    obtain ⟨result, read⟩ := getExecutionRequestsFrom_exists (previous := none)
      (start := ExecutionRequests.empty preset fork) entries sorted
      fun type mem => ⟨known type mem, fun _ named => by cases named⟩
    obtain ⟨-, each, untouched⟩ := getExecutionRequestsFrom_spec read
    have firsts : list.map (·.data[0]?.getD 0) = types :=
      map_eq_of_forall₂ (entries.imp fun type request ⟨data, _, _, made⟩ => by
        rw [made, getElem?_zero_cons_append]
        rfl)
    suffices same : result = requests by
      rw [← same]
      exact read
    refine eq_of_requestSlot fun type member => ?_
    by_cases mem : type ∈ types
    · obtain ⟨request, requestMem, data, bytes, -, made⟩ := exists_mem_of_forall₂ entries mem
      obtain ⟨type', first, -, -, -, count, -, slot⟩ := each request requestMem
      have : type' = type := by
        rw [made, getElem?_zero_cons_append] at first
        exact (Option.some.inj first).symm
      subst this
      refine ⟨data, ?_, bytes⟩
      rw [slot, made, extract_one_cons_append]
    · have zero : (requestSlot requests type).1 = 0 := by
        have notKept := fun kept => mem (filtered ▸ List.mem_filter.mpr ⟨member, kept⟩)
        simpa using notKept
      refine ⟨.empty, ?_, requestSlot_bytes_of_count_eq_zero member zero⟩
      rw [untouched type (firsts ▸ mem), requestSlot_empty]

end EthLib.Consensus
