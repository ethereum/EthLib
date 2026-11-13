module

public import EthLib.Consensus.BeaconApi.Produce
public import EthLib.Consensus.Proofs.BeaconApi.Rewards

/-!
# Proofs: the value of a produced block

The consensus value of a block is the total of its block rewards, at 10^9 Wei per Gwei.

Under the hypotheses of the block rewards, it is the rise of the proposer's balance in Wei.

That rise is over the operations and the sync aggregate of the block.

Through Fulu, a factor of zero keeps the local payload.

From Gloas, a chosen bid is accepted, has the largest weight and beats the local payload.

No bid is chosen exactly when no accepted bid beats the local payload, so it wins a tie.

Changing an execution payment that reaches its cap to another at or above it keeps the choice.

The weight of a bid fits in 128 bits.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base

variable {preset : Preset} {fork : Fork} {state : BeaconState preset fork}

/-- The consensus value of a block is the total of its block rewards, in Wei. -/
theorem consensusBlockValue_ok_iff {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork} {value : Nat} :
    consensusBlockValue config checks engine state block = .ok value ↔
      ∃ rewards, blockRewards config checks engine state block = .ok rewards ∧
        value = rewards.total.toNat * GWEI_TO_WEI := by
  unfold consensusBlockValue
  cases blockRewards config checks engine state block with
  | error error => simp [bind, Except.bind]
  | ok rewards =>
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq]
    exact ⟨fun valued => ⟨rewards, rfl, valued.symm⟩, fun ⟨_, same, valued⟩ => by
      cases same
      exact valued.symm⟩

/-- The consensus value of a block is the rise of the proposer's balance, in Wei.

The rise is over the operations and the sync aggregate of the block.

The hypotheses are those under which the block rewards give that rise. -/
theorem consensusBlockValue_balance {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork} {value : Nat}
    {after : BeaconState preset fork} {validator : Validator}
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (applied : processBlock config checks engine state block = .ok after)
    (valued : consensusBlockValue config checks engine state block = .ok value)
    (found : state.validators.data[block.proposerIndex.toNat]? = some validator)
    (held : block.proposerIndex.toNat < state.balances.data.size)
    (unslashedByProposers : ∀ slashing ∈ block.body.proposerSlashings.data,
      slashing.signedHeader1.message.proposerIndex ≠ block.proposerIndex)
    (unslashedByAttesters : ∀ slashing ∈ block.body.attesterSlashings.data,
      block.proposerIndex ∉ slashingIndices slashing)
    (undeposited : ∀ before : fork < .pectra,
      ∀ deposit ∈ (block.body.deposits (Nat.lt_trans before (by decide))).data,
        deposit.data.pubkey ≠ validator.pubkey)
    (unswitched : ∀ electra : .pectra ≤ fork ∧ fork < .glamsterdam,
      ∀ request ∈ (block.body.executionRequests electra).consolidations.data,
        request.sourcePubkey ≠ validator.pubkey)
    (unseated : ∀ altair : .altair ≤ fork,
      validator.pubkey ∉ (state.currentSyncCommittee altair).value.pubkeys.toList) :
    ∃ start balance final, stateBeforeOperations config checks engine state block = .ok start ∧
      start.balances.data[block.proposerIndex.toNat]? = some balance ∧
      after.balances.data[block.proposerIndex.toNat]? = some final ∧
      final.toNat * GWEI_TO_WEI = balance.toNat * GWEI_TO_WEI + value := by
  obtain ⟨rewards, answered, rfl⟩ := consensusBlockValue_ok_iff.mp valued
  obtain ⟨start, balance, final, startOk, balanceOk, finalOk, risen⟩ :=
    blockRewards_balance apart applied answered found held unslashedByProposers
      unslashedByAttesters undeposited unswitched unseated
  exact ⟨start, balance, final, startOk, balanceOk, finalOk, by rw [risen, Nat.add_mul]⟩

/-- Through Fulu, with a factor of zero the node returns its local payload. -/
theorem preferLocalV3_zero (localValue builderValue : Nat) :
    preferLocalV3 localValue builderValue 0 = true := by
  simp [preferLocalV3]

/-- The capped value of a bid is below 2^64. -/
private theorem cappedBidValue_lt (bid : CandidateBid) : cappedBidValue bid < 2 ^ 64 := by
  have : UINT64_MAX.toNat = 2 ^ 64 - 1 := by decide
  unfold cappedBidValue
  omega

/-- The weight of a bid fits in 128 bits. -/
theorem bidWeight_lt (bid : CandidateBid) : bidWeight bid < 2 ^ 128 := by
  have factor := bid.terms.builderBoostFactor.toNat_lt
  have value := cappedBidValue_lt bid
  unfold bidWeight
  calc bid.terms.builderBoostFactor.toNat * cappedBidValue bid
      < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' factor value
    _ = 2 ^ 128 := by rw [← Nat.pow_add]

/-- The heaviest bid of a list is a member of it. -/
private theorem heaviestBid_mem : ∀ {l : List CandidateBid} {bid : CandidateBid},
    heaviestBid l = some bid → bid ∈ l
  | [], _, h => by simp [heaviestBid] at h
  | b :: rest, bid, h => by
    unfold heaviestBid at h
    cases hr : heaviestBid rest with
    | none => rw [hr] at h; cases h; simp
    | some o =>
      simp only [hr] at h
      have := heaviestBid_mem hr
      by_cases w : bidWeight o ≤ bidWeight b
      · simp only [w, ite_true] at h; cases h; simp
      · simp only [w, ite_false] at h; cases h; simp [this]

/-- The heaviest bid of a list is none exactly when the list is empty. -/
private theorem heaviestBid_eq_none : ∀ {l : List CandidateBid},
    heaviestBid l = none ↔ l = []
  | [] => by simp [heaviestBid]
  | b :: rest => by
    unfold heaviestBid
    cases hr : heaviestBid rest with
    | none => simp [heaviestBid_eq_none.mp hr]
    | some o =>
      simp only
      by_cases w : bidWeight o ≤ bidWeight b <;> simp [w]

/-- The heaviest bid of a list weighs at least each member. -/
private theorem heaviestBid_max : ∀ {l : List CandidateBid} {bid : CandidateBid},
    heaviestBid l = some bid → ∀ other ∈ l, bidWeight other ≤ bidWeight bid
  | [], _, h, _, _ => by simp [heaviestBid] at h
  | b :: rest, bid, h, other, listed => by
    unfold heaviestBid at h
    cases hr : heaviestBid rest with
    | none =>
      rw [hr] at h; cases h
      have := heaviestBid_eq_none.mp hr
      subst this
      simp at listed; subst listed; exact Nat.le_refl _
    | some o =>
      simp only [hr] at h
      have ih := heaviestBid_max hr
      rcases List.mem_cons.mp listed with rfl | inRest
      · by_cases w : bidWeight o ≤ bidWeight other
        · simp only [w, ite_true] at h; cases h; exact Nat.le_refl _
        · simp only [w, ite_false] at h; cases h; omega
      · have := ih other inRest
        by_cases w : bidWeight o ≤ bidWeight b
        · simp only [w, ite_true] at h; cases h; omega
        · simp only [w, ite_false] at h; cases h; exact this

/-- A map that keeps weights commutes with the heaviest bid. -/
private theorem heaviestBid_map {change : CandidateBid → CandidateBid}
    (weight : ∀ bid, bidWeight (change bid) = bidWeight bid) :
    ∀ l : List CandidateBid, heaviestBid (l.map change) = (heaviestBid l).map change
  | [] => by simp [heaviestBid]
  | b :: rest => by
    simp only [List.map_cons, heaviestBid]
    rw [heaviestBid_map weight rest]
    cases heaviestBid rest with
    | none => simp
    | some o =>
      simp only [Option.map_some, weight]
      split <;> simp

/-- A chosen bid is the heaviest of the accepted ones, and beats the local value. -/
private theorem selectPayload_some {localValue : Nat} {bids : List CandidateBid}
    {bid : CandidateBid} (chosen : selectPayload localValue bids = some bid) :
    heaviestBid (bids.filter bidAccepted) = some bid ∧
      100 * localValue < bidWeight bid * GWEI_TO_WEI := by
  unfold selectPayload at chosen
  cases h : heaviestBid (bids.filter bidAccepted) with
  | none => simp [h] at chosen
  | some o =>
    simp only [h, Option.filter_some] at chosen
    split at chosen
    · rename_i hp
      cases chosen
      exact ⟨rfl, by simpa using hp⟩
    · simp at chosen

/-- A chosen bid is in the list, and its terms accept it. -/
theorem selectPayload_accepted {localValue : Nat} {bids : List CandidateBid}
    {bid : CandidateBid} (chosen : selectPayload localValue bids = some bid) :
    bid ∈ bids ∧ bidAccepted bid = true :=
  List.mem_filter.mp (heaviestBid_mem (selectPayload_some chosen).1)

/-- A chosen bid weighs at least as much as each accepted bid of the list. -/
theorem selectPayload_max {localValue : Nat} {bids : List CandidateBid}
    {bid : CandidateBid} (chosen : selectPayload localValue bids = some bid)
    {other : CandidateBid} (listed : other ∈ bids) (accepted : bidAccepted other = true) :
    bidWeight other ≤ bidWeight bid :=
  heaviestBid_max (selectPayload_some chosen).1 other (List.mem_filter.mpr ⟨listed, accepted⟩)

/-- A chosen bid weighs more than 100 times the local value, in Wei. -/
theorem selectPayload_beats_local {localValue : Nat} {bids : List CandidateBid}
    {bid : CandidateBid} (chosen : selectPayload localValue bids = some bid) :
    100 * localValue < bidWeight bid * GWEI_TO_WEI :=
  (selectPayload_some chosen).2

/-- The node keeps its local payload exactly when no accepted bid weighs more than it.

So the local payload wins a tie. -/
theorem selectPayload_eq_none_iff {localValue : Nat} {bids : List CandidateBid} :
    selectPayload localValue bids = none ↔
      ∀ bid ∈ bids, bidAccepted bid = true → bidWeight bid * GWEI_TO_WEI ≤ 100 * localValue := by
  constructor
  · intro none other listed accepted
    by_contra lt
    have lt : 100 * localValue < bidWeight other * GWEI_TO_WEI := by omega
    have inl := List.mem_filter.mpr ⟨listed, accepted⟩
    cases h : heaviestBid (bids.filter bidAccepted) with
    | none =>
      simp [heaviestBid_eq_none] at h
      rw [h other listed] at accepted
      cases accepted
    | some o =>
      have le := heaviestBid_max h other inl
      have lt' : 100 * localValue < bidWeight o * GWEI_TO_WEI :=
        Nat.lt_of_lt_of_le lt (Nat.mul_le_mul_right _ le)
      unfold selectPayload at none
      simp [h] at none
      omega
  · intro all
    unfold selectPayload
    cases h : heaviestBid (bids.filter bidAccepted) with
    | none => simp
    | some o =>
      have mem := List.mem_filter.mp (heaviestBid_mem h)
      have := all o mem.1 mem.2
      simp only [Option.filter_some]
      simp [Nat.not_lt.mpr this]

/-- A change of bids that keeps their signers, terms and values keeps the choice. -/
theorem selectPayload_map {localValue : Nat} {bids : List CandidateBid}
    {change : CandidateBid → CandidateBid} (signer : ∀ bid, (change bid).signer = bid.signer)
    (terms : ∀ bid, (change bid).terms = bid.terms)
    (value : ∀ bid, cappedBidValue (change bid) = cappedBidValue bid) :
    selectPayload localValue (bids.map change) = (selectPayload localValue bids).map change := by
  have accepted : ∀ bid, bidAccepted (change bid) = bidAccepted bid := by
    intro bid
    simp [bidAccepted, signer, terms, value]
  have weight : ∀ bid, bidWeight (change bid) = bidWeight bid := by
    intro bid
    simp [bidWeight, terms, value]
  have filt : (bids.map change).filter bidAccepted = (bids.filter bidAccepted).map change := by
    rw [List.filter_map]
    congr 1
    exact List.filter_congr (fun bid _ => accepted bid)
  unfold selectPayload
  rw [filt, heaviestBid_map weight]
  cases heaviestBid (bids.filter bidAccepted) with
  | none => simp
  | some o =>
    simp only [Option.map_some, Option.filter_some, weight]
    split <;> simp

/-- An execution payment at or above its cap counts as the cap, whatever its size. -/
theorem cappedBidValue_cap {bid : CandidateBid} {payment : Gwei}
    (above : bid.terms.maxExecutionPayment ≤ bid.executionPayment)
    (raised : bid.terms.maxExecutionPayment ≤ payment) :
    cappedBidValue { bid with executionPayment := payment } = cappedBidValue bid := by
  have a : bid.terms.maxExecutionPayment.toNat ≤ bid.executionPayment.toNat := above
  have r : bid.terms.maxExecutionPayment.toNat ≤ payment.toNat := raised
  simp only [cappedBidValue, builderBidValue]
  rw [Nat.min_eq_right a, Nat.min_eq_right r]

/-- Changing the execution payments that reach their caps keeps the choice.

Each such bid takes a new payment, also at or above its cap. -/
theorem selectPayload_cap {localValue : Nat} {bids : List CandidateBid}
    {payment : CandidateBid → Gwei}
    (raised : ∀ bid, bid.terms.maxExecutionPayment ≤ payment bid) :
    let raise := fun bid : CandidateBid =>
      if bid.terms.maxExecutionPayment ≤ bid.executionPayment then
        { bid with executionPayment := payment bid }
      else bid
    selectPayload localValue (bids.map raise) = (selectPayload localValue bids).map raise := by
  intro raise
  refine selectPayload_map (fun bid => ?_) (fun bid => ?_) (fun bid => ?_)
  · simp only [raise]; split <;> rfl
  · simp only [raise]; split <;> rfl
  · simp only [raise]
    split
    · rename_i h; exact cappedBidValue_cap h (raised bid)
    · rfl

end EthLib.Consensus.BeaconApi
