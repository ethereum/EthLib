module

public import EthLib.Consensus.Proofs.Transition.BuilderDebtSlots
public import EthLib.Consensus.Proofs.Transition.PayloadInputs

/-!
# Proofs: the operations of a block keep the builder debt invariant

The operations of a block run after its header and its bid.

The latest block is then the block itself, at the slot of the state.

So the payment of the parent, in the sense of the invariant, is the payment of the block's own bid.

A slashing of a proposer cancels the payments of its blocks.

The value of a cancelled payment of the block moves from the debt to the reserve of the late path.

Any other cancelled payment only lowers the debt.

An attestation adds weight to the payment of the block of its slot.

It adds weight only to a payment with an amount.

Its slot is before the slot of the state, so it never weighs the payment of the block itself.

The other operations keep the builders, their payments, their withdrawals and the latest bid.

[EIP-7732] adds the cancellation of the payments and their weight.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-! ## Cancelled payments -/

/-- A list owes a builder at most a list of the same length that owes as much at each position.
-/
private theorem owedBy_le_of_forall {index : BuilderIndex} :
    ∀ {first second : List BuilderPendingWithdrawal}, first.length = second.length →
      (∀ k (inFirst : k < first.length) (inSecond : k < second.length),
        owedBy index [first[k]] ≤ owedBy index [second[k]]) →
      owedBy index first ≤ owedBy index second
  | [], [], _, _ => Nat.le_refl _
  | [], _ :: _, same, _ => by simp at same
  | _ :: _, [], same, _ => by simp at same
  | a :: first, b :: second, same, each => by
    have head := each 0 (by simp) (by simp)
    have tail := owedBy_le_of_forall (index := index) (first := first) (second := second)
      (by simpa using same) fun k inFirst inSecond =>
        each (k + 1) (by simpa using inFirst) (by simpa using inSecond)
    simp only [owedBy, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil,
      List.getElem_cons_zero] at head tail ⊢
    omega

private theorem paymentAt_cancelProposerPayments {gloas : .glamsterdam ≤ fork}
    {proposer : ValidatorIndex} (position : Nat) :
    paymentAt (cancelProposerPayments state gloas proposer) gloas position =
      if (paymentAt state gloas position).proposerIndex = proposer then .empty
      else paymentAt state gloas position := by
  have general : ∀ found : Option BuilderPendingPayment,
      (found.map fun payment =>
        if payment.proposerIndex = proposer then .empty else payment).getD .empty =
        if (found.getD .empty).proposerIndex = proposer then .empty else found.getD .empty := by
    intro found
    cases found <;> simp
  simp only [paymentAt, cancelProposerPayments, Serialization.Ssz.RootedVector.ofVector]
  rw [Vector.getElem?_map]
  exact general _

private theorem payments_cancelProposerPayments {gloas : .glamsterdam ≤ fork}
    {proposer : ValidatorIndex} :
    ((cancelProposerPayments state gloas proposer).builderPendingPayments gloas).elements.toList =
      (state.builderPendingPayments gloas).elements.toList.map fun payment =>
        if payment.proposerIndex = proposer then .empty else payment := by
  simp [cancelProposerPayments, Serialization.Ssz.RootedVector.ofVector, Vector.toList_map]

/-- Cancelling payments never raises the debt plus the reserve of each builder.

A cancelled parent payment moves its amount from the debt to the reserve. -/
private theorem pendingBuilderTotal_add_lateBidValue_cancelProposerPayments_le
    {gloas : .glamsterdam ≤ fork} {proposer : ValidatorIndex}
    (fresh : ParentPaymentFresh state gloas) (index : BuilderIndex) :
    pendingBuilderTotal (cancelProposerPayments state gloas proposer) gloas index +
        lateBidValue (cancelProposerPayments state gloas proposer) gloas index ≤
      pendingBuilderTotal state gloas index + lateBidValue state gloas index := by
  obtain ⟨cancel, cancelDef⟩ : ∃ cancel : BuilderPendingPayment → BuilderPendingPayment,
      cancel = fun payment => if payment.proposerIndex = proposer then .empty else payment :=
    ⟨_, rfl⟩
  obtain ⟨payments, paymentsDef⟩ :=
    (⟨_, rfl⟩ : ∃ payments, payments = (state.builderPendingPayments gloas).elements.toList)
  have total : pendingBuilderTotal (cancelProposerPayments state gloas proposer) gloas index =
      owedBy index (state.builderPendingWithdrawals gloas).data.toList +
        owedBy index ((payments.map cancel).map (·.withdrawal)) := by
    simp only [pendingBuilderTotal, payments_cancelProposerPayments, cancelDef, paymentsDef]
    rfl
  -- A cancelled payment owes at most what it owed.
  have each : ∀ payment,
      owedBy index [(cancel payment).withdrawal] ≤ owedBy index [payment.withdrawal] := by
    intro payment
    simp only [cancelDef]
    split <;> simp [owedBy, BuilderPendingPayment.empty]
  have pointwise : owedBy index ((payments.map cancel).map (·.withdrawal)) ≤
      owedBy index (payments.map (·.withdrawal)) :=
    owedBy_le_of_forall (by simp) fun k _ inside => by
      simpa using each (payments[k]'(by simpa using inside))
  have bid : (cancelProposerPayments state gloas proposer).latestExecutionPayloadBid gloas =
      state.latestExecutionPayloadBid gloas := rfl
  rw [total]
  unfold pendingBuilderTotal
  rw [← paymentsDef]
  by_cases opened : latePaymentOpen (cancelProposerPayments state gloas proposer) gloas =
    latePaymentOpen state gloas
  · have late : lateBidValue (cancelProposerPayments state gloas proposer) gloas index =
        lateBidValue state gloas index := by
      simp only [lateBidValue, opened, bid]
    rw [late]
    omega
  -- The reserve opens only when the parent payment, with an amount, is cancelled.
  have position : parentPaymentPosition (cancelProposerPayments state gloas proposer) =
      parentPaymentPosition state := rfl
  unfold latePaymentOpen at opened
  rw [position] at opened
  rcases found : parentPaymentPosition state with _ | parent
  · simp [found] at opened
  rw [found] at opened
  simp only [paymentAt_cancelProposerPayments] at opened
  split at opened
  case isFalse => exact absurd rfl opened
  rename_i cancelled
  have amount : (paymentAt state gloas parent.toNat).withdrawal.amount ≠ 0 := by
    intro zero
    simp [zero, BuilderPendingPayment.empty] at opened
  have closed : lateBidValue state gloas index = 0 := by
    simp [lateBidValue, latePaymentOpen, found, amount]
  have reserved : lateBidValue (cancelProposerPayments state gloas proposer) gloas index =
      owedBy index [latestBidWithdrawal state gloas] := by
    simp [lateBidValue, latePaymentOpen, position, found, paymentAt_cancelProposerPayments,
      cancelled, BuilderPendingPayment.empty, owedBy, latestBidWithdrawal, bidPayment, bid]
  have pays := ((fresh parent found).2.resolve_left amount)
  have length : payments.length = 2 * preset.SLOTS_PER_EPOCH.toNat := by simp [paymentsDef]
  have inside : parent.toNat < payments.length := by
    rw [length]
    refine Nat.lt_of_not_le fun outside => amount ?_
    simp [paymentAt, outside, BuilderPendingPayment.empty]
  have read : paymentAt state gloas parent.toNat = payments[parent.toNat] := by
    rw [paymentAt_of_lt (length ▸ inside)]
    simp only [paymentsDef, Vector.getElem_toList]
    rfl
  -- Put the parent payment back in the cancelled list, then compare position by position.
  have moved := owedBy_set (index := index)
    (withdrawals := (payments.map cancel).map (·.withdrawal)) (k := parent.toNat)
    (by simpa using inside) payments[parent.toNat].withdrawal
  have gone : ((payments.map cancel).map (·.withdrawal))[parent.toNat]'(by simpa using inside) =
      BuilderPendingPayment.empty.withdrawal := by
    simp only [List.getElem_map, cancelDef, ← read, cancelled, ite_true]
  have back : owedBy index (((payments.map cancel).map (·.withdrawal)).set parent.toNat
      payments[parent.toNat].withdrawal) ≤ owedBy index (payments.map (·.withdrawal)) := by
    refine owedBy_le_of_forall (by simp) fun k _ _ => ?_
    simp only [List.getElem_set]
    split
    · subst_vars
      simp
    · simpa using each (payments[k]'(by simpa using ‹k < (payments.map _).length›))
  rw [read] at pays
  rw [gone, pays] at moved
  rw [pays] at back
  rw [closed, reserved]
  have empty : owedBy index [BuilderPendingPayment.empty.withdrawal] = 0 := by
    simp [owedBy, BuilderPendingPayment.empty]
  omega

/-- Cancelling the payments of the blocks of a proposer keeps the builder debt invariant. -/
theorem BuilderDebtCovered.cancelProposerPayments {gloas : .glamsterdam ≤ fork}
    {proposer : ValidatorIndex} (holds : BuilderDebtCovered state gloas) :
    BuilderDebtCovered (cancelProposerPayments state gloas proposer) gloas := by
  have position : parentPaymentPosition
      (EthLib.Consensus.cancelProposerPayments state gloas proposer) =
      parentPaymentPosition state := rfl
  refine ⟨fun index => ?_, fun index builder found exited => ?_, fun parent found => ?_,
    fun k later => ?_⟩
  · exact Nat.le_trans
      (pendingBuilderTotal_add_lateBidValue_cancelProposerPayments_le holds.parentFresh index)
      (holds.covered index)
  · have lower := pendingBuilderTotal_add_lateBidValue_cancelProposerPayments_le
      (proposer := proposer) holds.parentFresh index
    have := holds.exitedClear index builder found exited
    omega
  · rw [position] at found
    rw [paymentAt_cancelProposerPayments]
    split
    · simp [BuilderPendingPayment.empty]
    · exact holds.parentFresh parent found
  · rw [paymentAt_cancelProposerPayments,
      holds.laterEmpty k fun parent found => later parent (position ▸ found)]
    simp

/-- From Gloas, slashing a validator keeps the builder fields, then cancels payments of a proposer.
-/
private theorem slashValidator_eq_cancelProposerPayments {gloas : .glamsterdam ≤ fork}
    {slashedIndex : ValidatorIndex} {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    ∃ last proposer, BuilderFrame state last ∧
      after = Consensus.cancelProposerPayments last gloas proposer := by
  obtain ⟨_, _, _, marked, _, _, _, lowered, _, _, _, last, exitedOk, -, -, markedOk, -, -, -,
    loweredOk, -, -, raisedOk, lastOk, rfl⟩ := slashValidator_ok computed
  have loweredFrame : BuilderFrame marked lowered := by
    refine BuilderFrame.trans ?_ (builderFrame_decreaseBalance loweredOk)
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have frame : BuilderFrame state last :=
    (builderFrame_initiateValidatorExit exitedOk).trans <|
      (builderFrame_setValidator markedOk).trans <|
      loweredFrame.trans <|
      (builderFrame_increaseBalance raisedOk).trans (builderFrame_increaseBalance lastOk)
  rw [dite_eq_left gloas]
  exact ⟨last, _, frame, rfl⟩

/-- From Gloas, slashing a validator keeps the builder debt invariant. -/
theorem BuilderDebtCovered.slashValidator {gloas : .glamsterdam ≤ fork}
    {slashedIndex : ValidatorIndex} {whistleblowerIndex : Option ValidatorIndex}
    (holds : BuilderDebtCovered state gloas)
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    BuilderDebtCovered after gloas := by
  obtain ⟨_, _, frame, rfl⟩ := slashValidator_eq_cancelProposerPayments (gloas := gloas) computed
  exact (holds.of_frame frame).cancelProposerPayments

/-- From Gloas, slashing a validator keeps the builders. -/
private theorem builders_slashValidator {gloas : .glamsterdam ≤ fork}
    {slashedIndex : ValidatorIndex} {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    after.builders = state.builders := by
  obtain ⟨_, _, frame, rfl⟩ := slashValidator_eq_cancelProposerPayments (gloas := gloas) computed
  exact frame.builders

/-! ## Weighed payments -/

/-- Weighing a payment keeps the withdrawal of each payment. -/
private theorem recordPaymentWeight_withdrawals {gloas : .glamsterdam ≤ fork}
    {data : AttestationData} {current : Bool} {before updated : EpochParticipation preset fork}
    {attesters : List ValidatorIndex}
    (computed : recordPaymentWeight state gloas data current before updated attesters = .ok after) :
    (after.builderPendingPayments gloas).elements.toList.map (·.withdrawal) =
      (state.builderPendingPayments gloas).elements.toList.map (·.withdrawal) := by
  unfold recordPaymentWeight at computed
  dsimp only at computed
  split at computed
  rotate_left
  · cases computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  simp only [Serialization.Ssz.RootedVector.elements_set, Vector.toList_set, List.map_set]
  apply List.ext_getElem (by simp)
  intro k _ _
  rw [List.getElem_set]
  split
  · subst_vars
    simp only [List.getElem_map, Vector.getElem_toList]
    rfl
  · rfl

/-- Weighing a payment keeps the withdrawal at each position. -/
private theorem paymentAt_recordPaymentWeight_withdrawal {gloas : .glamsterdam ≤ fork}
    {data : AttestationData} {current : Bool} {before updated : EpochParticipation preset fork}
    {attesters : List ValidatorIndex}
    (computed : recordPaymentWeight state gloas data current before updated attesters = .ok after)
    (position : Nat) :
    (paymentAt after gloas position).withdrawal = (paymentAt state gloas position).withdrawal := by
  have same := congrArg (·[position]?) (recordPaymentWeight_withdrawals computed)
  simp only [List.getElem?_map, Vector.getElem?_toList] at same
  unfold paymentAt
  revert same
  cases (after.builderPendingPayments gloas).elements[position]? <;>
    cases (state.builderPendingPayments gloas).elements[position]? <;> simp

/-- Weighing a payment keeps each payment at another position. -/
private theorem paymentAt_recordPaymentWeight_other {gloas : .glamsterdam ≤ fork}
    {data : AttestationData} {current : Bool} {before updated : EpochParticipation preset fork}
    {attesters : List ValidatorIndex} {position : Nat}
    (computed : recordPaymentWeight state gloas data current before updated attesters = .ok after)
    (other : position ≠ attestationPaymentPosition preset current data.slot) :
    paymentAt after gloas position = paymentAt state gloas position := by
  have kept := recordPaymentWeight_other computed other
  simp only [Serialization.Ssz.RootedVector.getElem?_eq] at kept
  simp only [paymentAt, kept]

/-- Weighing a payment reads whether the vote is for the block of its own slot. -/
private theorem recordPaymentWeight_sameSlot {gloas : .glamsterdam ≤ fork}
    {data : AttestationData} {current : Bool} {before updated : EpochParticipation preset fork}
    {attesters : List ValidatorIndex}
    (computed : recordPaymentWeight state gloas data current before updated attesters = .ok after) :
    ∃ sameSlot, isAttestationSameSlot state data = .ok sameSlot := by
  unfold recordPaymentWeight at computed
  dsimp only at computed
  split at computed
  rotate_left
  · cases computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨sameSlot, sameOk, _⟩ := computed
  exact ⟨sameSlot, sameOk⟩

/-- Weighing a payment keeps the builder debt invariant once a block has run its header.

A vote of the current epoch must be for a slot of that epoch. -/
private theorem BuilderDebtCovered.recordPaymentWeight (positive : preset.PaymentQuorumPositive)
    {gloas : .glamsterdam ≤ fork} {data : AttestationData} {current : Bool}
    {before updated : EpochParticipation preset fork} {attesters : List ValidatorIndex}
    (header : state.latestBlockHeader.slot = state.slot) (started : state.slot ≠ 0)
    (epoch : current = true → computeEpochAtSlot preset data.slot = getCurrentEpoch state)
    (holds : BuilderDebtCovered state gloas)
    (computed : recordPaymentWeight state gloas data current before updated attesters = .ok after) :
    BuilderDebtCovered after gloas := by
  obtain ⟨one, fits⟩ := positive.slotsPerEpoch_bounds
  have rest := recordPaymentWeight_eq computed
  have position : parentPaymentPosition after = parentPaymentPosition state := by
    rw [rest]
    rfl
  have total : ∀ index,
      pendingBuilderTotal after gloas index = pendingBuilderTotal state gloas index := by
    intro index
    unfold pendingBuilderTotal
    rw [recordPaymentWeight_withdrawals computed, rest]
  have opened : latePaymentOpen after gloas = latePaymentOpen state gloas := by
    unfold latePaymentOpen
    rw [position]
    split <;> simp only [paymentAt_recordPaymentWeight_withdrawal computed]
  have bid : after.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by rw [rest]
  have late : ∀ index, lateBidValue after gloas index = lateBidValue state gloas index :=
    fun _ => by simp only [lateBidValue, opened, bid]
  have builders : after.builders = state.builders := by rw [rest]
  have balance : ∀ index, builderBalance after gloas index = builderBalance state gloas index :=
    fun _ => by simp only [builderBalance, builders]
  have parentAt : parentPaymentPosition state =
      some (preset.SLOTS_PER_EPOCH + state.slot % preset.SLOTS_PER_EPOCH) := by
    simp [parentPaymentPosition, slotPaymentPosition, header, getCurrentEpoch]
  -- The weighed position is not that of the parent.
  have apart : (preset.SLOTS_PER_EPOCH + state.slot % preset.SLOTS_PER_EPOCH).toNat ≠
      attestationPaymentPosition preset current data.slot := by
    intro same
    have stateLow := Nat.mod_lt state.slot.toNat one
    have dataLow := Nat.mod_lt data.slot.toNat one
    unfold attestationPaymentPosition at same
    cases current
    · simp only [Bool.false_eq_true, ↓reduceIte, UInt64.toNat_add, UInt64.toNat_mod,
        UInt64.toNat_zero] at same
      omega
    -- A vote of the current epoch at the position of the parent is at the slot of the state.
    simp only [↓reduceIte, UInt64.toNat_add, UInt64.toNat_mod] at same
    have epochs := congrArg UInt64.toNat (epoch rfl)
    simp only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div] at epochs
    have remainders : data.slot.toNat % preset.SLOTS_PER_EPOCH.toNat =
        state.slot.toNat % preset.SLOTS_PER_EPOCH.toNat := by
      omega
    have slots := Nat.div_add_mod data.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    rw [epochs, remainders, Nat.div_add_mod] at slots
    have equal : data.slot = state.slot := UInt64.toNat_inj.mp slots.symm
    -- The block root at the slot of the state is not yet known.
    obtain ⟨_, sameOk⟩ := recordPaymentWeight_sameSlot computed
    simp [isAttestationSameSlot, getBlockRootAtSlot, equal, started, bind, Except.bind] at sameOk
  refine ⟨fun index => ?_, fun index builder found exited => ?_, fun parent found => ?_,
    fun k later => ?_⟩
  · rw [total, late, balance]
    exact holds.covered index
  · rw [total, late]
    exact holds.exitedClear index builder (by rwa [builders] at found) exited
  · rw [position, parentAt] at found
    cases found
    rw [paymentAt_recordPaymentWeight_other computed apart]
    simpa only [latestBidWithdrawal, bid] using holds.parentFresh _ parentAt
  · have kept := holds.laterEmpty k fun parent found => later parent (position ▸ found)
    by_cases weighed : k = attestationPaymentPosition preset current data.slot
    · have same := recordPaymentWeight_of_noWeight computed (.inr fun payment found => by
        rw [← weighed, Serialization.Ssz.RootedVector.getElem?_eq] at found
        simp only [paymentAt, found, Option.getD_some] at kept
        rw [kept]
        rfl)
      rw [same]
      exact kept
    · rw [paymentAt_recordPaymentWeight_other computed weighed]
      exact kept

/-- Setting the participation flags of an epoch keeps the builder fields. -/
private theorem builderFrame_setEpochParticipation {current : Bool}
    {participation : EpochParticipation preset fork} :
    BuilderFrame state (setEpochParticipation state current participation) := by
  unfold setEpochParticipation
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- From Gloas, an attestation keeps the builder fields, then weighs a payment. -/
private theorem processAttestation_eq_recordPaymentWeight {gloas : .glamsterdam ≤ fork}
    {parentSlot : Slot} {attestation : Attestation preset fork}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    ∃ (raised : BeaconState preset fork) (data : AttestationData) (current : Bool)
      (before updated : EpochParticipation preset fork) (attesters : List ValidatorIndex),
      BuilderFrame state raised ∧
        recordPaymentWeight raised gloas data current before updated attesters = .ok after := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) gloas
  unfold Consensus.processAttestation processAttestationAltair at computed
  simp only [altair, gloas, ↓reduceDIte, bind_ok_iff, ensure_ok_iff, liftAccessor_ok]
    at computed
  obtain ⟨_, -, _, -, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, raised, raisedOk, recorded⟩ := computed
  exact ⟨raised, _, _, _, _, _,
    builderFrame_setEpochParticipation.trans (builderFrame_increaseBalance raisedOk), recorded⟩

/-- From Gloas, an attestation keeps the builder debt invariant once a block has run its header.

The latest block must be at the slot of the state, and that slot must not be the first.

The preset must have a payment quorum of at least one gwei, as mainnet and minimal do. -/
theorem BuilderDebtCovered.processAttestation (positive : preset.PaymentQuorumPositive)
    {gloas : .glamsterdam ≤ fork} {parentSlot : Slot} {attestation : Attestation preset fork}
    (header : state.latestBlockHeader.slot = state.slot) (started : state.slot ≠ 0)
    (holds : BuilderDebtCovered state gloas)
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    BuilderDebtCovered after gloas := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) gloas
  unfold Consensus.processAttestation processAttestationAltair at computed
  simp only [altair, gloas, ↓reduceDIte, bind_ok_iff, ensure_ok_iff, liftAccessor_ok]
    at computed
  obtain ⟨_, -, _, slotEpoch, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, raised, raisedOk, recorded⟩ := computed
  have frame : BuilderFrame state raised :=
    builderFrame_setEpochParticipation.trans (builderFrame_increaseBalance raisedOk)
  have epochs : getCurrentEpoch raised = getCurrentEpoch state := by
    unfold getCurrentEpoch
    rw [frame.slot]
  refine (holds.of_frame frame).recordPaymentWeight positive
    (by rw [frame.headerSlot, frame.slot]; exact header) (by rw [frame.slot]; exact started)
    (fun current => ?_) recorded
  rw [epochs, ← slotEpoch]
  simpa using current

/-! ## The operations -/

/-- A step of an attester slashing keeps the builder debt invariant. -/
private theorem BuilderDebtCovered.slashIfSlashable {gloas : .glamsterdam ≤ fork}
    {step next : BeaconState preset fork × Bool} {index : ValidatorIndex}
    (holds : BuilderDebtCovered step.1 gloas)
    (computed : slashIfSlashable config step index = .ok next) :
    BuilderDebtCovered next.1 gloas := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [Consensus.slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact holds.slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ holds

/-- From Gloas, a relation that each step of the operations keeps holds across them.

The steps are a slashing, the weighing of a payment, and the steps that keep the builder fields.

The relation must be transitive. -/
private theorem processOperations_of_steps {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (keeps : BeaconState preset fork → BeaconState preset fork → Prop)
    (trans : ∀ {first second third}, keeps first second → keeps second third →
      keeps first third)
    (frame : ∀ {first second}, BuilderFrame first second → keeps first second)
    (slash : ∀ {first second} {slashedIndex : ValidatorIndex}
      {whistleblowerIndex : Option ValidatorIndex},
      slashValidator config first slashedIndex whistleblowerIndex = .ok second →
        keeps first second)
    (weigh : ∀ {first second} {data : AttestationData} {current : Bool}
      {before updated : EpochParticipation preset fork} {attesters : List ValidatorIndex},
      recordPaymentWeight first gloas data current before updated attesters = .ok second →
        keeps first second)
    (computed : processOperations config checks state body parentSlot = .ok after) :
    keeps state after := by
  simp only [Consensus.processOperations, gloas, ↓reduceDIte, processOperationsGloas,
    bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
    attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
  have proposers := foldlM_ok_invariant (fun s => keeps state s)
    (fun _ _ _ kept ok => by
      simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
      exact trans kept (slash slashed)) (frame (BuilderFrame.refl state)) proposersOk
  have attesters := foldlM_ok_invariant (fun s => keeps state s)
    (fun s _ _ kept ok => by
      simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
        Except.ok.injEq] at ok
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
      exact trans kept (foldlM_ok_invariant (fun step => keeps s step.1)
        (fun step _ index before ok => by
          obtain ⟨current, slashedAny⟩ := step
          simp only [Consensus.slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
          obtain ⟨_, _, ok⟩ := ok
          split at ok
          · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
            obtain ⟨_, slashed, rfl⟩ := ok
            exact trans before (slash slashed)
          · simp only [pure, Except.pure, Except.ok.injEq] at ok
            exact ok ▸ before)
        (show keeps s (s, false).1 from frame (BuilderFrame.refl s)) folded))
      proposers attestersOk
  have attested := foldlM_ok_invariant (fun s => keeps state s)
    (fun _ _ _ kept ok => by
      obtain ⟨_, _, _, _, _, _, framed, recorded⟩ :=
        processAttestation_eq_recordPaymentWeight (gloas := gloas) ok
      exact trans kept (trans (frame framed) (weigh recorded))) attesters attestedOk
  have exited := foldlM_ok_invariant (fun s => keeps state s)
    (fun _ _ _ kept ok => by
      unfold processVoluntaryExit at ok
      simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
      exact trans kept (frame (builderFrame_initiateValidatorExit exited))) attested exitsOk
  have changed := foldlM_ok_invariant (fun s => keeps state s)
    (fun _ _ _ kept ok => by
      obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
      exact trans kept (frame (builderFrame_setValidator set))) exited changesOk
  exact foldlM_ok_invariant (fun s => keeps state s)
    (fun _ _ _ kept ok => by
      rw [processPayloadAttestation_eq ok]
      exact kept) changed paid

/-- From Gloas, the operations of a block keep the builder debt invariant.

The latest block must be at the slot of the state, and that slot must not be the first.

The preset must have a payment quorum of at least one gwei, as mainnet and minimal do. -/
theorem BuilderDebtCovered.processOperations (positive : preset.PaymentQuorumPositive)
    {gloas : .glamsterdam ≤ fork} {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (header : state.latestBlockHeader.slot = state.slot) (started : state.slot ≠ 0)
    (holds : BuilderDebtCovered state gloas)
    (computed : processOperations config checks state body parentSlot = .ok after) :
    BuilderDebtCovered after gloas := by
  simp only [Consensus.processOperations, gloas, ↓reduceDIte, processOperationsGloas,
    bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
    attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
  have proposers := foldlM_ok_invariant (fun s => BuilderDebtCovered s gloas)
    (fun _ _ _ kept ok => by
      simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
      exact kept.slashValidator slashed) holds proposersOk
  have attesters := foldlM_ok_invariant (fun s => BuilderDebtCovered s gloas)
    (fun s _ _ kept ok => by
      simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
        Except.ok.injEq] at ok
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
      exact foldlM_ok_invariant (fun step => BuilderDebtCovered step.1 gloas)
        (fun _ _ _ before ok => before.slashIfSlashable ok)
        (show BuilderDebtCovered (s, false).1 gloas from kept) folded) proposers attestersOk
  -- The slashings keep the slot and the latest block header, which the attestations read.
  have slashed :=
    (PayloadInputs.foldlM (fun _ _ _ ok => payloadInputs_processProposerSlashing ok)
      proposersOk).trans <|
    PayloadInputs.foldlM (fun _ _ _ ok => payloadInputs_processAttesterSlashing ok) attestersOk
  have attested := foldlM_ok_invariant
    (fun s => BuilderDebtCovered s gloas ∧ PayloadInputs state s)
    (fun _ _ _ ⟨kept, inputs⟩ ok =>
      ⟨kept.processAttestation positive
          (by rw [inputs.latestBlockHeader, inputs.slot]; exact header)
          (by rw [inputs.slot]; exact started) ok,
        inputs.trans (payloadInputs_processAttestation ok)⟩)
    ⟨attesters, slashed⟩ attestedOk
  have exited := foldlM_ok_invariant (fun s => BuilderDebtCovered s gloas)
    (fun _ _ _ kept ok => by
      unfold processVoluntaryExit at ok
      simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
      exact kept.of_frame (builderFrame_initiateValidatorExit exited)) attested.1 exitsOk
  have changed := foldlM_ok_invariant (fun s => BuilderDebtCovered s gloas)
    (fun _ _ _ kept ok => by
      obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
      exact kept.of_frame (builderFrame_setValidator set)) exited changesOk
  exact foldlM_ok_invariant (fun s => BuilderDebtCovered s gloas)
    (fun _ _ _ kept ok => by
      rw [processPayloadAttestation_eq ok]
      exact kept) changed paid

/-- From Gloas, the operations of a block keep the builders. -/
theorem processOperations_builders (gloas : .glamsterdam ≤ fork)
    {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    after.builders = state.builders :=
  processOperations_of_steps (gloas := gloas) (fun first second => second.builders = first.builders)
    (fun one two => two.trans one) (fun frame => frame.builders)
    (fun slashed => builders_slashValidator (gloas := gloas) slashed)
    (fun weighed => by rw [recordPaymentWeight_eq weighed]) computed

/-! ## Emptied payments -/

/-- From Gloas, slashing a validator may only empty pending payments. -/
private theorem PaymentCancel.slashValidator {gloas : .glamsterdam ≤ fork}
    {slashedIndex : ValidatorIndex} {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    PaymentCancel state after gloas := by
  obtain ⟨last, proposer, frame, rfl⟩ :=
    slashValidator_eq_cancelProposerPayments (gloas := gloas) computed
  refine (PaymentCancel.of_frame frame).trans ⟨rfl, rfl, rfl, rfl, fun position => ?_⟩
  rw [paymentAt_cancelProposerPayments]
  split
  · exact Or.inr (by simp [BuilderPendingPayment.empty])
  · exact Or.inl rfl

/-- From Gloas, the operations of a block may only empty pending payments.

A slashing empties the payments of the blocks of the slashed proposer.

An attestation adds weight to a payment, and keeps its withdrawal. -/
theorem PaymentCancel.processOperations {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    PaymentCancel state after gloas :=
  processOperations_of_steps (gloas := gloas) (fun first second => PaymentCancel first second gloas)
    PaymentCancel.trans PaymentCancel.of_frame
    PaymentCancel.slashValidator
    (fun weighed => by
      have fields := recordPaymentWeight_eq weighed
      exact ⟨congrArg (·.slot) fields, congrArg (·.latestBlockHeader.slot) fields,
        congrArg (·.latestExecutionPayloadBid gloas) fields,
        congrArg (·.builderPendingWithdrawals gloas) fields, fun position =>
          Or.inl (paymentAt_recordPaymentWeight_withdrawal weighed position)⟩) computed

end EthLib.Consensus
