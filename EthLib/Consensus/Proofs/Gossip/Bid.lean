module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.GasLimit
public import EthLib.Consensus.Gossip.Bid
public import EthLib.Base.Proofs.Uint64
public import EthLib.Networking.Proofs.Gossip.Validation

/-!
# Proofs: the topic of bids

The topic checks a bid in a fixed order, so its outcome is a chain of checks.

Once the computed inputs are fixed, the outcome is that chain.

A bid is valid exactly when every check passes.

A valid bid records its key, and a bid with the same key is then ignored.

Each valid bid beats the best value before it, for its slot and parents.

So the best value recorded for a slot and its parents only grows.

A compatible gas limit moves from the parent's limit by less than a 1024th of it.

The check of the inclusion lists of Heze accepts before Heze, and never rejects.

A bid on the parent of the head block, and on the payload it builds on, is on the head branch.

Otherwise it must build on the head block, with the payload that a proposer would build on.

So a valid bid builds on the head block, or on its parent and the payload that the head builds on.

The exit check reads the envelope that the store keeps for the parent block of a bid.

It does so when the bid builds on the latest payload of the parent state, advanced to its slot.

It then reports an exit exactly when a request there has the key and address of the builder.

It fails when the store lacks that envelope.

So the store holds the parent envelope of a valid bid on that payload.

No exit request of that envelope has both the key and the address of the builder of the bid.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Networking.Gossip Networking.Gossip.ValidationResult

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {seen : Seen} {store : Store preset fork} {gloas : .glamsterdam ≤ fork}
  {signed : SignedExecutionPayloadBid preset fork} {currentTimeMs : UInt64}

/-! ## The gas limit -/

/-- A compatible gas limit is within the bounds that the parent's limit sets.

The bounds are the parent's limit minus and plus a 1024th of it, less one. -/
theorem isGasLimitTargetCompatible_bounds {parent gasLimit target : UInt64}
    (compatible : isGasLimitTargetCompatible parent gasLimit target = .ok true) :
    parent.toNat - (parent.toNat / 1024 - 1) ≤ gasLimit.toNat ∧
      gasLimit.toNat ≤ parent.toNat + (parent.toNat / 1024 - 1) := by
  unfold isGasLimitTargetCompatible at compatible
  cases sum : addChecked parent (saturatingSub (parent / 1024) 1) with
  | error e => simp [sum, bind, Except.bind] at compatible
  | ok high =>
    simp only [sum, bind, Except.bind, pure, Except.pure, Except.ok.injEq, beq_iff_eq] at compatible
    rw [compatible]
    exact gasLimitToward_bounds parent.toNat target.toNat

/-- A compatible gas limit differs from a parent's limit of at least 1024 by less than its 1024th.
-/
theorem isGasLimitTargetCompatible_close {parent gasLimit target : UInt64}
    (large : 1024 ≤ parent.toNat)
    (compatible : isGasLimitTargetCompatible parent gasLimit target = .ok true) :
    gasLimit.toNat < parent.toNat + parent.toNat / 1024 ∧
      parent.toNat < gasLimit.toNat + parent.toNat / 1024 := by
  have := isGasLimitTargetCompatible_bounds compatible
  omega

/-! ## Seen keys -/

/-- A bid whose slot, parents and builder have a valid bid already is ignored. -/
theorem validateExecutionPayloadBid_of_seen
    (known : (signed.message.slot, signed.message.parentBlockHash, signed.message.parentBlockRoot,
      signed.message.builderIndex) ∈ seen.executionPayloadBids) :
    validateExecutionPayloadBid config checks seen store gloas signed currentTimeMs =
      .ok (.ignore "already seen valid bid for this slot, parent, and builder") := by
  simp [validateExecutionPayloadBid, known, pure, Except.pure]

/-- After a valid bid, a bid of the same builder for the same slot and parents is ignored. -/
theorem validateExecutionPayloadBid_recordExecutionPayloadBid
    {other : SignedExecutionPayloadBid preset fork}
    (sameSlot : other.message.slot = signed.message.slot)
    (sameHash : other.message.parentBlockHash = signed.message.parentBlockHash)
    (sameRoot : other.message.parentBlockRoot = signed.message.parentBlockRoot)
    (sameBuilder : other.message.builderIndex = signed.message.builderIndex) :
    validateExecutionPayloadBid config checks (seen.recordExecutionPayloadBid signed) store gloas
        other currentTimeMs =
      .ok (.ignore "already seen valid bid for this slot, parent, and builder") :=
  validateExecutionPayloadBid_of_seen (by
    simp [Seen.recordExecutionPayloadBid, sameSlot, sameHash, sameRoot, sameBuilder])

/-- After a valid bid, the best value for its slot and parents is its own value. -/
theorem bestExecutionPayloadBidFor_recordExecutionPayloadBid :
    (seen.recordExecutionPayloadBid signed).bestExecutionPayloadBidFor
        (signed.message.slot, signed.message.parentBlockHash, signed.message.parentBlockRoot) =
      some signed.message.value := by
  simp [Seen.recordExecutionPayloadBid, Seen.bestExecutionPayloadBidFor]

/-- A bid whose value does not beat the best value for its slot and parents is ignored.

That check comes after the check of the seen key. -/
theorem validateExecutionPayloadBid_of_not_best {best : Gwei}
    (fresh : (signed.message.slot, signed.message.parentBlockHash, signed.message.parentBlockRoot,
      signed.message.builderIndex) ∉ seen.executionPayloadBids)
    (recorded : seen.bestExecutionPayloadBidFor
      (signed.message.slot, signed.message.parentBlockHash, signed.message.parentBlockRoot) =
        some best)
    (low : signed.message.value ≤ best) :
    validateExecutionPayloadBid config checks seen store gloas signed currentTimeMs =
      .ok (.ignore "bid is not the highest value bid seen for this slot and parent") := by
  have notBelow : ¬best < signed.message.value := by
    rw [UInt64.lt_iff_toNat_lt]
    rw [UInt64.le_iff_toNat_le] at low
    omega
  simp [validateExecutionPayloadBid, fresh, recorded, notBelow, pure, Except.pure]

/-- A valid bid beats the best value recorded for its slot and parents, if there is one. -/
theorem lt_value_of_validateExecutionPayloadBid_eq_accept {best : Gwei}
    (valid : validateExecutionPayloadBid config checks seen store gloas signed currentTimeMs =
      .ok accept)
    (recorded : seen.bestExecutionPayloadBidFor
      (signed.message.slot, signed.message.parentBlockHash, signed.message.parentBlockRoot) =
        some best) :
    best < signed.message.value := by
  by_cases seenKey : (signed.message.slot, signed.message.parentBlockHash,
      signed.message.parentBlockRoot, signed.message.builderIndex) ∈ seen.executionPayloadBids
  · rw [validateExecutionPayloadBid_of_seen seenKey] at valid
    cases valid
  · by_cases below : best < signed.message.value
    · exact below
    · have low : signed.message.value ≤ best := by
        rw [UInt64.lt_iff_toNat_lt] at below
        rw [UInt64.le_iff_toNat_le]
        omega
      rw [validateExecutionPayloadBid_of_not_best seenKey recorded low] at valid
      cases valid

/-! ## The inclusion lists of Heze -/

/-- Before Heze a bid has no inclusion list bits, so their check accepts. -/
theorem bidInclusionListOutcome_of_lt_heze {state : BeaconState preset fork}
    {bid : ExecutionPayloadBid preset fork} (early : ¬ .hegota ≤ fork) :
    bidInclusionListOutcome store state bid = .ok accept := by
  simp [bidInclusionListOutcome, early, pure, Except.pure]

/-- The check of the inclusion list bits of a bid never rejects. -/
theorem bidInclusionListOutcome_ne_reject {state : BeaconState preset fork}
    {bid : ExecutionPayloadBid preset fork} {reason : String} :
    bidInclusionListOutcome store state bid ≠ .ok (.reject reason) := by
  unfold bidInclusionListOutcome
  split
  · intro h
    simp only [bind, Except.bind] at h
    repeat' split at h
    all_goals simp_all [ignoreUnless, pure, Except.pure, Except.mapError]
    all_goals split at h <;> simp_all
  · simp [pure, Except.pure]

/-! ## The head branch -/

/-- The check of the head branch, once the head and its block are known.

A bid on the parent of the head block, and on the payload that the head block builds on, passes.

Otherwise a bid on a block other than the head block fails.

Otherwise a bid on the head block needs the decision whether to build on the full head.

If it would, the bid passes exactly when its parent payload is the head's own payload.

If not, it passes exactly when that parent payload is the one that the head block builds on.

A failure of that decision is a failure of the check. -/
theorem isBidCompatibleWithHead_eq_ok_iff {bid : ExecutionPayloadBid preset fork}
    {head : ForkChoiceNode} {headBlock : BeaconBlock preset fork} {compatible : Bool}
    (chosen : store.getHead config = .ok head)
    (stored : store.blocks[head.root]? = some headBlock) :
    store.isBidCompatibleWithHead config gloas bid = .ok compatible ↔
      if bid.parentBlockRoot = headBlock.parentRoot ∧ bid.parentBlockHash =
          (headBlock.body.signedExecutionPayloadBid gloas).message.parentBlockHash then
        compatible = true
      else if bid.parentBlockRoot ≠ head.root then compatible = false
      else ∃ full, store.shouldBuildOnFull gloas head bid.slot = .ok full ∧
        (compatible = true ↔ bid.parentBlockHash =
          if full then (headBlock.body.signedExecutionPayloadBid gloas).message.blockHash
          else (headBlock.body.signedExecutionPayloadBid gloas).message.parentBlockHash) := by
  simp only [Store.isBidCompatibleWithHead, chosen, Store.block, stored, bind, Except.bind, pure,
    Except.pure]
  by_cases onParent : bid.parentBlockRoot = headBlock.parentRoot ∧ bid.parentBlockHash =
      (headBlock.body.signedExecutionPayloadBid gloas).message.parentBlockHash
  · cases compatible <;> simp [onParent]
  · have notBoth : (bid.parentBlockRoot == headBlock.parentRoot &&
        bid.parentBlockHash ==
          (headBlock.body.signedExecutionPayloadBid gloas).message.parentBlockHash) = false := by
      simpa using onParent
    rw [ite_eq_right_of_eq_false _ _ (eq_false onParent), notBoth]
    by_cases onHead : bid.parentBlockRoot = head.root
    · cases computed : store.shouldBuildOnFull gloas head bid.slot with
      | error e => simp [onHead]
      | ok full => cases full <;> cases compatible <;> simp [onHead]
    · cases compatible <;> simp [onHead]

/-- A bid on the head branch builds on the head block, or on the parent of the head block.

On the head block, its parent payload is the head's own payload or the one the head builds on.

On the parent, its parent payload is the one that the head block builds on.

The head and its block are then known. -/
theorem exists_head_of_isBidCompatibleWithHead {bid : ExecutionPayloadBid preset fork}
    (compatible : store.isBidCompatibleWithHead config gloas bid = .ok true) :
    ∃ head headBlock, store.getHead config = .ok head ∧ store.blocks[head.root]? = some headBlock ∧
      (bid.parentBlockRoot = head.root ∧
          (bid.parentBlockHash =
              (headBlock.body.signedExecutionPayloadBid gloas).message.blockHash ∨
            bid.parentBlockHash =
              (headBlock.body.signedExecutionPayloadBid gloas).message.parentBlockHash) ∨
        bid.parentBlockRoot = headBlock.parentRoot ∧
          bid.parentBlockHash =
            (headBlock.body.signedExecutionPayloadBid gloas).message.parentBlockHash) := by
  cases chosen : store.getHead config with
  | error e => simp [Store.isBidCompatibleWithHead, chosen, bind, Except.bind] at compatible
  | ok head =>
    cases stored : store.blocks[head.root]? with
    | none =>
      simp [Store.isBidCompatibleWithHead, chosen, Store.block, stored, bind, Except.bind,
        throw, throwThe, MonadExceptOf.throw] at compatible
    | some headBlock =>
      refine ⟨head, headBlock, rfl, stored, ?_⟩
      have value := (isBidCompatibleWithHead_eq_ok_iff chosen stored).mp compatible
      by_cases onParent : bid.parentBlockRoot = headBlock.parentRoot ∧ bid.parentBlockHash =
          (headBlock.body.signedExecutionPayloadBid gloas).message.parentBlockHash
      · exact Or.inr onParent
      · rw [ite_eq_right_of_eq_false _ _ (eq_false onParent)] at value
        by_cases onHead : bid.parentBlockRoot = head.root
        · simp only [onHead, ne_eq, not_true_eq_false, ↓reduceIte, true_iff] at value
          obtain ⟨full, -, hash⟩ := value
          refine Or.inl ⟨onHead, ?_⟩
          cases full
          · exact Or.inr (by simpa using hash)
          · exact Or.inl (by simpa using hash)
        · simp [onHead] at value

/-- A valid bid passes the check of the head branch. -/
theorem isBidCompatibleWithHead_of_validateExecutionPayloadBid_eq_accept
    (valid : validateExecutionPayloadBid config checks seen store gloas signed currentTimeMs =
      .ok accept) :
    store.isBidCompatibleWithHead config gloas signed.message = .ok true := by
  cases branch : store.isBidCompatibleWithHead config gloas signed.message with
  | ok onHead =>
    cases onHead
    · simp only [validateExecutionPayloadBid, branch, bind, Except.bind, pure, Except.pure,
        Except.mapError, ignoreUnless_andThenM, rejectUnless_andThenM, Bool.false_eq_true,
        ↓reduceIte] at valid
      repeat' split at valid
      all_goals simp at valid
    · rfl
  | error e =>
    simp only [validateExecutionPayloadBid, branch, bind, Except.bind, pure, Except.pure,
      Except.mapError, ignoreUnless_andThenM, rejectUnless_andThenM] at valid
    repeat' split at valid
    all_goals simp at valid

/-- A valid bid builds on the head block, or on the parent of the head block.

On the head block, its parent payload is the head's own payload or the one the head builds on.

On the parent, its parent payload is the one that the head block builds on. -/
theorem exists_head_of_validateExecutionPayloadBid_eq_accept
    (valid : validateExecutionPayloadBid config checks seen store gloas signed currentTimeMs =
      .ok accept) :
    ∃ head headBlock, store.getHead config = .ok head ∧ store.blocks[head.root]? = some headBlock ∧
      (signed.message.parentBlockRoot = head.root ∧
          (signed.message.parentBlockHash =
              (headBlock.body.signedExecutionPayloadBid gloas).message.blockHash ∨
            signed.message.parentBlockHash =
              (headBlock.body.signedExecutionPayloadBid gloas).message.parentBlockHash) ∨
        signed.message.parentBlockRoot = headBlock.parentRoot ∧
          signed.message.parentBlockHash =
            (headBlock.body.signedExecutionPayloadBid gloas).message.parentBlockHash) :=
  exists_head_of_isBidCompatibleWithHead
    (isBidCompatibleWithHead_of_validateExecutionPayloadBid_eq_accept valid)

/-! ## The exit of the builder -/

/-- The answer of the check whether the parent payload of a bid asks a builder to exit.

A bid that does not build on the latest payload of the state gets the answer no.

A bid on that payload needs the envelope that the store keeps for its parent block.

The answer is then yes exactly when a request of that envelope has the builder's key and address.
-/
theorem builderMayExit_eq_ok_iff {state : BeaconState preset fork}
    {bid : ExecutionPayloadBid preset fork} {builder : Builder} {exiting : Bool} :
    builderMayExit store gloas state bid builder = .ok exiting ↔
      if bid.parentBlockHash = (state.latestExecutionPayloadBid gloas).blockHash then
        ∃ envelope, (store.payloads gloas)[bid.parentBlockRoot]? = some envelope ∧
          (exiting = true ↔
            ∃ request ∈ (envelope.executionRequests.builderExits gloas).data,
              request.pubkey = builder.pubkey ∧ request.sourceAddress = builder.executionAddress)
      else exiting = false := by
  unfold builderMayExit
  by_cases latest : bid.parentBlockHash = (state.latestExecutionPayloadBid gloas).blockHash
  · cases stored : (store.payloads gloas)[bid.parentBlockRoot]? with
    | none => simp [latest, throw, throwThe, MonadExceptOf.throw]
    | some envelope =>
      simp only [latest, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq, Option.some.injEq, exists_eq_left']
      cases exiting
      · simp only [Bool.false_eq_true, false_iff, Bool.eq_false_iff, ne_eq, List.any_eq_true,
          Bool.and_eq_true, beq_iff_eq, Array.mem_toList_iff]
      · simp only [true_iff, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Array.mem_toList_iff]
  · cases exiting <;> simp [latest, pure, Except.pure]

/-- The exit check fails exactly when it needs an envelope that the store lacks.

It needs one when the bid builds on the latest payload of the state.

The error then names the parent block of the bid as a payload not verified. -/
theorem builderMayExit_eq_error_iff {state : BeaconState preset fork}
    {bid : ExecutionPayloadBid preset fork} {builder : Builder} {e : ForkChoiceError} :
    builderMayExit store gloas state bid builder = .error e ↔
      bid.parentBlockHash = (state.latestExecutionPayloadBid gloas).blockHash ∧
        (store.payloads gloas)[bid.parentBlockRoot]? = none ∧
        e = .payloadNotVerified bid.parentBlockRoot := by
  unfold builderMayExit
  by_cases latest : bid.parentBlockHash = (state.latestExecutionPayloadBid gloas).blockHash
  · cases stored : (store.payloads gloas)[bid.parentBlockRoot]? with
    | none => simp [latest, throw, throwThe, MonadExceptOf.throw, eq_comm]
    | some envelope => simp [latest, pure, Except.pure]
  · simp [latest, pure, Except.pure]

/-- For a valid bid, the exit check answers no.

The check reads the state of the parent block, advanced to the slot of the bid.

The builder is the one at the index of the bid in that state.
-/
theorem builderMayExit_of_validateExecutionPayloadBid_eq_accept
    (valid : validateExecutionPayloadBid config checks seen store gloas signed currentTimeMs =
      .ok accept) :
    ∃ state advanced builder,
      store.blockStates[signed.message.parentBlockRoot]? = some state ∧
        processSlots config checks state signed.message.slot = .ok advanced ∧
        (advanced.builders gloas).data[signed.message.builderIndex.toNat]? = some builder ∧
        builderMayExit store gloas advanced signed.message builder = .ok false := by
  unfold validateExecutionPayloadBid at valid
  replace valid := (andThenM_eq_ok_accept.mp valid).2
  replace valid := (andThenM_eq_ok_accept.mp valid).2
  obtain ⟨_, -, valid⟩ := bind_ok_iff.mp valid
  replace valid := (andThenM_eq_ok_accept.mp valid).2
  replace valid := (andThenM_eq_ok_accept.mp valid).2
  replace valid := (andThenM_eq_ok_accept.mp valid).2
  replace valid := (andThenM_eq_ok_accept.mp valid).2
  cases known : store.blocks[signed.message.parentBlockRoot]? with
  | none => simp [known, pure, Except.pure] at valid
  | some _ =>
  simp only [known] at valid
  replace valid := (andThenM_eq_ok_accept.mp valid).2
  cases held : store.blockStates[signed.message.parentBlockRoot]? with
  | none => simp [held, pure, Except.pure] at valid
  | some state =>
  simp only [held] at valid
  obtain ⟨_, -, valid⟩ := bind_ok_iff.mp valid
  replace valid := (andThenM_eq_ok_accept.mp valid).2
  obtain ⟨dependentRoot, -, valid⟩ := bind_ok_iff.mp valid
  cases preferred : seen.proposerPreferencesFor (signed.message.slot, dependentRoot) with
  | none => simp [preferred, pure, Except.pure] at valid
  | some _ =>
  simp only [preferred] at valid
  replace valid := (andThenM_eq_ok_accept.mp valid).2
  cases payload : seen.executionPayloadGasLimitFor signed.message.parentBlockHash with
  | none => simp [payload, pure, Except.pure] at valid
  | some _ =>
  simp only [payload] at valid
  obtain ⟨_, -, valid⟩ := bind_ok_iff.mp valid
  replace valid := (andThenM_eq_ok_accept.mp valid).2
  obtain ⟨_, -, valid⟩ := bind_ok_iff.mp valid
  replace valid := (andThenM_eq_ok_accept.mp valid).2
  obtain ⟨_, -, valid⟩ := bind_ok_iff.mp valid
  replace valid := (andThenM_eq_ok_accept.mp valid).2
  obtain ⟨advanced, slots, valid⟩ := bind_ok_iff.mp valid
  replace slots : processSlots config checks state signed.message.slot = .ok advanced := by
    revert slots
    cases processSlots config checks state signed.message.slot <;> simp [Except.mapError]
  cases found : (advanced.builders gloas).data[signed.message.builderIndex.toNat]? with
  | none => simp [found, pure, Except.pure] at valid
  | some builder =>
  simp only [found] at valid
  replace valid := (andThenM_eq_ok_accept.mp valid).2
  obtain ⟨_, -, valid⟩ := bind_ok_iff.mp valid
  replace valid := (andThenM_eq_ok_accept.mp valid).2
  obtain ⟨_, -, valid⟩ := bind_ok_iff.mp valid
  replace valid := (andThenM_eq_ok_accept.mp valid).2
  obtain ⟨exiting, exit, valid⟩ := bind_ok_iff.mp valid
  have staying := (andThenM_eq_ok_accept.mp valid).1
  refine ⟨state, advanced, builder, rfl, slots, found, ?_⟩
  cases exiting
  · exact exit
  · simp at staying

/-- For a valid bid on the latest payload, the store holds the envelope of its parent block.

No exit request of that envelope has both the key and the address of its builder.

The state is that of the parent block at the slot of the bid, which the check reads. -/
theorem exists_envelope_of_validateExecutionPayloadBid_eq_accept
    (valid : validateExecutionPayloadBid config checks seen store gloas signed currentTimeMs =
      .ok accept) :
    ∃ state advanced builder,
      store.blockStates[signed.message.parentBlockRoot]? = some state ∧
        processSlots config checks state signed.message.slot = .ok advanced ∧
        (advanced.builders gloas).data[signed.message.builderIndex.toNat]? = some builder ∧
        (signed.message.parentBlockHash = (advanced.latestExecutionPayloadBid gloas).blockHash →
          ∃ envelope, (store.payloads gloas)[signed.message.parentBlockRoot]? = some envelope ∧
            ∀ request ∈ (envelope.executionRequests.builderExits gloas).data,
              request.pubkey = builder.pubkey →
                request.sourceAddress ≠ builder.executionAddress) := by
  obtain ⟨state, advanced, builder, held, slots, found, exit⟩ :=
    builderMayExit_of_validateExecutionPayloadBid_eq_accept valid
  refine ⟨state, advanced, builder, held, slots, found, fun latest => ?_⟩
  have value := builderMayExit_eq_ok_iff.mp exit
  rw [ite_eq_left_of_eq_true _ _ (eq_true latest)] at value
  obtain ⟨envelope, stored, exits⟩ := value
  refine ⟨envelope, stored, fun request mem key address => ?_⟩
  simpa using exits.mpr ⟨request, mem, key, address⟩

/-! ## The chain of checks -/

section Chain

variable {timely onHead compatible active covered exiting valid : Bool}
  {parent : BeaconBlock preset fork} {state advanced : BeaconState preset fork}
  {lookahead : Epoch} {dependentRoot : Root} {preferences : ProposerPreferences}
  {parentGasLimit : UInt64} {randao : Bytes32} {builder : Builder}
  {listCheck : ValidationResult}

/-- The outcome of a bid is its chain of checks, in order.

It holds once the clock, the parent block, its state, the lookahead and the dependent root are set.

The preferences, the parent gas limit and the head test must be fixed too.

So must the RANDAO mix, the advanced state, the builder and the tests on the builder. -/
theorem validateExecutionPayloadBid_eq
    (clock : store.isCurrentOrNextSlot config signed.message.slot currentTimeMs = .ok timely)
    (known : store.blocks[signed.message.parentBlockRoot]? = some parent)
    (held : store.blockStates[signed.message.parentBlockRoot]? = some state)
    (reach : addChecked (getCurrentEpoch state) preset.MIN_SEED_LOOKAHEAD = .ok lookahead)
    (dependent : store.getShufflingDependentRoot signed.message.parentBlockRoot
      (computeEpochAtSlot preset signed.message.slot) = .ok dependentRoot)
    (preferred : seen.proposerPreferencesFor (signed.message.slot, dependentRoot) =
      some preferences)
    (payload : seen.executionPayloadGasLimitFor signed.message.parentBlockHash =
      some parentGasLimit)
    (gas : isGasLimitTargetCompatible parentGasLimit signed.message.gasLimit
      preferences.targetGasLimit = .ok compatible)
    (branch : store.isBidCompatibleWithHead config gloas signed.message = .ok onHead)
    (mix : getRandaoMix state (getCurrentEpoch state) = .ok randao)
    (slots : processSlots config checks state signed.message.slot = .ok advanced)
    (found : (advanced.builders gloas).data[signed.message.builderIndex.toNat]? = some builder)
    (activity : isActiveBuilder advanced gloas signed.message.builderIndex = .ok active)
    (funds : canBuilderCoverBid advanced gloas signed.message.builderIndex signed.message.value =
      .ok covered)
    (exit : builderMayExit store gloas advanced signed.message builder = .ok exiting)
    (lists : bidInclusionListOutcome store advanced signed.message = .ok listCheck)
    (signature : verifyExecutionPayloadBidSignature config checks advanced gloas signed =
      .ok valid) :
    validateExecutionPayloadBid config checks seen store gloas signed currentTimeMs =
      .ok ((ignoreUnless (!seen.executionPayloadBids.contains (signed.message.slot,
            signed.message.parentBlockHash, signed.message.parentBlockRoot,
            signed.message.builderIndex))
          "already seen valid bid for this slot, parent, and builder").andThen fun _ =>
        (ignoreUnless ((seen.bestExecutionPayloadBidFor (signed.message.slot,
            signed.message.parentBlockHash, signed.message.parentBlockRoot)).all
            (· < signed.message.value))
          "bid is not the highest value bid seen for this slot and parent").andThen fun _ =>
        (ignoreUnless timely "bid's slot is not the current or next slot").andThen fun _ =>
        (rejectUnless (signed.message.executionPayment == 0)
          "bid's execution payment must be zero").andThen fun _ =>
        (rejectUnless (signed.message.blockHash != signed.message.parentBlockHash)
          "bid's block hash equals its parent block hash").andThen fun _ =>
        (rejectUnless (signed.message.blobKzgCommitments.data.size ≤
            (config.getBlobParameters
              (computeEpochAtSlot preset signed.message.slot)).maxBlobsPerBlock.toNat)
          "too many blob kzg commitments").andThen fun _ =>
        (rejectUnless (parent.slot < signed.message.slot)
          "bid's slot is not higher than its parent's slot").andThen fun _ =>
        (ignoreUnless (computeEpochAtSlot preset signed.message.slot ≤ lookahead)
          "bid's slot is past the parent's proposer lookahead").andThen fun _ =>
        (ignoreUnless (signed.message.feeRecipient == preferences.feeRecipient)
          "bid's fee recipient does not match the proposer's preference").andThen fun _ =>
        (ignoreUnless compatible
          "bid's gas limit is not compatible with the proposer's target").andThen fun _ =>
        (ignoreUnless onHead "bid is not compatible with the current head branch").andThen
          fun _ =>
        (rejectUnless (signed.message.prevRandao == randao)
          "bid's previous randao is incorrect").andThen fun _ =>
        (rejectUnless (builder.version == PAYLOAD_BUILDER_VERSION)
          "builder is not a payload builder").andThen fun _ =>
        (rejectUnless active "builder is not active").andThen fun _ =>
        (ignoreUnless covered "builder cannot cover bid value").andThen fun _ =>
        (ignoreUnless (!exiting) "builder may exit").andThen fun _ =>
        listCheck.andThen fun _ =>
        rejectUnless valid "invalid bid signature") := by
  unfold validateExecutionPayloadBid
  simp only [clock, known, held, reach, dependent, preferred, payload, gas, branch, mix, slots,
    found, activity, funds, exit, lists, signature, bind, Except.bind, pure, Except.pure,
    Except.mapError, ignoreUnless_andThenM, ignoreUnless_andThen, rejectUnless_andThenM,
    rejectUnless_andThen, apply_ite (Except.ok (ε := ForkChoiceError))]
  cases listCheck <;> simp only [ValidationResult.andThenM, ValidationResult.andThen, pure,
    Except.pure]

/-- Once its inputs are computed, a bid is valid exactly when every check passes. -/
theorem validateExecutionPayloadBid_eq_accept
    (clock : store.isCurrentOrNextSlot config signed.message.slot currentTimeMs = .ok timely)
    (known : store.blocks[signed.message.parentBlockRoot]? = some parent)
    (held : store.blockStates[signed.message.parentBlockRoot]? = some state)
    (reach : addChecked (getCurrentEpoch state) preset.MIN_SEED_LOOKAHEAD = .ok lookahead)
    (dependent : store.getShufflingDependentRoot signed.message.parentBlockRoot
      (computeEpochAtSlot preset signed.message.slot) = .ok dependentRoot)
    (preferred : seen.proposerPreferencesFor (signed.message.slot, dependentRoot) =
      some preferences)
    (payload : seen.executionPayloadGasLimitFor signed.message.parentBlockHash =
      some parentGasLimit)
    (gas : isGasLimitTargetCompatible parentGasLimit signed.message.gasLimit
      preferences.targetGasLimit = .ok compatible)
    (branch : store.isBidCompatibleWithHead config gloas signed.message = .ok onHead)
    (mix : getRandaoMix state (getCurrentEpoch state) = .ok randao)
    (slots : processSlots config checks state signed.message.slot = .ok advanced)
    (found : (advanced.builders gloas).data[signed.message.builderIndex.toNat]? = some builder)
    (activity : isActiveBuilder advanced gloas signed.message.builderIndex = .ok active)
    (funds : canBuilderCoverBid advanced gloas signed.message.builderIndex signed.message.value =
      .ok covered)
    (exit : builderMayExit store gloas advanced signed.message builder = .ok exiting)
    (lists : bidInclusionListOutcome store advanced signed.message = .ok listCheck)
    (signature : verifyExecutionPayloadBidSignature config checks advanced gloas signed =
      .ok valid) :
    validateExecutionPayloadBid config checks seen store gloas signed currentTimeMs = .ok accept ↔
      (signed.message.slot, signed.message.parentBlockHash, signed.message.parentBlockRoot,
          signed.message.builderIndex) ∉ seen.executionPayloadBids ∧
        (seen.bestExecutionPayloadBidFor (signed.message.slot, signed.message.parentBlockHash,
          signed.message.parentBlockRoot)).all (· < signed.message.value) = true ∧
        timely = true ∧ signed.message.executionPayment = 0 ∧
        signed.message.blockHash ≠ signed.message.parentBlockHash ∧
        signed.message.blobKzgCommitments.data.size ≤
          (config.getBlobParameters
            (computeEpochAtSlot preset signed.message.slot)).maxBlobsPerBlock.toNat ∧
        parent.slot < signed.message.slot ∧
        computeEpochAtSlot preset signed.message.slot ≤ lookahead ∧
        signed.message.feeRecipient = preferences.feeRecipient ∧ compatible = true ∧
        onHead = true ∧ signed.message.prevRandao = randao ∧
        builder.version = PAYLOAD_BUILDER_VERSION ∧ active = true ∧ covered = true ∧
        exiting = false ∧ listCheck = accept ∧ valid = true := by
  rw [validateExecutionPayloadBid_eq clock known held reach dependent preferred payload gas branch
    mix slots found activity funds exit lists signature]
  simp only [Except.ok.injEq, andThen_eq_accept, ignoreUnless_eq_accept, rejectUnless_eq_accept]
  simp

/-- Once its inputs are computed, a bid is ignored only when an ignore check fails. -/
theorem validateExecutionPayloadBid_ignored {reason : String}
    (clock : store.isCurrentOrNextSlot config signed.message.slot currentTimeMs = .ok timely)
    (known : store.blocks[signed.message.parentBlockRoot]? = some parent)
    (held : store.blockStates[signed.message.parentBlockRoot]? = some state)
    (reach : addChecked (getCurrentEpoch state) preset.MIN_SEED_LOOKAHEAD = .ok lookahead)
    (dependent : store.getShufflingDependentRoot signed.message.parentBlockRoot
      (computeEpochAtSlot preset signed.message.slot) = .ok dependentRoot)
    (preferred : seen.proposerPreferencesFor (signed.message.slot, dependentRoot) =
      some preferences)
    (payload : seen.executionPayloadGasLimitFor signed.message.parentBlockHash =
      some parentGasLimit)
    (gas : isGasLimitTargetCompatible parentGasLimit signed.message.gasLimit
      preferences.targetGasLimit = .ok compatible)
    (branch : store.isBidCompatibleWithHead config gloas signed.message = .ok onHead)
    (mix : getRandaoMix state (getCurrentEpoch state) = .ok randao)
    (slots : processSlots config checks state signed.message.slot = .ok advanced)
    (found : (advanced.builders gloas).data[signed.message.builderIndex.toNat]? = some builder)
    (activity : isActiveBuilder advanced gloas signed.message.builderIndex = .ok active)
    (funds : canBuilderCoverBid advanced gloas signed.message.builderIndex signed.message.value =
      .ok covered)
    (exit : builderMayExit store gloas advanced signed.message builder = .ok exiting)
    (lists : bidInclusionListOutcome store advanced signed.message = .ok listCheck)
    (signature : verifyExecutionPayloadBidSignature config checks advanced gloas signed =
      .ok valid)
    (ignored : validateExecutionPayloadBid config checks seen store gloas signed currentTimeMs =
      .ok (.ignore reason)) :
    (signed.message.slot, signed.message.parentBlockHash, signed.message.parentBlockRoot,
          signed.message.builderIndex) ∈ seen.executionPayloadBids ∨
        (seen.bestExecutionPayloadBidFor (signed.message.slot, signed.message.parentBlockHash,
          signed.message.parentBlockRoot)).all (· < signed.message.value) = false ∨
        timely = false ∨ lookahead < computeEpochAtSlot preset signed.message.slot ∨
        signed.message.feeRecipient ≠ preferences.feeRecipient ∨ compatible = false ∨
        onHead = false ∨ covered = false ∨ exiting = true ∨
        ∃ reason, listCheck = .ignore reason := by
  rw [validateExecutionPayloadBid_eq clock known held reach dependent preferred payload gas branch
    mix slots found activity funds exit lists signature] at ignored
  refine Classical.byContradiction fun none => ?_
  simp only [not_or, Bool.not_eq_false, Bool.not_eq_true, ne_eq, Decidable.not_not,
    UInt64.not_lt] at none
  obtain ⟨fresh, best, current, inside, fee, gasOk, branchOk, coveredOk, staying, noIgnore⟩ :=
    none
  simp only [Except.ok.injEq, ignoreUnless_andThen, rejectUnless_andThen, best, current,
    inside, fee, gasOk, branchOk, coveredOk, staying, beq_self_eq_true, decide_true, Bool.not_false,
    Bool.not_eq_true', ite_true] at ignored
  repeat' split at ignored
  all_goals cases valid <;> cases listCheck <;> simp_all [ValidationResult.andThen, rejectUnless]

end Chain

end EthLib.Consensus
