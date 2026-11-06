module

public import EthLib.Base.Proofs.MapM
public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Consensus.Proofs.Mutators
public import EthLib.Consensus.Transition.Block

/-!
# Proofs: the first steps of a block

Each step keeps the number of validators and the number of balances.

The header step stores the header of the block, and the RANDAO and vote steps change one field.

A valid proposer slashing slashes its proposer.

A valid attester slashing slashes a validator that signed both attestations.

Casper FFG never forbids a vote together with itself.

A valid indexed attestation has strictly increasing indices.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz SszType

variable {preset : Preset} {fork : Base.Fork}

/-- The constructor index that a code names, so that codes are read back in one pass. -/
private def ctorIdxOfCode : UInt32 → Nat
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | 5 => 4
  | 6 => 5
  | 7 => 6
  | 8 => 7
  | 9 => 8
  | 10 => 9
  | 11 => 10
  | 12 => 11
  | 13 => 12
  | 14 => 13
  | 15 => 14
  | 16 => 15
  | 17 => 16
  | 18 => 17
  | 19 => 18
  | 20 => 19
  | 21 => 20
  | 22 => 21
  | 23 => 22
  | 24 => 23
  | 25 => 24
  | 26 => 25
  | 27 => 26
  | 28 => 27
  | 29 => 28
  | 30 => 29
  | 31 => 30
  | 32 => 31
  | 33 => 32
  | 34 => 33
  | 35 => 34
  | 36 => 35
  | 37 => 36
  | 38 => 37
  | 39 => 38
  | 40 => 39
  | 41 => 40
  | 42 => 41
  | 43 => 42
  | 44 => 43
  | 45 => 44
  | 46 => 45
  | 47 => 46
  | 48 => 47
  | 49 => 48
  | 50 => 49
  | 51 => 50
  | 61 => 51
  | 62 => 52
  | 63 => 53
  | 64 => 54
  | 65 => 55
  | 52 => 56
  | 53 => 57
  | 54 => 58
  | 55 => 59
  | 66 => 60
  | 67 => 61
  | 68 => 62
  | 69 => 63
  | 70 => 64
  | 71 => 65
  | 72 => 66
  | 73 => 67
  | 74 => 68
  | 75 => 69
  | 76 => 70
  | 77 => 71
  | _ => 0

/-- Two errors with one code come from one constructor. -/
theorem TransitionError.code_injective (e₁ e₂ : TransitionError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Each code names the index of its constructor, so the code determines the index.
  have back : ∀ e : TransitionError, ctorIdxOfCode e.code = e.ctorIdx := by
    intro e
    cases e <;> rfl
  rw [← back e₁, ← back e₂, h]

theorem liftAccessor_ok {α : Type} {result : Except AccessorError α} {value : α} :
    liftAccessor result = .ok value ↔ result = .ok value :=
  mapError_ok_iff

theorem liftSsz_ok {α : Type} {result : Except Err α} {value : α} :
    liftSsz result = .ok value ↔ result = .ok value :=
  mapError_ok_iff

/-! ## The block header -/

/-- A valid block is at the slot of the state, after the latest block, and from its proposer.

Its parent is the latest block, and its proposer is not slashed. -/
theorem processBlockHeader_checks {state after : BeaconState preset fork}
    {block : BeaconBlock preset fork} (computed : processBlockHeader state block = .ok after) :
    block.slot = state.slot ∧ state.latestBlockHeader.slot < block.slot ∧
      getBeaconProposerIndex state = .ok block.proposerIndex ∧
      hashTreeRoot state.latestBlockHeader = .ok block.parentRoot ∧
      ∃ proposer, getValidator state block.proposerIndex = .ok proposer ∧
        proposer.slashed = false := by
  simp only [processBlockHeader, bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok, pure,
    Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, slot, _, newer, _, proposer, _, same, _, parent, _, parentSame, _, _, validator,
    found, _, notSlashed, _⟩ := computed
  subst same parentSame
  exact ⟨slot, newer, proposer, parent, validator, found, notSlashed⟩

/-- The header step stores the header of the block, with a zero state root, and nothing else. -/
theorem processBlockHeader_eq {state after : BeaconState preset fork}
    {block : BeaconBlock preset fork} (computed : processBlockHeader state block = .ok after) :
    ∃ bodyRoot, hashTreeRoot block.body = .ok bodyRoot ∧
      after = { state with
        latestBlockHeader :=
          { slot := block.slot, proposerIndex := block.proposerIndex,
            parentRoot := block.parentRoot, stateRoot := Vector.replicate 32 0, bodyRoot } } := by
  simp only [processBlockHeader, bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok, pure,
    Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, bodyRoot, body, _, _, _, _, stored⟩ := computed
  exact ⟨bodyRoot, body, stored.symm⟩

theorem sameSizes_processBlockHeader {state after : BeaconState preset fork}
    {block : BeaconBlock preset fork} (computed : processBlockHeader state block = .ok after) :
    SameSizes state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact SameSizes.refl state

/-! ## RANDAO -/

/-- The RANDAO step checks that the reveal is the proposer's signature of the current epoch.

It then mixes the hash of the reveal into the mix of the epoch, and changes nothing else. -/
theorem processRandao_eq {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) :
    ∃ index proposer domain signingRoot mix,
      getBeaconProposerIndex state = .ok index ∧ getValidator state index = .ok proposer ∧
      getDomain config state DOMAIN_RANDAO = .ok domain ∧
      computeSigningRoot (getCurrentEpoch state) domain = .ok signingRoot ∧
      checks.verify (packBytes proposer.pubkey) (packBytes signingRoot)
        (packBytes body.randaoReveal) = true ∧
      getRandaoMix state (getCurrentEpoch state) = .ok mix ∧
      after = { state with
        randaoMixes := state.randaoMixes.set!
          (getCurrentEpoch state % preset.EPOCHS_PER_HISTORICAL_VECTOR).toNat
          (Vector.zipWith (· ^^^ ·) mix (sha256Bytes32 (packBytes body.randaoReveal))) } := by
  simp only [processRandao, bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok, pure,
    Except.pure, Except.ok.injEq] at computed
  obtain ⟨index, indexOk, proposer, found, domain, domainOk, signingRoot, rootOk, _, verified, mix,
    mixOk, stored⟩ := computed
  exact ⟨index, proposer, domain, signingRoot, mix, indexOk, found, domainOk, rootOk, verified,
    mixOk, stored.symm⟩

theorem sameSizes_processRandao {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) : SameSizes state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact SameSizes.refl state

/-! ## Votes on the deposit contract -/

/-- The vote step appends the vote.

It adopts the vote once more than half the slots of the period cast it.

It changes nothing else. -/
theorem processEth1Data_eq {before : fork < .hegota} {state after : BeaconState preset fork}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) :
    (after.eth1DataVotes before).data =
        (state.eth1DataVotes before).data.push (body.eth1Data before) ∧
      after.eth1Data before =
        (if preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * preset.SLOTS_PER_EPOCH.toNat <
            ((state.eth1DataVotes before).data.push (body.eth1Data before)).count
              (body.eth1Data before) * 2
          then body.eth1Data before else state.eth1Data before) ∧
      { after with eth1DataVotes := state.eth1DataVotes, eth1Data := state.eth1Data } = state := by
  simp only [processEth1Data] at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
      mulChecked_ok_iff] at computed
    obtain ⟨slots, ⟨_, product⟩, computed⟩ := computed
    rw [product] at computed
    split at computed <;>
      · simp only [pure, Except.pure, Except.ok.injEq] at computed
        subst computed
        simp_all
        try (intro; omega)
  · simp [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at computed

theorem sameSizes_processEth1Data {before : fork < .hegota}
    {state after : BeaconState preset fork} {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) :
    SameSizes state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  rw [← rest]
  exact SameSizes.refl after

/-! ## Slashable votes and indexed attestations -/

/-- Casper FFG never forbids a vote together with itself. -/
theorem isSlashableAttestationData_self (data : AttestationData) :
    isSlashableAttestationData data data = false := by
  simp [isSlashableAttestationData]

/-- Two different votes for one target epoch are a double vote. -/
theorem isSlashableAttestationData_of_double {data1 data2 : AttestationData}
    (distinct : data1 ≠ data2) (sameTarget : data1.target.epoch = data2.target.epoch) :
    isSlashableAttestationData data1 data2 = true := by
  simp [isSlashableAttestationData, distinct, sameTarget]

/-- A vote whose source and target lie strictly around those of another is a surround vote. -/
theorem isSlashableAttestationData_of_surround {data1 data2 : AttestationData}
    (source : data1.source.epoch < data2.source.epoch)
    (target : data2.target.epoch < data1.target.epoch) :
    isSlashableAttestationData data1 data2 = true := by
  simp [isSlashableAttestationData, source, target]

/-- A valid indexed attestation has nonempty, strictly increasing indices.

From Gloas there are at most as many as one slot can hold. -/
theorem isValidIndexedAttestation_indices {config : Config} {checks : SignatureChecks}
    {state : BeaconState preset fork} {attestation : IndexedAttestation preset fork}
    (valid : isValidIndexedAttestation config checks state attestation = .ok true) :
    attestation.attestingIndices.data.toList ≠ [] ∧
      attestation.attestingIndices.data.toList.Pairwise (· < ·) ∧
      (.glamsterdam ≤ fork →
        attestation.attestingIndices.data.toList.length ≤ maxAttesters preset fork) := by
  simp only [isValidIndexedAttestation] at valid
  split at valid
  · simp [pure, Except.pure] at valid
  · rename_i accepted
    simp only [not_or, not_and, Nat.not_lt, Decidable.not_not] at accepted
    obtain ⟨nonempty, sorted, bounded⟩ := accepted
    exact ⟨nonempty, sorted ▸ sortedSet_sorted _, bounded⟩

/-- A valid indexed attestation carries the aggregate signature of its validators on its data. -/
theorem isValidIndexedAttestation_signature {config : Config} {checks : SignatureChecks}
    {state : BeaconState preset fork} {attestation : IndexedAttestation preset fork}
    (valid : isValidIndexedAttestation config checks state attestation = .ok true) :
    ∃ pubkeys domain signingRoot,
      attestation.attestingIndices.data.toList.toArray.mapM
          (fun index => do return packBytes (← liftAccessor (getValidator state index)).pubkey) =
        .ok pubkeys ∧
      getDomain config state DOMAIN_BEACON_ATTESTER (some attestation.data.target.epoch) =
        .ok domain ∧
      computeSigningRoot attestation.data domain = .ok signingRoot ∧
      checks.fastAggregateVerify pubkeys (packBytes signingRoot)
        (packBytes attestation.signature) = true := by
  simp only [isValidIndexedAttestation] at valid
  split at valid
  · simp [pure, Except.pure] at valid
  · simp only [bind_ok_iff, liftAccessor_ok, liftSsz_ok, pure, Except.pure,
      Except.ok.injEq] at valid
    obtain ⟨pubkeys, pubkeysOk, domain, domainOk, signingRoot, rootOk, verified⟩ := valid
    exact ⟨pubkeys, domain, signingRoot, pubkeysOk, domainOk, rootOk, verified⟩

/-! ## Proposer slashings -/

/-- A header signature passes when the key signs the header in the epoch of its slot. -/
theorem checkHeaderSignature_ok {config : Config} {checks : SignatureChecks}
    {state : BeaconState preset fork} {pubkey : BLSPubkey} {signed : SignedBeaconBlockHeader}
    {u : Unit} (computed : checkHeaderSignature config checks state pubkey signed = .ok u) :
    ∃ domain signingRoot,
      getDomain config state DOMAIN_BEACON_PROPOSER
          (some (computeEpochAtSlot preset signed.message.slot)) = .ok domain ∧
      computeSigningRoot signed.message domain = .ok signingRoot ∧
      checks.verify (packBytes pubkey) (packBytes signingRoot) (packBytes signed.signature) =
        true := by
  simp only [checkHeaderSignature, bind_ok_iff, ensure_ok_iff, liftAccessor_ok,
    liftSsz_ok] at computed
  obtain ⟨domain, domainOk, signingRoot, rootOk, verified⟩ := computed
  exact ⟨domain, signingRoot, domainOk, rootOk, verified⟩

/-- A valid proposer slashing holds two different headers of one slot and one proposer.

The proposer is slashable in the current epoch, and signed both headers. -/
theorem processProposerSlashing_checks {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    slashing.signedHeader1.message.slot = slashing.signedHeader2.message.slot ∧
      slashing.signedHeader1.message.proposerIndex =
        slashing.signedHeader2.message.proposerIndex ∧
      slashing.signedHeader1.message ≠ slashing.signedHeader2.message ∧
      ∃ proposer, getValidator state slashing.signedHeader1.message.proposerIndex = .ok proposer ∧
        isSlashableValidator proposer (getCurrentEpoch state) = true ∧
        checkHeaderSignature config checks state proposer.pubkey slashing.signedHeader1 =
          .ok () ∧
        checkHeaderSignature config checks state proposer.pubkey slashing.signedHeader2 =
          .ok () := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, slot, _, index, _, distinct, proposer, found, _, slashable, _, first, _, second,
    _⟩ := computed
  exact ⟨slot, index, distinct, proposer, found, slashable, first, second⟩

/-- A valid proposer slashing slashes its proposer. -/
theorem processProposerSlashing_slashed {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    slashedFlag after slashing.signedHeader1.message.proposerIndex = .ok true := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact (slashValidator_slashedFlag slashed).1

theorem sameSizes_processProposerSlashing {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    SameSizes state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact sameSizes_slashValidator slashed

/-! ## Attester slashings -/

/-- A step of an attester slashing keeps the sizes, and keeps every slashed flag that is set.

The flag it returns is set only if it was set, or if the step slashed its validator. -/
theorem slashIfSlashable_ok {config : Config} {step after : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok after) :
    SameSizes step.1 after.1 ∧
      (∀ other, slashedFlag step.1 other = .ok true → slashedFlag after.1 other = .ok true) ∧
      (after.2 = true → step.2 = true ∨ slashedFlag after.1 index = .ok true) := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨slashedState, slashed, rfl⟩ := computed
    obtain ⟨flag, others⟩ := slashValidator_slashedFlag slashed
    refine ⟨sameSizes_slashValidator slashed, fun other set => ?_, fun _ => .inr flag⟩
    by_cases same : other = index
    · exact same ▸ flag
    · exact (others other same).trans set
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨SameSizes.refl _, fun _ set => set, .inl⟩

/-- The steps of an attester slashing over some indices keep the sizes and every set flag.

The flag they return is set only if it was set, or if they slashed one of the indices. -/
theorem foldlM_slashIfSlashable {config : Config} (indices : List ValidatorIndex) :
    ∀ {step after : BeaconState preset fork × Bool},
      indices.foldlM (slashIfSlashable config) step = .ok after →
      SameSizes step.1 after.1 ∧
        (∀ other, slashedFlag step.1 other = .ok true → slashedFlag after.1 other = .ok true) ∧
        (after.2 = true → step.2 = true ∨
          ∃ index ∈ indices, slashedFlag after.1 index = .ok true) := by
  induction indices with
  | nil =>
    intro step after computed
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨SameSizes.refl _, fun _ set => set, .inl⟩
  | cons first rest ih =>
    intro step after computed
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, firstOk, restOk⟩ := computed
    obtain ⟨sizes, kept, flagged⟩ := slashIfSlashable_ok firstOk
    obtain ⟨restSizes, restKept, restFlagged⟩ := ih restOk
    refine ⟨sizes.trans restSizes, fun other set => restKept other (kept other set),
      fun done => ?_⟩
    rcases restFlagged done with middleFlag | ⟨index, member, flag⟩
    · rcases flagged middleFlag with stepFlag | flag
      · exact .inl stepFlag
      · exact .inr ⟨first, List.mem_cons_self, restKept first flag⟩
    · exact .inr ⟨index, List.mem_cons_of_mem first member, flag⟩

/-- A valid attester slashing holds two valid attestations that Casper FFG forbids together. -/
theorem processAttesterSlashing_checks {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    isSlashableAttestationData slashing.attestation1.data slashing.attestation2.data = true ∧
      isValidIndexedAttestation config checks state slashing.attestation1 = .ok true ∧
      isValidIndexedAttestation config checks state slashing.attestation2 = .ok true := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, slashable, valid1, first, _, valid1True, valid2, second, _, valid2True, _⟩ := computed
  subst valid1True valid2True
  exact ⟨slashable, first, second⟩

/-- A valid attester slashing slashes a validator that signed both attestations. -/
theorem processAttesterSlashing_slashed {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    ∃ index, index ∈ slashing.attestation1.attestingIndices.data.toList ∧
      index ∈ slashing.attestation2.attestingIndices.data.toList ∧
      slashedFlag after index = .ok true := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨folded, slashedAny⟩, foldOk, computed⟩ := computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, done, rfl⟩ := computed
  obtain ⟨_, _, flagged⟩ := foldlM_slashIfSlashable _ foldOk
  rcases flagged done with never | ⟨index, member, flag⟩
  · cases never
  · rw [slashingIndices, mem_sortedSet, List.mem_filter, decide_eq_true_iff] at member
    exact ⟨index, member.1, member.2, flag⟩

theorem sameSizes_processAttesterSlashing {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    SameSizes state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨folded, slashedAny⟩, foldOk, computed⟩ := computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact (foldlM_slashIfSlashable _ foldOk).1

end EthLib.Consensus
