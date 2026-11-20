module

public import EthLib.Consensus.Proofs.DirectSafety.Safety
public import EthLib.Consensus.Proofs.Transition.ForkVersions
public import EthLib.Consensus.Proofs.SignatureChecks

/-!
# Signatures of the accountable keys of direct safety

Two runs share a run from genesis to a state `x`, then split into two tails.

For each accountable key, the runs executed two accepted checks on conflicting objects.

A check that accepted says nothing about who signed, unless an assumption links the two.

The two assumptions here cover only the accepted signature checks that blocks of the runs made.

For the relation of real signatures, they say that none of those checks accepted a forgery.

Under them, each accountable key signed the signing roots of two conflicting objects.

They are two attestation data that the test of slashable votes flags, in attester domains.

Or they are two different headers of one slot, in proposer domains.

The proposer index of the two headers holds the key in the registry at `x`.

Each domain is that of the genesis validators root of the runs and of a version of the config.

The states of the runs hold only such versions, so their checks read no other.

The two headers are signed under the version of one fork.

Two runs that finalize conflicting checkpoints meet the bound of direct accountable safety.

So the keys that signed such a pair hold at least a third of the unslashed active stake at `x`.

Two thirds of the larger drift of the two tails are subtracted from that third.

When the unslashed active keys stay those of `x` on both tails, the drift is zero.

Otherwise the hashes of the runs show evidence.

These theorems do not show that a block of either run could include a slashing of those keys.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- A step of a chain keeps the genesis validators root.

A slot keeps it, each upgrade that the slot reaches keeps it, and a block keeps it. -/
theorem genesisValidatorsRoot_chainStep {x y : ForkedBeaconState preset}
    (step : ChainStep config checks x y) :
    y.state.genesisValidatorsRoot = x.state.genesisValidatorsRoot := by
  cases step with
  | slot computed =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
    refine processUpgrades_induction_due
      (property := fun forked => forked.state.genesisValidatorsRoot =
        x.state.genesisValidatorsRoot)
      (fun _ holds stepOk => (upgradeFrame_upgradeNext stepOk).genesisValidatorsRoot.trans holds)
      ?_ upgraded
    exact (advanceSlot_kept advancedOk).2.1
  | block engine signed _ computed =>
    obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok computed
    exact (frame_processBlock blockOk).genesisValidatorsRoot

/-- A run keeps the genesis validators root of its first state. -/
theorem _root_.EthLib.Consensus.Run.genesisValidatorsRoot {g a : ForkedBeaconState preset}
    (run : Run config checks g a) :
    a.state.genesisValidatorsRoot = g.state.genesisValidatorsRoot := by
  induction run with
  | nil => rfl
  | snoc _ step ih => exact (genesisValidatorsRoot_chainStep step.chainStep).trans ih

/-- A run from a genesis of deposits reaches only states that hold versions of the config. -/
theorem _root_.EthLib.Consensus.Run.forkVersions_ofConfig {g a : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (run : Run config checks g a) :
    a.state.forkVersions.OfConfig config := by
  obtain ⟨hash, time, deposits, initialized⟩ := genesis
  exact forkVersions_ofConfig_of_genesis_chainSteps initialized run.chainSteps

/-- The state before a block of the run has the genesis validators root of the run. -/
theorem CheckSite.genesisValidatorsRoot {g a : ForkedBeaconState preset}
    {run : Run config checks g a} (site : CheckSite run) :
    site.before.genesisValidatorsRoot = g.state.genesisValidatorsRoot := by
  obtain ⟨pre, -, -⟩ := run.contains_split _ site.member
  exact pre.genesisValidatorsRoot

/-- The aggregate calls of the accepted checks of indexed attestations that blocks of the run made.

Each call holds the keys that the check read, its signing root as bytes, and the signature. -/
def aggregateCalls {g a : ForkedBeaconState preset} (run : Run config checks g a) :
    Set (Array BLSPubkey × ByteArray × BLSSignature) :=
  {call | ∃ key, ∃ c : AttestationCheck run key, ∃ domain root,
    (c.indexed.attestingIndices.data.toList.toArray.mapM fun index => do
        return (← liftAccessor (getValidator c.checked index)).pubkey) = .ok call.1 ∧
      getDomain config c.checked DOMAIN_BEACON_ATTESTER (some c.indexed.data.target.epoch) =
        .ok domain ∧
      computeSigningRoot c.indexed.data domain = .ok root ∧
      call.2 = (packBytes root, c.indexed.signature)}

/-- The calls of the accepted checks of slashed headers that blocks of the run made.

Each call holds the key of the proposer, the signing root of a header as bytes, and its signature.

Each proposer slashing gives two calls, one for each of its headers. -/
def verifyCalls {g a : ForkedBeaconState preset} (run : Run config checks g a) :
    Set (BLSPubkey × ByteArray × BLSSignature) :=
  {call | ∃ key, ∃ c : HeaderCheck run key,
    ∃ header ∈ [c.slashing.signedHeader1, c.slashing.signedHeader2], ∃ domain root,
      getDomain config c.checked DOMAIN_BEACON_PROPOSER
          (some (computeEpochAtSlot preset header.message.slot)) = .ok domain ∧
        computeSigningRoot header.message domain = .ok root ∧
        call = (key, packBytes root, header.signature)}

/-- `key` signed the signing root of `object`, in a domain of the given type and version.

The domain is that of the given genesis validators root and of the given fork version. -/
def SignedIn (config : Config) (genesisRoot : Root) (signed : BLSPubkey → ByteArray → Prop)
    (key : BLSPubkey) (domainType : DomainType) (version : Version) {α : Type} [SszType α]
    (object : α) : Prop :=
  ∃ domain root,
    computeDomain config domainType version genesisRoot = .ok domain ∧
      computeSigningRoot object domain = .ok root ∧ signed key (packBytes root)

/-- `key` signed the signing roots of two conflicting objects.

They are two attestation data that the test of slashable votes flags, each in an attester domain.

Or they are two different headers of one slot, each in a proposer domain.

Their proposer index holds `key` in the registry of the reference state.

Each domain is that of the given genesis validators root and of the version of a fork of the config.

The two attestation data may take two forks, and the two headers take one.

If SHA-256 collides on the two roots, the two signatures may be one. -/
def SignedConflict (config : Config) (genesisRoot : Root) (reference : ForkedBeaconState preset)
    (signed : BLSPubkey → ByteArray → Prop) (key : BLSPubkey) : Prop :=
  (∃ (d₁ d₂ : AttestationData) (f₁ f₂ : Fork), isSlashableAttestationData d₁ d₂ = true ∧
      SignedIn config genesisRoot signed key DOMAIN_BEACON_ATTESTER (config.forkVersion f₁) d₁ ∧
      SignedIn config genesisRoot signed key DOMAIN_BEACON_ATTESTER (config.forkVersion f₂) d₂) ∨
    ∃ (h₁ h₂ : BeaconBlockHeader) (f : Fork), h₁.slot = h₂.slot ∧
      h₁.proposerIndex = h₂.proposerIndex ∧ h₁ ≠ h₂ ∧
      (∃ v, reference.state.validators.data[h₁.proposerIndex.toNat]? = some v ∧
        v.pubkey = key) ∧
      SignedIn config genesisRoot signed key DOMAIN_BEACON_PROPOSER (config.forkVersion f) h₁ ∧
      SignedIn config genesisRoot signed key DOMAIN_BEACON_PROPOSER (config.forkVersion f) h₂

/-- An accepted check of an indexed attestation that names `key` is a signature by `key`.

The key signed the signing root of the data, in the attester domain of the run.

The version is the one that the state before the block reads at the target epoch of the data.

This needs the assumption on the aggregate calls of the run. -/
theorem AttestationCheck.signedIn {g a : ForkedBeaconState preset} {run : Run config checks g a}
    {key : BLSPubkey} (c : AttestationCheck run key) {signed : BLSPubkey → ByteArray → Prop}
    (sound : checks.AggregateSoundOn (· ∈ aggregateCalls run) signed) :
    SignedIn config g.state.genesisValidatorsRoot signed key DOMAIN_BEACON_ATTESTER
      (c.before.forkVersions.versionAt c.indexed.data.target.epoch) c.indexed.data := by
  obtain ⟨pubkeys, domain, root, keysOk, domainOk, rootOk, verified⟩ :=
    isValidIndexedAttestation_signature c.valid
  -- The call is one of the aggregate calls of the run.
  have call : (pubkeys, packBytes root, c.indexed.signature) ∈ aggregateCalls run :=
    ⟨key, c, domain, root, keysOk, domainOk, rootOk, rfl⟩
  obtain ⟨i, member, v, found, rfl⟩ := c.signer
  -- The aggregate reads the key of each of its indices, so it holds the key of `i`.
  have holds : v.pubkey ∈ pubkeys := by
    simp only [bind_pure_comp, Array.mapM_eq_mapM_toList] at keysOk
    cases mapped : (c.indexed.attestingIndices.data.toList.mapM fun index =>
        Validator.pubkey <$> liftAccessor (getValidator c.checked index)) with
    | error e =>
      rw [mapped] at keysOk
      cases keysOk
    | ok ys =>
      rw [mapped] at keysOk
      simp only [Functor.map, Except.map, Except.ok.injEq] at keysOk
      subst keysOk
      obtain ⟨y, mem, read⟩ := exists_mem_of_mapM_ok mapped member
      simp [getValidator, found, liftAccessor, Except.mapError, Functor.map, Except.map] at read
      subst read
      simpa using mem
  -- The checked state follows the state before the block, so it keeps its genesis root.
  have rooted : c.checked.genesisValidatorsRoot = g.state.genesisValidatorsRoot :=
    (c.site.frame.genesisValidatorsRoot.trans
      (frame_operationsInput c.started).genesisValidatorsRoot).trans
      c.toCheckSite.genesisValidatorsRoot
  -- The checked state keeps the fork versions of the state before the block.
  have versions : c.checked.forkVersions = c.before.forkVersions :=
    c.site.frame.forkVersions.trans (frame_operationsInput c.started).forkVersions
  -- The domain is that of the genesis root of the checked state and of one of its versions.
  simp only [getDomain, Option.getD_some, mapError_ok_iff, rooted, versions] at domainOk
  exact ⟨domain, root, domainOk, rootOk, sound _ _ _ call verified _ holds⟩

/-- Both headers of a checked proposer slashing are signatures by `key`.

The key signed the signing root of each header, in the proposer domain of the run.

The version is the one that the state before the block reads at the epoch of the slot of the header.

This needs the assumption on the header calls of the run. -/
theorem HeaderCheck.signedIn {g a : ForkedBeaconState preset} {run : Run config checks g a}
    {key : BLSPubkey} (c : HeaderCheck run key) {signed : BLSPubkey → ByteArray → Prop}
    (sound : checks.VerifySoundOn (· ∈ verifyCalls run) signed) :
    ∀ header ∈ [c.slashing.signedHeader1, c.slashing.signedHeader2],
      SignedIn config g.state.genesisValidatorsRoot signed key DOMAIN_BEACON_PROPOSER
        (c.before.forkVersions.versionAt (computeEpochAtSlot preset header.message.slot))
        header.message := by
  -- The checked state follows the state before the block, so it keeps its genesis root.
  have rooted : c.checked.genesisValidatorsRoot = g.state.genesisValidatorsRoot :=
    ((BlockFrame.foldlM (fun _ _ _ ok => frame_processProposerSlashing ok)
      c.earlier).genesisValidatorsRoot.trans
      (frame_operationsInput c.started).genesisValidatorsRoot).trans
      c.toCheckSite.genesisValidatorsRoot
  intro header member
  have checked : checkHeaderSignature config checks c.checked key header = .ok () := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact c.first
    · exact c.second
  obtain ⟨domain, root, domainOk, rootOk, verified⟩ := checkHeaderSignature_ok checked
  -- The call is one of the header calls of the run.
  have call : (key, packBytes root, header.signature) ∈ verifyCalls run :=
    ⟨key, c, header, member, domain, root, domainOk, rootOk, rfl⟩
  -- The checked state keeps the fork versions of the state before the block.
  have versions : c.checked.forkVersions = c.before.forkVersions :=
    (BlockFrame.foldlM (fun _ _ _ ok => frame_processProposerSlashing ok)
      c.earlier).forkVersions.trans (frame_operationsInput c.started).forkVersions
  -- The domain is that of the genesis root of the checked state and of one of its versions.
  simp only [getDomain, Option.getD_some, mapError_ok_iff, rooted, versions] at domainOk
  exact ⟨domain, root, domainOk, rootOk, sound _ _ _ call verified⟩

/-- The state before a block of a run from a genesis of deposits reads a version of the config.

At each epoch, that version is the version of a fork of the config. -/
theorem CheckSite.versionAt {g a : ForkedBeaconState preset} {run : Run config checks g a}
    (site : CheckSite run) (genesis : Genesis config checks g) (epoch : Epoch) :
    ∃ read : Fork, site.before.forkVersions.versionAt epoch = config.forkVersion read := by
  obtain ⟨pre, -, -⟩ := run.contains_split _ site.member
  exact (pre.forkVersions_ofConfig genesis).versionAt epoch

/-- A block step of a tail, read as a block step of the run that the tail ends. -/
def CheckSite.lift {g x a : ForkedBeaconState preset} (shared : Run config checks g x)
    {tail : Run config checks x a} (site : CheckSite tail) : CheckSite (shared.append tail) :=
  { site with member := (shared.contains_append tail _).mpr (.inr site.member) }

/-- A check of an indexed attestation by a tail, read as a check by the run that it ends. -/
def AttestationCheck.lift {g x a : ForkedBeaconState preset} (shared : Run config checks g x)
    {tail : Run config checks x a} {key : BLSPubkey} (c : AttestationCheck tail key) :
    AttestationCheck (shared.append tail) key :=
  { c with toCheckSite := c.toCheckSite.lift shared }

/-- A check of a proposer slashing by a tail, read as a check by the run that it ends. -/
def HeaderCheck.lift {g x a : ForkedBeaconState preset} (shared : Run config checks g x)
    {tail : Run config checks x a} {key : BLSPubkey} (c : HeaderCheck tail key) :
    HeaderCheck (shared.append tail) key :=
  { c with toCheckSite := c.toCheckSite.lift shared }

/-- The proposer of a proposer slashing checked in a tail holds its key at its index at `x`.

The key is at some index of the registry at `x`, and the runs start at a genesis from deposits.

The registry keeps its keys and their distinctness, so the proposer index is that index. -/
theorem HeaderCheck.proposerIndex_eq {g x a : ForkedBeaconState preset}
    (shared : Run config checks g x) {tail : Run config checks x a} {key : BLSPubkey}
    (c : HeaderCheck tail key) (genesis : Genesis config checks g) {i : Nat} {v : Validator}
    (found : x.state.validators.data[i]? = some v) (keyEq : v.pubkey = key) :
    c.slashing.signedHeader1.message.proposerIndex.toNat = i := by
  obtain ⟨pre, -, -⟩ := tail.contains_split _ c.member
  -- The registry at `x` is a prefix of the registry before the block.
  have prefixed := (validatorKeys_prefix_and_distinct_of_chainSteps pre.chainSteps).1
  -- The block keeps the keys and their distinctness up to the check.
  have frame : BlockFrame c.before c.checked :=
    (frame_operationsInput c.started).trans
      (BlockFrame.foldlM (fun _ _ _ ok => frame_processProposerSlashing ok) c.earlier)
  have distinct := frame.pubkeysDistinct ((shared.append pre).pubkeysDistinct genesis)
  -- The key of `x` stays at its index, and the proposer index holds the same key.
  obtain ⟨w, wFound, wKey⟩ :=
    validators_getElem?_of_validatorKeys_prefix (prefixed.trans frame.pubkeysPrefix) found
  obtain ⟨u, uFound, uKey⟩ := c.proposer
  exact distinct.index_eq uFound wFound ((uKey.trans keyEq.symm).trans wKey.symm)

/-- Every accountable key signed the signing roots of two conflicting objects.

They are two attestation data that the test of slashable votes flags, or two headers of one slot.

The proposer index of the two headers holds the key at `x`.

This needs the assumptions on the aggregate and header calls of both runs.

The runs start at a genesis from deposits, with more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes.
-/
theorem signedConflict_of_accountable {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a)
    (right : Run config checks x b) (genesis : Genesis config checks g)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 <
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {signed : BLSPubkey → ByteArray → Prop}
    (aggregate : checks.AggregateSoundOn
      (· ∈ aggregateCalls (shared.append left) ∪ aggregateCalls (shared.append right)) signed)
    (single : checks.VerifySoundOn
      (· ∈ verifyCalls (shared.append left) ∪ verifyCalls (shared.append right)) signed)
    {key : BLSPubkey} (member : key ∈ accountableKeys shared left right) :
    SignedConflict config g.state.genesisValidatorsRoot x signed key := by
  classical
  obtain ⟨unslashed, accountable⟩ := Finset.mem_filter.mp member
  -- An unslashed key at `x` is the key of a validator at some index of the registry at `x`.
  obtain ⟨i, v, found, keyEq⟩ :
      ∃ (i : Nat) (v : Validator), x.state.validators.data[i]? = some v ∧ v.pubkey = key := by
    simp only [unslashedKeys, activeKeys, keysAt, Finset.mem_filter, List.mem_toFinset,
      List.mem_filterMap, Option.map_eq_some_iff] at unslashed
    obtain ⟨⟨_, -, v, found, keyEq⟩, -⟩ := unslashed
    exact ⟨_, v, found, keyEq⟩
  -- A slashing in a tail gives two checks of its own, read as checks of the run it ends.
  have fromTail {z : ForkedBeaconState preset} (tail : Run config checks x z)
      (evidence : tail.SlashingEvidence key)
      (votes : checks.AggregateSoundOn (· ∈ aggregateCalls (shared.append tail)) signed)
      (headers : checks.VerifySoundOn (· ∈ verifyCalls (shared.append tail)) signed) :
      SignedConflict config g.state.genesisValidatorsRoot x signed key := by
    rcases checked_of_slashingEvidence evidence with ⟨one, two, conflict⟩ | ⟨c, conflict⟩
    · obtain ⟨f₁, read₁⟩ := (one.lift shared).versionAt genesis one.indexed.data.target.epoch
      obtain ⟨f₂, read₂⟩ := (two.lift shared).versionAt genesis two.indexed.data.target.epoch
      have first := (one.lift shared).signedIn votes
      have second := (two.lift shared).signedIn votes
      simp only [AttestationCheck.lift, CheckSite.lift] at first second read₁ read₂
      rw [read₁] at first
      rw [read₂] at second
      exact Or.inl ⟨_, _, f₁, f₂, conflict, first, second⟩
    · -- The two headers share a slot, so the state reads one version for both.
      obtain ⟨f, read⟩ := (c.lift shared).versionAt genesis
        (computeEpochAtSlot preset c.slashing.signedHeader1.message.slot)
      have first := (c.lift shared).signedIn headers c.slashing.signedHeader1
        (by simp [HeaderCheck.lift])
      have second := (c.lift shared).signedIn headers c.slashing.signedHeader2
        (by simp [HeaderCheck.lift])
      simp only [HeaderCheck.lift, CheckSite.lift] at first second read
      rw [read] at first
      rw [← conflict.1, read] at second
      refine Or.inr ⟨_, _, f, conflict.1, conflict.2.1, conflict.2.2, ⟨v, ?_, keyEq⟩, first,
        second⟩
      rw [c.proposerIndex_eq shared genesis found keyEq]
      exact found
  rcases accountable with ⟨d₁, d₂, first, second, conflict⟩ | evidence | evidence
  · -- Each accepted vote comes with an accepted aggregate check, so the key signed its data.
    have vote {data : AttestationData}
        (accepted : AcceptedEither (shared.append left) (shared.append right) key data) :
        ∃ f : Fork, SignedIn config g.state.genesisValidatorsRoot signed key
          DOMAIN_BEACON_ATTESTER (config.forkVersion f) data := by
      rcases accepted with accepted | accepted
      · obtain ⟨c, rfl⟩ := Run.attestationCheck_of_accepted lookahead accepted
        obtain ⟨f, read⟩ := c.versionAt genesis c.indexed.data.target.epoch
        exact ⟨f, read ▸ c.signedIn fun _ _ _ call => aggregate _ _ _ (.inl call)⟩
      · obtain ⟨c, rfl⟩ := Run.attestationCheck_of_accepted lookahead accepted
        obtain ⟨f, read⟩ := c.versionAt genesis c.indexed.data.target.epoch
        exact ⟨f, read ▸ c.signedIn fun _ _ _ call => aggregate _ _ _ (.inr call)⟩
    obtain ⟨f₁, one⟩ := vote first
    obtain ⟨f₂, two⟩ := vote second
    exact Or.inl ⟨d₁, d₂, f₁, f₂, conflict, one, two⟩
  · exact fromTail left evidence (fun _ _ _ call => aggregate _ _ _ (.inl call))
      (fun _ _ _ call => single _ _ _ (.inl call))
  · exact fromTail right evidence (fun _ _ _ call => aggregate _ _ _ (.inr call))
      (fun _ _ _ call => single _ _ _ (.inr call))

/-- The unslashed active keys at `x` that signed the signing roots of two conflicting objects. -/
noncomputable def signedConflictKeys (config : Config) (genesisRoot : Root)
    (signed : BLSPubkey → ByteArray → Prop) (x : ForkedBeaconState preset) :
    Finset BLSPubkey := by
  classical
  exact (unslashedKeys x.state).filter (SignedConflict config genesisRoot x signed)

/-- Every accountable key is among the keys that signed conflicting objects.

This needs the assumptions on the aggregate and header calls of both runs.

The runs start at a genesis from deposits, with more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes.
-/
theorem accountableKeys_subset_signedConflictKeys {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a)
    (right : Run config checks x b) (genesis : Genesis config checks g)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 <
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {signed : BLSPubkey → ByteArray → Prop}
    (aggregate : checks.AggregateSoundOn
      (· ∈ aggregateCalls (shared.append left) ∪ aggregateCalls (shared.append right)) signed)
    (single : checks.VerifySoundOn
      (· ∈ verifyCalls (shared.append left) ∪ verifyCalls (shared.append right)) signed) :
    accountableKeys shared left right ⊆
      signedConflictKeys config g.state.genesisValidatorsRoot signed x := by
  classical
  intro key member
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp member).1,
    signedConflict_of_accountable shared left right genesis lookahead aggregate single member⟩

/-- Direct accountable safety, for the keys that signed conflicting objects.

The finalized checkpoints of the two runs conflict, and the left epoch is at most the right one.

Then the unslashed active stake at `x` is at most three times the stake of those keys at `x`.

Twice the larger drift of the two tails is added.

Otherwise SHA-256 collides in the root of a header of the runs, or a header or state has root zero.

This needs the assumptions on the aggregate and header calls of both runs.

The other hypotheses are those of direct accountable safety. -/
theorem accountable_safety_signed {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b)
    (parameters : Parameters preset) (genesis : Genesis config checks g)
    (enoughA : EnoughStake (shared.append left) b.state.finalizedCheckpoint.epoch.toNat)
    (enoughB : EnoughStake (shared.append right) b.state.finalizedCheckpoint.epoch.toNat)
    (ordered : a.state.finalizedCheckpoint.epoch ≤ b.state.finalizedCheckpoint.epoch)
    (conflict : Conflict (shared.append left) (shared.append right)
      a.state.finalizedCheckpoint b.state.finalizedCheckpoint)
    {signed : BLSPubkey → ByteArray → Prop}
    (aggregate : checks.AggregateSoundOn
      (· ∈ aggregateCalls (shared.append left) ∪ aggregateCalls (shared.append right)) signed)
    (single : checks.VerifySoundOn
      (· ∈ verifyCalls (shared.append left) ∪ verifyCalls (shared.append right)) signed) :
    Models.stake (effectiveWeight x.state) (unslashedKeys x.state) ≤
        3 * Models.stake (effectiveWeight x.state)
          (signedConflictKeys config g.state.genesisValidatorsRoot signed x) +
        2 * max (derivedDrift b.state.finalizedCheckpoint.epoch.toNat left)
          (derivedDrift b.state.finalizedCheckpoint.epoch.toNat right) ∨
      HashEvidence ((shared.append left).hashObjects ++ (shared.append right).hashObjects) := by
  classical
  rcases accountable_safety shared left right parameters genesis enoughA enoughB ordered
    conflict with bound | hashes
  · -- Each accountable key signed conflicting objects, so the signers hold at least its stake.
    have more := Models.stake_mono (w := effectiveWeight x.state)
      (accountableKeys_subset_signedConflictKeys shared left right genesis parameters.lookahead
        aggregate single)
    exact .inl (by omega)
  · exact .inr hashes

/-- Direct accountable safety, for the keys that signed conflicting objects, in its one-third form.

The hypotheses are those of the signed form, with stable unslashed active keys on both tails.

That holds up to one epoch past the later finalized epoch, as for the one-third form.

Then the signers of conflicting objects hold at least a third of the unslashed active stake at `x`.

Otherwise SHA-256 collides in the root of a header of the runs, or a header or state has root zero.
-/
theorem accountable_safety_signed_third {g x a b : ForkedBeaconState preset}
    (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b)
    (parameters : Parameters preset) (genesis : Genesis config checks g)
    (enoughA : EnoughStake (shared.append left) b.state.finalizedCheckpoint.epoch.toNat)
    (enoughB : EnoughStake (shared.append right) b.state.finalizedCheckpoint.epoch.toNat)
    (ordered : a.state.finalizedCheckpoint.epoch ≤ b.state.finalizedCheckpoint.epoch)
    (conflict : Conflict (shared.append left) (shared.append right)
      a.state.finalizedCheckpoint b.state.finalizedCheckpoint)
    {signed : BLSPubkey → ByteArray → Prop}
    (aggregate : checks.AggregateSoundOn
      (· ∈ aggregateCalls (shared.append left) ∪ aggregateCalls (shared.append right)) signed)
    (single : checks.VerifySoundOn
      (· ∈ verifyCalls (shared.append left) ∪ verifyCalls (shared.append right)) signed)
    (stableA : ∀ {u : ForkedBeaconState preset} (pre : Run config checks x u)
      (post : Run config checks u a), pre.append post = left →
        (getCurrentEpoch u.state).toNat ≤ b.state.finalizedCheckpoint.epoch.toNat + 1 →
          StableKeys x u)
    (stableB : ∀ {u : ForkedBeaconState preset} (pre : Run config checks x u)
      (post : Run config checks u b), pre.append post = right →
        (getCurrentEpoch u.state).toNat ≤ b.state.finalizedCheckpoint.epoch.toNat + 1 →
          StableKeys x u) :
    Models.stake (effectiveWeight x.state) (unslashedKeys x.state) ≤
        3 * Models.stake (effectiveWeight x.state)
          (signedConflictKeys config g.state.genesisValidatorsRoot signed x) ∨
      HashEvidence ((shared.append left).hashObjects ++ (shared.append right).hashObjects) := by
  classical
  rcases accountable_safety_third shared left right parameters genesis enoughA enoughB ordered
    conflict stableA stableB with bound | hashes
  · -- Each accountable key signed conflicting objects, so the signers hold at least its stake.
    have more := Models.stake_mono (w := effectiveWeight x.state)
      (accountableKeys_subset_signedConflictKeys shared left right genesis parameters.lookahead
        aggregate single)
    exact .inl (by omega)
  · exact .inr hashes

end EthLib.Consensus.DirectSafety
