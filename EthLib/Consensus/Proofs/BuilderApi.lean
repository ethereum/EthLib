module

public import EthLib.Consensus.BuilderApi
public import EthLib.Consensus.Proofs.Constants
public import EthLib.Consensus.Proofs.Containers.BuilderApi
public import EthLib.Consensus.Proofs.Signing
public import EthLib.Consensus.Transition.Block

/-!
# Proofs: the Builder API

The two domain types of the Builder API set the bit of the application mask.

No domain type of a fork sets it, so none of them equals either type.

So no domain of a fork equals a domain of the Builder API, at any fork version or validators root.

The two domains of the Builder API also differ from each other.

From Bellatrix to Fulu, blinding a body or a block always succeeds and keeps its root.

So a signature over a blinded block is a signature over the full block.

When the block names the proposer of the state, the two checks of a signature agree.

Unblinding with a payload of the same header undoes blinding, and blinding undoes unblinding.

So the signature of the proposer checks the same on the full block as on the blinded block.

From Gloas, a bid's execution payment adds at most the proposer's cap to its value.

A payment at or above the cap adds the cap, and a payment at or below it adds itself.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

/-- The domain type of registrations and bids sets the bit of the application mask. -/
theorem DOMAIN_APPLICATION_BUILDER_masked :
    DOMAIN_APPLICATION_BUILDER[3] &&& DOMAIN_APPLICATION_MASK[3] ≠ 0 := by
  decide

/-- No domain type of a fork is the domain type of registrations and bids. -/
theorem DOMAIN_APPLICATION_BUILDER_not_mem :
    DOMAIN_APPLICATION_BUILDER ∉ protocolDomainTypes :=
  not_mem_protocolDomainTypes_of_masked 3 DOMAIN_APPLICATION_BUILDER_masked

/-- The domain type of request authentication sets the bit of the application mask. -/
theorem DOMAIN_BUILDER_REQUEST_AUTH_masked :
    DOMAIN_BUILDER_REQUEST_AUTH[3] &&& DOMAIN_APPLICATION_MASK[3] ≠ 0 := by
  decide

/-- No domain type of a fork is the domain type of request authentication. -/
theorem DOMAIN_BUILDER_REQUEST_AUTH_not_mem :
    DOMAIN_BUILDER_REQUEST_AUTH ∉ protocolDomainTypes :=
  not_mem_protocolDomainTypes_of_masked 3 DOMAIN_BUILDER_REQUEST_AUTH_masked

/-- The domain type of request authentication is not the protocol domain type of builders.

The builder specification warns that the two must not be confused. -/
theorem DOMAIN_BUILDER_REQUEST_AUTH_ne_DOMAIN_BEACON_BUILDER :
    DOMAIN_BUILDER_REQUEST_AUTH ≠ DOMAIN_BEACON_BUILDER := by
  decide

/-- The domain type of request authentication is not that of registrations and bids. -/
theorem DOMAIN_BUILDER_REQUEST_AUTH_ne_DOMAIN_APPLICATION_BUILDER :
    DOMAIN_BUILDER_REQUEST_AUTH ≠ DOMAIN_APPLICATION_BUILDER := by
  decide

/-- No domain of a fork is a domain of the Builder API whose type sets a bit of the mask.

This holds whatever the fork version and the validators root of the domain of the fork. -/
theorem builderDomain_ne_of_masked {config : Config} {builderType domainType : DomainType}
    {version : Version} {root : Root} {builder domain : Domain} (i : Fin 4)
    (masked : builderType[i] &&& DOMAIN_APPLICATION_MASK[i] ≠ 0)
    (protocol : domainType ∈ protocolDomainTypes)
    (built : builderDomain config builderType = .ok builder)
    (computed : computeDomain config domainType version root = .ok domain) :
    builder ≠ domain := by
  refine computeDomain_ne (first := builderType) ?_ built computed
  intro same
  exact not_mem_protocolDomainTypes_of_masked i masked (same ▸ protocol)

/-- No domain of a fork is that of registrations and bids, whatever its fork version and chain. -/
theorem builderDomain_ne {config : Config} {domainType : DomainType} {version : Version}
    {root : Root} {builder domain : Domain} (protocol : domainType ∈ protocolDomainTypes)
    (built : builderDomain config = .ok builder)
    (computed : computeDomain config domainType version root = .ok domain) :
    builder ≠ domain :=
  builderDomain_ne_of_masked 3 DOMAIN_APPLICATION_BUILDER_masked protocol built computed

/-- No domain of a fork is the domain of request authentication, whatever its version and chain. -/
theorem builderDomain_requestAuth_ne {config : Config} {domainType : DomainType}
    {version : Version} {root : Root} {auth domain : Domain}
    (protocol : domainType ∈ protocolDomainTypes)
    (built : builderDomain config DOMAIN_BUILDER_REQUEST_AUTH = .ok auth)
    (computed : computeDomain config domainType version root = .ok domain) :
    auth ≠ domain :=
  builderDomain_ne_of_masked 3 DOMAIN_BUILDER_REQUEST_AUTH_masked protocol built computed

/-- The domain of request authentication is never that of registrations and bids.

This holds whatever the fork version and the validators root of the second domain. -/
theorem builderDomain_requestAuth_ne_builderDomain {config : Config} {version : Version}
    {root : Root} {auth domain : Domain}
    (built : builderDomain config DOMAIN_BUILDER_REQUEST_AUTH = .ok auth)
    (computed : computeDomain config DOMAIN_APPLICATION_BUILDER version root = .ok domain) :
    auth ≠ domain :=
  computeDomain_ne DOMAIN_BUILDER_REQUEST_AUTH_ne_DOMAIN_APPLICATION_BUILDER built computed

/-- The execution payment adds at most the cap to the value of a bid. -/
theorem builderBidValue_le (value executionPayment : Gwei) (preferences : BuilderPreferences) :
    builderBidValue value executionPayment preferences ≤
      value.toNat + preferences.maxExecutionPayment.toNat :=
  Nat.add_le_add_left (Nat.min_le_right _ _) _

/-- An execution payment at or above the cap adds exactly the cap to the value of a bid. -/
theorem builderBidValue_of_cap_le {value executionPayment : Gwei}
    {preferences : BuilderPreferences}
    (above : preferences.maxExecutionPayment.toNat ≤ executionPayment.toNat) :
    builderBidValue value executionPayment preferences =
      value.toNat + preferences.maxExecutionPayment.toNat := by
  rw [builderBidValue, Nat.min_eq_right above]

/-- An execution payment at or below the cap adds itself in full to the value of a bid. -/
theorem builderBidValue_of_le_cap {value executionPayment : Gwei}
    {preferences : BuilderPreferences}
    (below : executionPayment.toNat ≤ preferences.maxExecutionPayment.toNat) :
    builderBidValue value executionPayment preferences = value.toNat + executionPayment.toNat := by
  rw [builderBidValue, Nat.min_eq_left below]

/-- A zero cap leaves the bid valued at its beacon-chain payment alone. -/
theorem builderBidValue_zero_cap (value executionPayment : Gwei) :
    builderBidValue value executionPayment ⟨0⟩ = value.toNat := by
  simp [builderBidValue]

/-- The largest cap counts the execution payment in full, without wrapping the sum. -/
theorem builderBidValue_max_cap (value executionPayment : Gwei) :
    builderBidValue value executionPayment ⟨MAX_EXECUTION_PAYMENT⟩ =
      value.toNat + executionPayment.toNat := by
  apply builderBidValue_of_le_cap
  have max : MAX_EXECUTION_PAYMENT.toNat = 2 ^ 64 - 1 := by decide
  have bound := executionPayment.toNat_lt
  change executionPayment.toNat ≤ MAX_EXECUTION_PAYMENT.toNat
  omega

variable {preset : Preset} {fork : Fork}

/-- The root of a container from the roots of its fields does not read the names of its fields. -/
private theorem summaryRoot_container_names (names names' : List String) (roots : List Bytes) :
    summaryRoot (.container names) roots = summaryRoot (.container names') roots :=
  hashTreeRoot_container_names _ _ _ _

/-- From Bellatrix to Fulu, every body has a blinded form. -/
theorem BeaconBlockBody.blind_total (body : BeaconBlockBody preset fork)
    (range : HasBuilderApi fork) : ∃ blinded, body.blind range = .ok blinded := by
  obtain ⟨header, made⟩ := ExecutionPayload.header_total (body.executionPayload range)
  exact ⟨_, by rw [BeaconBlockBody.blind, made]; rfl⟩

/-- From Bellatrix to Fulu, every block has a blinded form. -/
theorem BeaconBlock.blind_total (block : BeaconBlock preset fork) (range : HasBuilderApi fork) :
    ∃ blinded, block.blind range = .ok blinded := by
  obtain ⟨body, made⟩ := block.body.blind_total range
  exact ⟨_, by rw [BeaconBlock.blind, made]; rfl⟩

/-- From Bellatrix to Fulu, a blinded body has the root of its body, as a tree before its hash.

The header and the payload have the same root, and every other field is the same. -/
private theorem BeaconBlockBody.root_blind [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    {body : BeaconBlockBody preset fork} {range : HasBuilderApi fork}
    {blinded : BlindedBeaconBlockBody preset fork} (made : body.blind range = .ok blinded) :
    SszType.root blinded = SszType.root body := by
  cases made' : (body.executionPayload range).header with
  | error e => simp [BeaconBlockBody.blind, made', bind, Except.bind] at made
  | ok header =>
    simp [BeaconBlockBody.blind, made', bind, Except.bind, pure, Except.pure] at made
    subst made
    have same := ExecutionPayload.hashTreeRoot_header range.2 made'
    obtain ⟨root, rooted⟩ := SszType.hashTreeRoot_total (body.executionPayload range)
    rw [rooted, SszType.hashTreeRoot_ok_iff, ← LawfulSszType.root_eq] at same
    rw [SszType.hashTreeRoot_ok_iff, ← LawfulSszType.root_eq, ← same] at rooted
    obtain ⟨bellatrix, gloas⟩ := range
    -- At each fork of the range, both containers list the roots of the same fields.
    cases fork <;> try (first | exact absurd bellatrix (by decide) | exact absurd gloas (by decide))
    all_goals
      change (do summaryRoot _ (← SszFields.roots _)) = (do summaryRoot _ (← SszFields.roots _))
      simp +decide only [SszFields.roots, rooted, dite_true, dite_false]
      exact congrArg (_ >>= ·) (funext fun roots => summaryRoot_container_names _ _ roots)

/-- From Bellatrix to Fulu, a body that unblinds blinds back to the blinded body it came from. -/
theorem BlindedBeaconBlockBody.unblind_blind {body : BlindedBeaconBlockBody preset fork}
    {range : HasBuilderApi fork} {payload : ExecutionPayload preset fork}
    {full : BeaconBlockBody preset fork} (made : body.unblind range payload = .ok full) :
    full.blind range = .ok body := by
  unfold BlindedBeaconBlockBody.unblind at made
  split at made
  · simp at made
  · rename_i header computed
    split at made
    · rename_i same
      simp only [Except.ok.injEq] at made
      subst made
      simp only [BeaconBlockBody.blind, computed, bind, Except.bind, pure, Except.pure]
      cases body
      congr
      funext h
      exact same
    · simp at made

/-- From Bellatrix to Fulu, a blinded body unblinds with the payload of its body, to that body. -/
theorem BeaconBlockBody.blind_unblind {full : BeaconBlockBody preset fork}
    {range : HasBuilderApi fork} {body : BlindedBeaconBlockBody preset fork}
    (made : full.blind range = .ok body) :
    body.unblind range (full.executionPayload range) = .ok full := by
  cases computed : (full.executionPayload range).header with
  | error e => simp [BeaconBlockBody.blind, computed, bind, Except.bind] at made
  | ok header =>
    simp only [BeaconBlockBody.blind, computed, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at made
    subst made
    simp only [BlindedBeaconBlockBody.unblind, computed, ite_true]
    cases full
    congr
    all_goals funext h
    all_goals exact absurd h (Nat.not_le_of_lt range.2)

/-- From Bellatrix to Fulu, a blinded body fails on its header exactly when the payload's differs.
-/
theorem BlindedBeaconBlockBody.unblind_eq_headerMismatch_iff
    {body : BlindedBeaconBlockBody preset fork} {range : HasBuilderApi fork}
    {payload : ExecutionPayload preset fork} :
    body.unblind range payload = .error .headerMismatch ↔
      ∃ header, payload.header = .ok header ∧ header ≠ body.executionPayloadHeader range := by
  unfold BlindedBeaconBlockBody.unblind
  constructor
  · intro failed
    split at failed
    · simp at failed
    · rename_i header computed
      split at failed
      · simp at failed
      · exact ⟨header, computed, by assumption⟩
  · rintro ⟨header, computed, differs⟩
    simp [computed, differs]

/-- From Bellatrix to Fulu, a blinded body never fails for want of the header of the payload.

The header of a payload always computes, so no other failure occurs. -/
theorem BlindedBeaconBlockBody.unblind_ne_header {body : BlindedBeaconBlockBody preset fork}
    {range : HasBuilderApi fork} {payload : ExecutionPayload preset fork} (fault : Err) :
    body.unblind range payload ≠ .error (.header fault) := by
  obtain ⟨header, computed⟩ := ExecutionPayload.header_total payload
  simp only [BlindedBeaconBlockBody.unblind, computed]
  split <;> simp

/-- From Bellatrix to Fulu, a block that unblinds blinds back to the blinded block it came from. -/
theorem BlindedBeaconBlock.unblind_blind {block : BlindedBeaconBlock preset fork}
    {range : HasBuilderApi fork} {payload : ExecutionPayload preset fork}
    {full : BeaconBlock preset fork} (made : block.unblind range payload = .ok full) :
    full.blind range = .ok block := by
  cases body : block.body.unblind range payload with
  | error e => simp [BlindedBeaconBlock.unblind, body, bind, Except.bind] at made
  | ok fullBody =>
    simp only [BlindedBeaconBlock.unblind, body, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at made
    subst made
    simp [BeaconBlock.blind, BlindedBeaconBlockBody.unblind_blind body, bind, Except.bind, pure,
      Except.pure]

/-- From Bellatrix to Fulu, a signed blinded block that unblinds keeps its proposer and signature.

The block it gives blinds back to the blinded block. -/
theorem SignedBlindedBeaconBlock.unblind_blind {signed : SignedBlindedBeaconBlock preset fork}
    {range : HasBuilderApi fork} {payload : ExecutionPayload preset fork}
    {full : SignedBeaconBlock preset fork} (made : signed.unblind range payload = .ok full) :
    full.message.blind range = .ok signed.message ∧ full.signature = signed.signature ∧
      full.message.proposerIndex = signed.message.proposerIndex := by
  cases block : signed.message.unblind range payload with
  | error e => simp [SignedBlindedBeaconBlock.unblind, block, bind, Except.bind] at made
  | ok fullBlock =>
    simp only [SignedBlindedBeaconBlock.unblind, block, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at made
    subst made
    refine ⟨BlindedBeaconBlock.unblind_blind block, rfl, ?_⟩
    cases body : signed.message.body.unblind range payload with
    | error e => simp [BlindedBeaconBlock.unblind, body, bind, Except.bind] at block
    | ok fullBody =>
      simp only [BlindedBeaconBlock.unblind, body, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at block
      subst block
      rfl

variable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]

/-- From Bellatrix to Fulu, a blinded body has the root of its body.

The header of the payload has the root of the payload, and every other field is the same. -/
theorem BeaconBlockBody.hashTreeRoot_blind {body : BeaconBlockBody preset fork}
    {range : HasBuilderApi fork} {blinded : BlindedBeaconBlockBody preset fork}
    (made : body.blind range = .ok blinded) :
    SszType.hashTreeRoot blinded = SszType.hashTreeRoot body := by
  unfold SszType.hashTreeRoot
  rw [BeaconBlockBody.root_blind made]

/-- From Bellatrix to Fulu, a blinded block has the root of its block.

So the proposer signs the same root as for the full block. -/
theorem BeaconBlock.hashTreeRoot_blind {block : BeaconBlock preset fork}
    {range : HasBuilderApi fork} {blinded : BlindedBeaconBlock preset fork}
    (made : block.blind range = .ok blinded) :
    SszType.hashTreeRoot blinded = SszType.hashTreeRoot block := by
  cases made' : block.body.blind range with
  | error e => simp [BeaconBlock.blind, made', bind, Except.bind] at made
  | ok body =>
    simp [BeaconBlock.blind, made', bind, Except.bind, pure, Except.pure] at made
    subst made
    unfold SszType.hashTreeRoot
    congr 1
    change (do summaryRoot _ (← SszFields.roots _)) = (do summaryRoot _ (← SszFields.roots _))
    simp only [SszFields.roots, BeaconBlockBody.root_blind made']

/-- From Bellatrix to Fulu, a blinded block has the signing root of its block, under any domain.

So a signature over the blinded block is a signature over the full block. -/
theorem BeaconBlock.computeSigningRoot_blind {block : BeaconBlock preset fork}
    {range : HasBuilderApi fork} {blinded : BlindedBeaconBlock preset fork}
    (made : block.blind range = .ok blinded) (domain : Domain) :
    computeSigningRoot blinded domain = computeSigningRoot block domain := by
  simp [computeSigningRoot, BeaconBlock.hashTreeRoot_blind made]

/-- From Bellatrix to Fulu, a signature verifies on a blinded block exactly as on its full block.

The full block must name the proposer of the state, which the blinded check reads from the state.

Both checks then read the same key, the same domain and the same signing root. -/
theorem verifyBlindedBlockSignature_blind {config : Config} {checks : SignatureChecks}
    {state : BeaconState preset fork} {block : BeaconBlock preset fork}
    {range : HasBuilderApi fork} {blinded : BlindedBeaconBlock preset fork}
    (made : block.blind range = .ok blinded)
    (proposer : getBeaconProposerIndex state = .ok block.proposerIndex)
    (signature : Cryptography.Bls.BLSSignature) :
    verifyBlindedBlockSignature config checks state ⟨blinded, signature⟩ =
      verifyBlockSignature config checks state ⟨block, signature⟩ := by
  simp [verifyBlindedBlockSignature, verifyBlockSignature, proposer, liftAccessor,
    BeaconBlock.computeSigningRoot_blind made, bind, Except.bind, Except.mapError]

/-- From Bellatrix to Fulu, the proposer's signature checks the same on the unblinded block.

The check on the unblinded block is the check on the blinded block.

The block must name the proposer of the state. -/
theorem verifyBlockSignature_unblind {config : Config} {checks : SignatureChecks}
    {state : BeaconState preset fork} {signed : SignedBlindedBeaconBlock preset fork}
    {range : HasBuilderApi fork} {payload : ExecutionPayload preset fork}
    {full : SignedBeaconBlock preset fork} (made : signed.unblind range payload = .ok full)
    (proposer : getBeaconProposerIndex state = .ok signed.message.proposerIndex) :
    verifyBlockSignature config checks state full =
      verifyBlindedBlockSignature config checks state signed := by
  obtain ⟨blinds, signature, index⟩ := SignedBlindedBeaconBlock.unblind_blind made
  have same := verifyBlindedBlockSignature_blind (config := config) (checks := checks) blinds
    (index ▸ proposer) full.signature
  cases full
  cases signed
  simp only at signature
  subst signature
  exact same.symm

end EthLib.Consensus
