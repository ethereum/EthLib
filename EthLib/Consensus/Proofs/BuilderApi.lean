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

end EthLib.Consensus
