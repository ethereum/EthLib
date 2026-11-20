module

public import EthLib.Consensus.Proofs.DirectSafety.Signatures
public import EthLib.Consensus.Proofs.Transition.AttesterSlashingAccepted

/-!
# Includable slashings of the keys of signed direct safety

Signed direct safety finds keys that signed two conflicting attestation data.

It does not show that a state could slash them, for three reasons.

An aggregate names all its signers, and its signature cannot drop one.

So an aggregate of one run may not verify against the registry of the other.

A validator may already be withdrawable, and then no slashing touches it.

A state checks a signature only under its previous or current fork version.

The simplest sufficient case is a signature by the key alone on each data.

Given two such signatures, the slashing that names the validator of the key alone is built here.

A state returns, on it, what slashing that validator returns.

The state must read the fork version of each signature at the target epoch of its data.

It must have the genesis validators root of the signatures, as each state of the runs does.

The validator must be slashable at the epoch of the state.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- The attester slashing of one validator by two signatures, one on each of two data.

Each attestation names the validator alone.

The preset must allow one attester or more, so that one index fits the list before Gloas. -/
def singleAttesterSlashing (index : ValidatorIndex) (first second : AttestationData)
    (firstSignature secondSignature : BLSSignature) (attesters : 1 ≤ maxAttesters preset fork) :
    AttesterSlashing preset fork :=
  let indices : ForkList .glamsterdam fork ValidatorIndex (maxAttesters preset fork) :=
    ⟨#[index], fun _ => attesters⟩
  ⟨⟨indices, first, firstSignature⟩, ⟨indices, second, secondSignature⟩⟩

/-- A state returns, on the slashing of a key by two signed conflicting data, what slashing returns.

The two data are a double or surround vote, each with the domain and signing root of a signature.

Each domain is that of a fork version and of a genesis validators root.

The two signatures are by the key alone, and each verifies on its signing root.

The state reads the fork version of each signature at the target epoch of its data.

It has the genesis validators root of the signatures.

The validator of the key is slashable at the epoch of the state.

Then the state returns what slashing the validator returns: it accepts exactly when it can slash. -/
theorem processAttesterSlashing_single_eq_slashValidator {config : Config}
    {checks : SignatureChecks} {state : BeaconState preset fork} {genesisRoot : Root}
    {key : BLSPubkey} {first second : AttestationData} {firstFork secondFork : Fork}
    {firstDomain secondDomain : Domain} {firstRoot secondRoot : Root}
    (conflict : isSlashableAttestationData first second = true)
    (firstDomained : computeDomain config DOMAIN_BEACON_ATTESTER (config.forkVersion firstFork)
      genesisRoot = .ok firstDomain)
    (firstRooted : computeSigningRoot first firstDomain = .ok firstRoot)
    (secondDomained : computeDomain config DOMAIN_BEACON_ATTESTER
      (config.forkVersion secondFork) genesisRoot = .ok secondDomain)
    (secondRooted : computeSigningRoot second secondDomain = .ok secondRoot)
    (firstSignature secondSignature : BLSSignature)
    (firstVerified :
      checks.fastAggregateVerify #[key] (packBytes firstRoot) firstSignature = true)
    (secondVerified :
      checks.fastAggregateVerify #[key] (packBytes secondRoot) secondSignature = true)
    (rooted : state.genesisValidatorsRoot = genesisRoot)
    (windowFirst : state.forkVersions.versionAt first.target.epoch = config.forkVersion firstFork)
    (windowSecond :
      state.forkVersions.versionAt second.target.epoch = config.forkVersion secondFork)
    {index : ValidatorIndex} {validator : Validator}
    (found : getValidator state index = .ok validator) (keyEq : validator.pubkey = key)
    (slashable : isSlashableValidator validator (getCurrentEpoch state) = true)
    (attesters : 1 ≤ maxAttesters preset fork) :
    processAttesterSlashing config checks state
        (singleAttesterSlashing index first second firstSignature secondSignature attesters) =
      liftAccessor (slashValidator config state index) := by
  subst keyEq
  -- The state reads each fork version and the genesis root of its signature, so the same domain.
  refine processAttesterSlashing_eq_slashValidator_of_single rfl rfl conflict found slashable
    ⟨firstDomain, firstRoot, ?_, firstRooted, firstVerified⟩
    ⟨secondDomain, secondRoot, ?_, secondRooted, secondVerified⟩ fun _ => attesters
  · simp [singleAttesterSlashing, getDomain, windowFirst, rooted, firstDomained, Except.mapError]
  · simp [singleAttesterSlashing, getDomain, windowSecond, rooted, secondDomained, Except.mapError]

/-- The same, at a state that a run reaches from the genesis of the signatures.

Such a state has that genesis validators root, so only the fork versions remain to check. -/
theorem processAttesterSlashing_single_eq_slashValidator_run {config : Config}
    {checks : SignatureChecks} {g y : ForkedBeaconState preset} (run : Run config checks g y)
    {key : BLSPubkey} {first second : AttestationData} {firstFork secondFork : Fork}
    {firstDomain secondDomain : Domain} {firstRoot secondRoot : Root}
    (conflict : isSlashableAttestationData first second = true)
    (firstDomained : computeDomain config DOMAIN_BEACON_ATTESTER (config.forkVersion firstFork)
      g.state.genesisValidatorsRoot = .ok firstDomain)
    (firstRooted : computeSigningRoot first firstDomain = .ok firstRoot)
    (secondDomained : computeDomain config DOMAIN_BEACON_ATTESTER
      (config.forkVersion secondFork) g.state.genesisValidatorsRoot = .ok secondDomain)
    (secondRooted : computeSigningRoot second secondDomain = .ok secondRoot)
    (firstSignature secondSignature : BLSSignature)
    (firstVerified :
      checks.fastAggregateVerify #[key] (packBytes firstRoot) firstSignature = true)
    (secondVerified :
      checks.fastAggregateVerify #[key] (packBytes secondRoot) secondSignature = true)
    (windowFirst :
      y.state.forkVersions.versionAt first.target.epoch = config.forkVersion firstFork)
    (windowSecond :
      y.state.forkVersions.versionAt second.target.epoch = config.forkVersion secondFork)
    {index : ValidatorIndex} {validator : Validator}
    (found : getValidator y.state index = .ok validator) (keyEq : validator.pubkey = key)
    (slashable : isSlashableValidator validator (getCurrentEpoch y.state) = true)
    (attesters : 1 ≤ maxAttesters preset y.fork) :
    processAttesterSlashing config checks y.state
        (singleAttesterSlashing index first second firstSignature secondSignature attesters) =
      liftAccessor (slashValidator config y.state index) :=
  processAttesterSlashing_single_eq_slashValidator conflict firstDomained firstRooted
    secondDomained secondRooted firstSignature secondSignature firstVerified secondVerified
    run.genesisValidatorsRoot windowFirst windowSecond found keyEq slashable attesters

end EthLib.Consensus.DirectSafety
