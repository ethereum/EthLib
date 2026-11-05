module

public import EthLib.Consensus.Builders
public import EthLib.Consensus.PqKeys.Possession
public import EthLib.Cryptography.Bls.Signatures
public import EthLib.Networking.Gossip.Topic
public import EthLib.Networking.Gossip.Validation

/-!
# `Consensus.PqKeys.Gossip`

Registrations travel on one global gossip topic, `pq_key_registration`.

A node forwards a registration only if it passes a list of checks, cheapest first.

Each check either ignores or rejects the registration when it fails.

A beacon block carries at most a preset number of registrations, and the block topic rejects more.

[EIP-8450][eip-8450] defines both, in its section "Gossip".

No fork includes the EIP yet, so the first epoch of the fork that activates it is an input.

The head state of that fork is not specified yet, so the checks read a view of the parts they use.

[eip-8450]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-8450.md#gossip
-/

@[expose] public section

namespace EthLib.Consensus.PqKeys

open Base Cryptography.Bls Serialization.Ssz Networking.Gossip

/-- The name of the topic of registrations. -/
def PQ_KEY_REGISTRATION_TOPIC : String := "pq_key_registration"

/-- The topic string of registrations under a fork digest. -/
def pqKeyRegistrationTopic (digest : ForkDigest) : String :=
  topicString digest PQ_KEY_REGISTRATION_TOPIC

/-- What the checks of a registration read from the head state of the node. -/
structure RegistrationView where
  /-- The root of the validators at genesis, which names the chain. -/
  genesisValidatorsRoot : Root
  /-- The epoch of the finalized checkpoint. -/
  finalizedEpoch : Epoch
  /-- The validators, by validator index. -/
  validators : Array Validator
  /-- The builders, by builder index. -/
  builders : Array Builder
  /-- The keys of each validator. -/
  validatorKeys : ValidatorPQKeyMaterial
  /-- The epoch of the last change of the keys of each validator. -/
  validatorChangeEpochs : ValidatorPQKeyChangeEpochs
  /-- The keys of each builder. -/
  builderKeys : BuilderPQKeyMaterial
  /-- The epoch of the last change of the keys of each builder. -/
  builderChangeEpochs : BuilderPQKeyChangeEpochs

/-- The BLS key and the stored entry of the registrant of an index, if the index names one.

The entry is the keys and the epoch of their last change. -/
def RegistrationView.registrant (view : RegistrationView) (index : ValidatorIndex) :
    Option (BLSPubkey × PQKeyMaterial × Epoch) :=
  if isBuilderIndex index then do
    let builder := (convertValidatorIndexToBuilderIndex index).toNat
    return ((← view.builders[builder]?).pubkey, ← view.builderKeys.data[builder]?,
      ← view.builderChangeEpochs.data[builder]?)
  else do
    let validator := index.toNat
    return ((← view.validators[validator]?).pubkey, ← view.validatorKeys.data[validator]?,
      ← view.validatorChangeEpochs.data[validator]?)

/-- Whether the registrant of an index has not begun to exit.

A validator has no exit epoch yet, and a builder has no withdrawable epoch yet. -/
def RegistrationView.notExiting (view : RegistrationView) (index : ValidatorIndex) : Bool :=
  if isBuilderIndex index then
    (view.builders[(convertValidatorIndexToBuilderIndex index).toNat]?).any
      (·.withdrawableEpoch == FAR_FUTURE_EPOCH)
  else (view.validators[index.toNat]?).any (·.exitEpoch == FAR_FUTURE_EPOCH)

/-- Whether an index names a validator, or a builder whose deposit epoch is finalized. -/
def RegistrationView.depositFinalized (view : RegistrationView) (index : ValidatorIndex) : Bool :=
  !isBuilderIndex index ||
    (view.builders[(convertValidatorIndexToBuilderIndex index).toNat]?).any
      (·.depositEpoch < view.finalizedEpoch)

/-- Whether any validator or builder holds a leanXMSS key. -/
def RegistrationView.keyInUse (view : RegistrationView) (key : XMSSPublicKey) : Bool :=
  view.validatorKeys.data.any (·.xmssPublicKey == key) ||
    view.builderKeys.data.any (·.xmssPublicKey == key)

/-- The root that the BLS signature of a registration signs, on a chain.

Its domain is that of a registration at the genesis fork version. -/
def registrationSigningRoot (config : Config) (genesisValidatorsRoot : Root)
    (registration : PQKeyRegistration) : Except Err Root := do
  let domain ← computeDomain config DOMAIN_PQ_KEY_REGISTRATION config.GENESIS_FORK_VERSION
    genesisValidatorsRoot
  computeSigningRoot registration domain

/-- Whether the BLS signature of a registration is valid under a BLS key. -/
def isValidRegistrationSignature (config : Config) (genesisValidatorsRoot : Root)
    (pubkey : BLSPubkey) (signed : SignedPQKeyRegistration) : Bool :=
  match registrationSigningRoot config genesisValidatorsRoot signed.message with
  | .ok root =>
    Cryptography.Bls.Signatures.verify (packBytes pubkey) (packBytes root)
      (packBytes signed.signature)
  | .error _ => false

/-- The checks of a registration on its topic, cheapest first.

The first check that fails gives the outcome.

# Arguments

- `activationEpoch`: the first epoch of the fork that activates the EIP.
- `clockEpoch`: the latest current epoch that the local clock allows, given the clock disparity.
- `head`: what the checks read from the head state, or nothing before that fork.
- `seen`: whether a valid registration with the same index and change epoch arrived first. -/
def validatePqKeyRegistration (config : Config) (preset : PqKeyPreset) (activationEpoch : Epoch)
    (clockEpoch : Epoch) (head : Option RegistrationView) (seen : Bool)
    (signed : SignedPQKeyRegistration) : ValidationResult :=
  let registration := signed.message
  let index := registration.index
  let keys := registration.keyMaterial
  let zero : XMSSPublicKey := Vector.replicate 32 0
  (ignoreUnless (activationEpoch ≤ clockEpoch) "before the fork of the registry").andThen fun _ =>
  match head with
  | none => .ignore "head state before the fork of the registry"
  | some view =>
  match view.registrant index with
  | none => .reject "no validator or builder at the index"
  | some (pubkey, stored, changeEpoch) =>
  (rejectUnless (view.notExiting index) "registrant exiting").andThen fun _ =>
  (ignoreUnless (view.depositFinalized index) "builder deposit not finalized").andThen fun _ =>
  (rejectUnless (!isBuilderIndex index || keys.vrfRoot == Vector.replicate 32 0)
    "builder with a VRF root").andThen fun _ =>
  (ignoreUnless (!seen) "registration already seen").andThen fun _ =>
  (rejectUnless (registration.previousChangeEpoch == changeEpoch)
    "previous change epoch not stored").andThen fun _ =>
  (ignoreUnless (stored.xmssPublicKey == zero || registration.previousChangeEpoch.toNat +
      preset.MIN_PQ_KEY_CHANGE_DELAY.toNat ≤ clockEpoch.toNat) "change too early").andThen fun _ =>
  (rejectUnless (keys.xmssPublicKey != zero) "zero leanXMSS key").andThen fun _ =>
  (rejectUnless (!view.keyInUse keys.xmssPublicKey) "leanXMSS key in use").andThen fun _ =>
  (rejectUnless (isValidRegistrationSignature config view.genesisValidatorsRoot pubkey signed)
    "invalid BLS signature").andThen fun _ =>
  rejectUnless (isValidPqPossessionProof config view.genesisValidatorsRoot pubkey
    keys.xmssPublicKey signed.possession) "invalid proof of possession"

/-- The extra check of a beacon block on its topic: at most the preset number of registrations. -/
def verifyPqKeyRegistrationsLimit (preset : PqKeyPreset) (registrations : PQKeyRegistrations) :
    ValidationResult :=
  rejectUnless (registrations.data.size ≤ preset.MAX_PQ_KEY_REGISTRATIONS.toNat)
    "too many pq key registrations"

end EthLib.Consensus.PqKeys
