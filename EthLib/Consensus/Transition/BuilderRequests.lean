module

public import EthLib.Consensus.Builders
public import EthLib.Consensus.Transition.Basic

/-!
# `Consensus.Transition.BuilderRequests`

From Gloas: the deposits and exits of builders that the execution layer requests.

A deposit to a key that no builder has registers a new builder, if its signature is valid.

A deposit to a known key adds to the balance of that builder, with no signature check.

Only a deposit whose withdrawal credentials carry the builder prefix counts; others are ignored.

A new builder takes the first index of a builder that has exited and been paid out, if any.

An exit request, sent from the address of a builder, starts the exit of that builder.

The builder must be active and owe nothing, or the request is ignored.

A 64-bit overflow is an error.

[EIP-8282] adds the two requests to [EIP-7732].

[EIP-8282]: https://eips.ethereum.org/EIPS/eip-8282#consensus-layer-processing
[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork}

/-- Whether a deposit message carries the signature of its key, under a domain type.

The domain is at the genesis version, with no validators root, so it holds at every fork. -/
def isValidDepositMessageSignature (config : Config) (checks : SignatureChecks)
    (domainType : DomainType) (pubkey : BLSPubkey) (withdrawalCredentials : Bytes32)
    (amount : Gwei) (signature : BLSSignature) : Except TransitionError Bool := do
  -- The message is the key, the withdrawal credentials and the amount.
  let message : DepositMessage := ⟨pubkey, withdrawalCredentials, amount⟩
  -- The domain at the genesis fork version, with a zero validators root.
  let domain ← liftSsz (computeDomain config domainType)
  let signingRoot ← liftSsz (computeSigningRoot message domain)
  return checks.verify pubkey (packBytes signingRoot) signature

/-- Whether a validator deposit carries the signature of its key, under the deposit domain. -/
def isValidDepositSignature (config : Config) (checks : SignatureChecks) (pubkey : BLSPubkey)
    (withdrawalCredentials : Bytes32) (amount : Gwei) (signature : BLSSignature) :
    Except TransitionError Bool :=
  isValidDepositMessageSignature config checks DOMAIN_DEPOSIT pubkey withdrawalCredentials amount
    signature

/-- Whether a builder deposit carries the signature of its key, under the builder deposit domain.

Its domain type differs from the deposit domain type of validators. -/
def isValidBuilderDepositSignature (config : Config) (checks : SignatureChecks)
    (request : BuilderDepositRequest) : Except TransitionError Bool :=
  isValidDepositMessageSignature config checks DOMAIN_BUILDER_DEPOSIT request.pubkey
    request.withdrawalCredentials request.amount request.signature

/-- Whether the index of a builder may be given to a new builder. -/
def isReusableBuilder (epoch : Epoch) (builder : Builder) : Bool :=
  -- Its withdrawable epoch is at most the epoch, and its balance is 0.
  builder.withdrawableEpoch ≤ epoch && builder.balance == 0

/-- The index of a new builder: the first reusable one, or the end of the registry. -/
def getIndexForNewBuilder (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    Nat :=
  -- The first builder reusable at the current epoch, else the size of the registry.
  let builders := (state.builders gloas).data
  (builders.findIdx? (isReusableBuilder (getCurrentEpoch state))).getD builders.size

/-- The state with a new builder at the index for a new builder.

A chosen position of `2^64` or more is an overflow. -/
def addBuilderToRegistry (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (pubkey : BLSPubkey) (version : UInt8) (executionAddress : ExecutionAddress) (amount : Gwei)
    (slot : Slot) : Except TransitionError (BeaconState preset fork) := do
  -- Its deposit epoch is the epoch of the slot, and its withdrawable epoch `FAR_FUTURE_EPOCH`.
  let builder : Builder :=
    ⟨pubkey, version, executionAddress, amount, computeEpochAtSlot preset slot,
      FAR_FUTURE_EPOCH⟩
  let builders := (state.builders gloas).data
  let index := getIndexForNewBuilder state gloas
  let _ ← liftAccessor (liftArith (ofNatChecked index))
  -- A reused index takes the new builder in place.
  if inside : index < builders.size then return state.putBuilder gloas index inside builder
  -- Else the builder is appended.
  else
    let builders : Builders := ⟨builders.push builder⟩
    return { state with builders := fun _ => builders }

/-- The position of the first builder with a key in the registry, if any. -/
def findBuilderByPubkey (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (pubkey : BLSPubkey) : Option (Fin (state.builders gloas).data.size) :=
  -- The first position whose builder has the key.
  (state.builders gloas).data.findFinIdx? (·.pubkey == pubkey)

/-- The address that the withdrawal credentials of a builder name: their last 20 bytes. -/
def credentialAddress (credentials : Bytes32) : ExecutionAddress :=
  -- Byte `i` of the address is byte `i + 12` of the credentials.
  Vector.ofFn fun i => credentials[i.val + 12]

/-- The state after a builder deposit.

[EIP-8282] states the registration and the top-up.

[EIP-8282]: https://eips.ethereum.org/EIPS/eip-8282#consensus-layer-processing
-/
def processBuilderDepositRequest (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (request : BuilderDepositRequest) : Except TransitionError (BeaconState preset fork) := do
  -- A deposit whose credentials lack the builder prefix changes nothing, a top-up included.
  if isBuilderWithdrawalCredential request.withdrawalCredentials = false then return state
  match findBuilderByPubkey state gloas request.pubkey with
  | none =>
    -- A new key registers a payload builder if the signature is valid, and else changes nothing.
    --
    -- The signature is under the builder deposit domain.
    if ← isValidBuilderDepositSignature config checks request then
      addBuilderToRegistry state gloas request.pubkey PAYLOAD_BUILDER_VERSION
        (credentialAddress request.withdrawalCredentials) request.amount state.slot
    else return state
  | some index =>
    let _ ← liftAccessor (liftArith (ofNatChecked index.val))
    let builder := (state.builders gloas).data[index]
    -- Let `e` be the current epoch.
    --
    -- A builder that has exited with a balance of 0 gets the withdrawable epoch `e + D`.
    --
    -- Here `D` is `MIN_BUILDER_WITHDRAWABILITY_DELAY`.
    let withdrawableEpoch ←
      if builder.withdrawableEpoch ≠ FAR_FUTURE_EPOCH ∧ builder.balance = 0 then
        liftAccessor (liftArith
          (addChecked (getCurrentEpoch state) config.MIN_BUILDER_WITHDRAWABILITY_DELAY))
      else pure builder.withdrawableEpoch
    -- A known key adds the amount to the balance of its builder.
    let balance ← liftAccessor (liftArith (addChecked builder.balance request.amount))
    return state.putBuilder gloas index index.isLt { builder with withdrawableEpoch, balance }

/-- The state after a builder exit request, as [EIP-8282] specifies.

A request that fails one of its conditions changes nothing.

[EIP-8282]: https://eips.ethereum.org/EIPS/eip-8282#consensus-layer-processing
-/
def processBuilderExitRequest (config : Config) (state : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) (request : BuilderExitRequest) :
    Except TransitionError (BeaconState preset fork) := do
  -- The key is that of a builder.
  let some index := findBuilderByPubkey state gloas request.pubkey | return state
  let builderIndex ← liftAccessor (liftArith (ofNatChecked index.val))
  let builder := (state.builders gloas).data[index]
  -- The builder is active.
  unless ← liftAccessor (isActiveBuilder state gloas builderIndex) do return state
  -- The source address of the request is the execution address of the builder.
  unless builder.executionAddress = request.sourceAddress do return state
  -- The builder owes nothing.
  unless (← liftAccessor (getPendingBalanceToWithdrawForBuilder state gloas builderIndex)) = 0 do
    return state
  -- It then starts to exit.
  liftAccessor (initiateBuilderExit config state gloas builderIndex)

end EthLib.Consensus
