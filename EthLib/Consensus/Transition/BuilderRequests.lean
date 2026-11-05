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
  let message : DepositMessage := ⟨pubkey, withdrawalCredentials, amount⟩
  let domain ← liftSsz (computeDomain config domainType)
  let signingRoot ← liftSsz (computeSigningRoot message domain)
  return checks.verify (packBytes pubkey) (packBytes signingRoot) (packBytes signature)

/-- Whether a validator deposit carries the signature of its key, under the deposit domain. -/
def isValidDepositSignature (config : Config) (checks : SignatureChecks) (pubkey : BLSPubkey)
    (withdrawalCredentials : Bytes32) (amount : Gwei) (signature : BLSSignature) :
    Except TransitionError Bool :=
  isValidDepositMessageSignature config checks DOMAIN_DEPOSIT pubkey withdrawalCredentials amount
    signature

/-- Whether a builder deposit carries the signature of its key, under the builder deposit domain.

That domain differs from the deposit domain, so no signature serves both deposits. -/
def isValidBuilderDepositSignature (config : Config) (checks : SignatureChecks)
    (request : BuilderDepositRequest) : Except TransitionError Bool :=
  isValidDepositMessageSignature config checks DOMAIN_BUILDER_DEPOSIT request.pubkey
    request.withdrawalCredentials request.amount request.signature

/-- Whether the index of a builder may be given to a new builder.

The builder must be withdrawable in an epoch, with nothing left of its balance. -/
def isReusableBuilder (epoch : Epoch) (builder : Builder) : Bool :=
  builder.withdrawableEpoch ≤ epoch && builder.balance == 0

/-- The index of a new builder: the first reusable one, or the end of the registry. -/
def getIndexForNewBuilder (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    Nat :=
  let builders := (state.builders gloas).data
  (builders.findIdx? (isReusableBuilder (getCurrentEpoch state))).getD builders.size

/-- The state with a new builder at the index for a new builder.

It deposits in the epoch of a slot, and does not exit. -/
def addBuilderToRegistry (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (pubkey : BLSPubkey) (version : UInt8) (executionAddress : ExecutionAddress) (amount : Gwei)
    (slot : Slot) : BeaconState preset fork :=
  let builder : Builder :=
    ⟨pubkey, version, executionAddress, amount, computeEpochAtSlot preset slot,
      FAR_FUTURE_EPOCH⟩
  let builders := (state.builders gloas).data
  let index := getIndexForNewBuilder state gloas
  if index < builders.size then state.setBuilder index builder
  else { state with builders := fun _ => ⟨builders.push builder⟩ }

/-- The position of the first builder with a key in the registry, if any. -/
def findBuilderByPubkey (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (pubkey : BLSPubkey) : Option (Fin (state.builders gloas).data.size) :=
  (state.builders gloas).data.findFinIdx? (·.pubkey == pubkey)

/-- The address that the withdrawal credentials of a builder name: their last 20 bytes. -/
def credentialAddress (credentials : Bytes32) : ExecutionAddress :=
  Vector.ofFn fun i => credentials[i.val + 12]

/-- The state after a builder deposit.

A deposit without the builder prefix changes nothing.

A deposit to a new key registers a payload builder if its signature is valid, and else nothing.

A deposit to a known key adds to the balance of its builder.

If that builder has exited and has no balance left, its exit moves to a fixed delay from now. -/
def processBuilderDepositRequest (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (request : BuilderDepositRequest) : Except TransitionError (BeaconState preset fork) := do
  if isBuilderWithdrawalCredential request.withdrawalCredentials = false then return state
  match findBuilderByPubkey state gloas request.pubkey with
  | none =>
    if ← isValidBuilderDepositSignature config checks request then
      return addBuilderToRegistry state gloas request.pubkey PAYLOAD_BUILDER_VERSION
        (credentialAddress request.withdrawalCredentials) request.amount state.slot
    else return state
  | some index =>
    let builder := (state.builders gloas).data[index]
    let withdrawableEpoch ←
      if builder.withdrawableEpoch ≠ FAR_FUTURE_EPOCH ∧ builder.balance = 0 then
        liftAccessor (liftArith
          (addChecked (getCurrentEpoch state) config.MIN_BUILDER_WITHDRAWABILITY_DELAY))
      else pure builder.withdrawableEpoch
    let balance ← liftAccessor (liftArith (addChecked builder.balance request.amount))
    return state.setBuilder index { builder with withdrawableEpoch, balance }

/-- The state after a builder exit request.

The request must name a known key, from the address of its builder.

That builder must be active and owe nothing; it then starts to exit.

A request that fails one of these conditions changes nothing. -/
def processBuilderExitRequest (config : Config) (state : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) (request : BuilderExitRequest) :
    Except TransitionError (BeaconState preset fork) := do
  let some index := findBuilderByPubkey state gloas request.pubkey | return state
  let builderIndex := index.val.toUInt64
  let builder := (state.builders gloas).data[index]
  unless ← liftAccessor (isActiveBuilder state gloas builderIndex) do return state
  unless builder.executionAddress = request.sourceAddress do return state
  unless (← liftAccessor (getPendingBalanceToWithdrawForBuilder state gloas builderIndex)) = 0 do
    return state
  liftAccessor (initiateBuilderExit config state gloas builderIndex)

end EthLib.Consensus
