module

public import EthLib.Consensus.Containers.Misc

/-!
# `Consensus.Credentials`

The kinds of withdrawal credentials of a validator, and what each kind allows.

The first byte of the credentials is a prefix that names their kind.

From Capella, credentials with the execution address prefix let the balance go to that address.

From Electra, compounding credentials also name an address, as [EIP-7251] specifies.

Their effective balance may grow past the activation balance.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

/-- From Capella: whether a validator has credentials that name an execution address.

The first byte of its credentials is the execution address prefix. -/
def hasEth1WithdrawalCredential (validator : Validator) : Bool :=
  validator.withdrawalCredentials[0] == ETH1_ADDRESS_WITHDRAWAL_PREFIX[0]

/-- From Electra: whether withdrawal credentials are compounding.

Their first byte is the compounding prefix. -/
def isCompoundingWithdrawalCredential (credentials : Bytes32) : Bool :=
  credentials[0] == COMPOUNDING_WITHDRAWAL_PREFIX[0]

/-- From Electra: whether a validator has compounding credentials. -/
def hasCompoundingWithdrawalCredential (validator : Validator) : Bool :=
  isCompoundingWithdrawalCredential validator.withdrawalCredentials

/-- From Electra: whether a validator has credentials that name an execution address.

Both the execution address prefix and the compounding prefix name one. -/
def hasExecutionWithdrawalCredential (validator : Validator) : Bool :=
  hasEth1WithdrawalCredential validator || hasCompoundingWithdrawalCredential validator

/-- From Electra: the largest effective balance of a validator.

With compounding credentials it is the largest Electra effective balance.

Otherwise it is the activation balance. -/
def getMaxEffectiveBalance (preset : Preset) (validator : Validator) : Gwei :=
  if hasCompoundingWithdrawalCredential validator then preset.MAX_EFFECTIVE_BALANCE_ELECTRA
  else preset.MIN_ACTIVATION_BALANCE

end EthLib.Consensus
