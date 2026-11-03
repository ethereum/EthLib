module

public import EthLib.Execution.Evm.Precompiles.Ecrecover.Errors
public import EthLib.Execution.Evm.Precompiles.Ecrecover.Core

/-!
# `EthLib.Execution.Evm.Precompiles.Ecrecover`

The ECRECOVER precompile at address `0x01`, as of the BPO2 fork.

It recovers the secp256k1 public key of an ECDSA signature, and returns its address.
-/
