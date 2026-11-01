module

public import EthLib.Precompiles.Ecrecover.Errors
public import EthLib.Precompiles.Ecrecover.Core

/-!
# `EthLib.Precompiles.Ecrecover`

The ECRECOVER precompile at address `0x01`, as of the BPO2 fork.

It recovers the secp256k1 public key of an ECDSA signature, and returns its address.
-/
