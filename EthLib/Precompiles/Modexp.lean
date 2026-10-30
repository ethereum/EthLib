module

public import EthLib.Precompiles.Modexp.Constants
public import EthLib.Precompiles.Modexp.Bytes
public import EthLib.Precompiles.Modexp.Gas
public import EthLib.Precompiles.Modexp.Errors
public import EthLib.Precompiles.Modexp.Core

/-!
# `EthLib.Precompiles.Modexp`

The MODEXP precompile at address `0x05`, as of the BPO2 fork.

BPO2 is the latest fork activated on mainnet.

The rules come from three EIPs:

- EIP-198: the input and output format, and the arithmetic.
- EIP-7883: the gas price.
- EIP-7823: the upper bound on the three lengths.

EIP-2565 priced the precompile before EIP-7883 and is not specified here.

The executable source is `forks/bpo2/vm/precompiled_contracts/modexp.py`.
It is in `ethereum/execution-specs` at commit `2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1`.
It is identical to the Osaka module, where EIP-7823 and EIP-7883 took effect.
-/
