module

public import EthLib.Execution.Evm.Precompiles.Modexp.Constants
public import EthLib.Execution.Evm.Precompiles.Modexp.Bytes
public import EthLib.Execution.Evm.Precompiles.Modexp.Gas
public import EthLib.Execution.Evm.Precompiles.Modexp.Errors
public import EthLib.Execution.Evm.Precompiles.Modexp.Core

/-!
# `EthLib.Execution.Evm.Precompiles.Modexp`

The MODEXP precompile at address `0x05`, as of the BPO2 fork.

The rules come from three EIPs:

- EIP-198: the input and output format, and the arithmetic.
- EIP-7883: the gas price.
- EIP-7823: the upper bound on the three lengths.

EIP-2565 priced the precompile before EIP-7883 and is not specified here.

EIP-7823 and EIP-7883 took effect in Osaka, and BPO2 changes only blob parameters.
-/
