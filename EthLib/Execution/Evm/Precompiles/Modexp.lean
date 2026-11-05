module

public import EthLib.Execution.Evm.Precompiles.Modexp.Constants
public import EthLib.Execution.Evm.Precompiles.Modexp.Encoding
public import EthLib.Execution.Evm.Precompiles.Modexp.Gas
public import EthLib.Execution.Evm.Precompiles.Modexp.Errors
public import EthLib.Execution.Evm.Precompiles.Modexp.Core

/-!
# `EthLib.Execution.Evm.Precompiles.Modexp`

The MODEXP precompile at address `0x05`, which Byzantium adds, at every fork.

The rules come from four EIPs:

- EIP-198: the input and output format, the arithmetic, and the first price.
- EIP-2565: the price from Berlin.
- EIP-7883: the price from Fusaka.
- EIP-7823: the upper bound on the three lengths, from Fusaka.
-/
