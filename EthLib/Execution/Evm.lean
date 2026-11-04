module

public import EthLib.Execution.Evm.Instructions.Arithmetic
public import EthLib.Execution.Evm.Instructions.Comparison
public import EthLib.Execution.Evm.Instructions.Bitwise
public import EthLib.Execution.Evm.Instructions.Keccak
public import EthLib.Execution.Evm.Precompiles
public import EthLib.Execution.Evm.Memory
public import EthLib.Execution.Evm.PowMod
public import EthLib.Execution.Evm.Words
public import EthLib.Execution.Evm.Gas
public import EthLib.Execution.Evm.Errors
public import EthLib.Execution.Evm.Op
public import EthLib.Execution.Evm.Stack
public import EthLib.Execution.Evm.Frame

/-!
# `EthLib.Execution.Evm`

The Ethereum Virtual Machine.

Each instruction is the word it pushes, as a function of the words it pops, in the order it pops them.

KECCAK256 reads bytes from memory instead, so it is the word it pushes, as a function of those bytes.

The precompiled contracts are here too, because only the EVM calls them.

The gas prices and the price of memory are here.

The opcodes, the stack, the memory and the state of a frame are here, with the gas meter.
-/
