module

public import EthLib.Execution.Evm.Instructions.Arithmetic
public import EthLib.Execution.Evm.Instructions.Comparison
public import EthLib.Execution.Evm.Instructions.Bitwise
public import EthLib.Execution.Evm.Instructions.Keccak
public import EthLib.Execution.Evm.Precompiles
public import EthLib.Execution.Evm.Machine.Memory
public import EthLib.Execution.Evm.Words
public import EthLib.Execution.Evm.Gas
public import EthLib.Execution.Evm.Errors
public import EthLib.Execution.Evm.Delegation
public import EthLib.Execution.Evm.Log
public import EthLib.Execution.Evm.TransferLog
public import EthLib.Execution.Evm.Op
public import EthLib.Execution.Evm.Machine.Stack
public import EthLib.Execution.Evm.Environment
public import EthLib.Execution.Evm.Machine.Frame
public import EthLib.Execution.Evm.Step
public import EthLib.Execution.Evm.Instructions.StackN
public import EthLib.Execution.Evm.Instructions.StackOnly
public import EthLib.Execution.Evm.Instructions.MemoryData
public import EthLib.Execution.Evm.Instructions.Return
public import EthLib.Execution.Evm.Instructions.EnvironmentData
public import EthLib.Execution.Evm.Instructions.AccountData
public import EthLib.Execution.Evm.Instructions.LogData
public import EthLib.Execution.Evm.Instructions.TransientStorage
public import EthLib.Execution.Evm.Instructions.Storage
public import EthLib.Execution.Evm.Machine.JumpDest
public import EthLib.Execution.Evm.Instructions.ControlFlow
public import EthLib.Execution.Evm.Measure
public import EthLib.Execution.Evm.Call
public import EthLib.Execution.Evm.Instructions.SelfDestruct
public import EthLib.Execution.Evm.Interpreter

/-!
# `EthLib.Execution.Evm`

The Ethereum Virtual Machine.

Each instruction is the word it pushes, as a function of the words it pops, in the order it pops them.

KECCAK256 reads bytes from memory instead, so it is the word it pushes, as a function of those bytes.

The module holds these parts:

- the precompiled contracts, because only the EVM calls them
- the gas prices and the price of memory
- the opcodes, the stack, the memory and the state of a frame, with the gas meter
- from Glamsterdam, the meter of state gas beside execution gas
- the addresses of the contracts that CREATE and CREATE2 make
- the environments of the block and of the transaction, with the substate
- the loop that runs one frame, with the measure that makes it end
- the execution of a message, with the recursion of messages
-/
