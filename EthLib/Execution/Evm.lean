module

public import EthLib.Execution.Evm.Instructions.Arithmetic
public import EthLib.Execution.Evm.Instructions.Comparison
public import EthLib.Execution.Evm.Instructions.Bitwise
public import EthLib.Execution.Evm.Instructions.Keccak
public import EthLib.Execution.Evm.Precompiles
public import EthLib.Execution.Evm.Machine.Memory
public import EthLib.Execution.Evm.Instructions.PowMod
public import EthLib.Execution.Evm.Machine.Words
public import EthLib.Execution.Evm.Gas
public import EthLib.Execution.Evm.Machine.Errors
public import EthLib.Execution.Evm.Op
public import EthLib.Execution.Evm.Machine.Stack
public import EthLib.Execution.Evm.Call.Delegation
public import EthLib.Execution.Evm.Environment
public import EthLib.Execution.Evm.Machine.Frame
public import EthLib.Execution.Evm.Gas.StateGas
public import EthLib.Execution.Evm.Step
public import EthLib.Execution.Evm.Instructions.StackN
public import EthLib.Execution.Evm.Instructions.StackOnly
public import EthLib.Execution.Evm.Instructions.MemoryData
public import EthLib.Execution.Evm.Instructions.Return
public import EthLib.Execution.Evm.Gas.CallGas
public import EthLib.Execution.Evm.Instructions.EnvironmentData
public import EthLib.Execution.Evm.Instructions.AccountData
public import EthLib.Execution.Evm.Call.ContractAddress
public import EthLib.Execution.Evm.Instructions.LogData
public import EthLib.Execution.Evm.Instructions.TransientStorage
public import EthLib.Execution.Evm.Instructions.Storage
public import EthLib.Execution.Evm.Machine.JumpDest
public import EthLib.Execution.Evm.Instructions.ControlFlow
public import EthLib.Execution.Evm.Measure
public import EthLib.Execution.Evm.Call
public import EthLib.Execution.Evm.Call.Create
public import EthLib.Execution.Evm.Instructions.SelfDestruct
public import EthLib.Execution.Evm.Call.TransferLog
public import EthLib.Execution.Evm.Interpreter
public import EthLib.Execution.Evm.Call.MessageCall

/-!
# `EthLib.Execution.Evm`

The Ethereum Virtual Machine.

Each instruction is the word it pushes, as a function of the words it pops, in the order it pops them.

KECCAK256 reads bytes from memory instead, so it is the word it pushes, as a function of those bytes.

The precompiled contracts are here too, because only the EVM calls them.

The gas prices and the price of memory are here.

The opcodes, the stack, the memory and the state of a frame are here, with the gas meter.

From Glamsterdam, the meter of state gas beside execution gas is here too.

The addresses of the contracts that CREATE and CREATE2 make are here.

The environments of the block and of the transaction are here, with the substate.

The loop that runs one frame is here, with the measure that makes it end.

The execution of a message is here, with the recursion of messages.
-/
