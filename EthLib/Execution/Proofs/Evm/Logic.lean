module

public import EthLib.Execution.Proofs.Evm.Logic.Reach
public import EthLib.Execution.Proofs.Evm.Logic.Triple
public import EthLib.Execution.Proofs.Evm.Logic.Symbolic
public import EthLib.Execution.Proofs.Evm.Logic.Loop
public import EthLib.Execution.Proofs.Evm.Logic.Message
public import EthLib.Execution.Proofs.Evm.Logic.Call
public import EthLib.Execution.Proofs.Evm.Logic.Callee
public import EthLib.Execution.Proofs.Evm.Logic.Rules
public import EthLib.Execution.Proofs.Evm.Logic.Examples.Return42
public import EthLib.Execution.Proofs.Evm.Logic.Examples.SlotOfCalldata
public import EthLib.Execution.Proofs.Evm.Logic.Examples.SumLoop
public import EthLib.Execution.Proofs.Evm.Logic.Examples.CallFlag
public import EthLib.Execution.Proofs.Evm.Logic.Examples.CallReturn42
public import EthLib.Execution.Proofs.Evm.Logic.Examples.CallChain
public import EthLib.Execution.Proofs.Evm.Logic.Examples.CallEcho

/-!
# `EthLib.Execution.Proofs.Evm.Logic`

A program logic over EVM bytecode.

It has the frames that a frame reaches, triples over them, rules for opcodes and for loops.

A triple over frames that send messages takes an assumption on the frames that end the messages.

Its run may also abort, when the runner of messages fails.

Worked examples prove whole contracts.
-/
