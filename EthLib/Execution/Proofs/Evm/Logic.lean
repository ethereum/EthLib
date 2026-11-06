module

public import EthLib.Execution.Proofs.Evm.Logic.Reach
public import EthLib.Execution.Proofs.Evm.Logic.Triple
public import EthLib.Execution.Proofs.Evm.Logic.Symbolic
public import EthLib.Execution.Proofs.Evm.Logic.Examples.Return42

/-!
# `EthLib.Execution.Proofs.Evm.Logic`

A program logic over EVM bytecode, for frames that send no message.

It has the frames that a frame reaches, triples over them, rules for opcodes and a worked example.
-/
