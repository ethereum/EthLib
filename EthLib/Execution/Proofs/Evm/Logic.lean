module

public import EthLib.Execution.Proofs.Evm.Logic.Reach
public import EthLib.Execution.Proofs.Evm.Logic.Triple
public import EthLib.Execution.Proofs.Evm.Logic.Symbolic
public import EthLib.Execution.Proofs.Evm.Logic.Loop
public import EthLib.Execution.Proofs.Evm.Logic.Subroutine
public import EthLib.Execution.Proofs.Evm.Logic.Message
public import EthLib.Execution.Proofs.Evm.Logic.FailsOn
public import EthLib.Execution.Proofs.Evm.Logic.Route
public import EthLib.Execution.Proofs.Evm.Logic.Call
public import EthLib.Execution.Proofs.Evm.Logic.Log
public import EthLib.Execution.Proofs.Evm.Logic.Static
public import EthLib.Execution.Proofs.Evm.Logic.Create
public import EthLib.Execution.Proofs.Evm.Logic.Deposit
public import EthLib.Execution.Proofs.Evm.Logic.Callee
public import EthLib.Execution.Proofs.Evm.Logic.Rules
public import EthLib.Execution.Proofs.Evm.Logic.Copy
public import EthLib.Execution.Proofs.Evm.Logic.Region
public import EthLib.Execution.Proofs.Evm.Logic.Known
public import EthLib.Execution.Proofs.Evm.Logic.Slots
public import EthLib.Execution.Proofs.Evm.Logic.Effect
public import EthLib.Execution.Proofs.Evm.Logic.NewAccount
public import EthLib.Execution.Proofs.Evm.Logic.Branch
public import EthLib.Execution.Proofs.Evm.Logic.Stack
public import EthLib.Execution.Proofs.Evm.Logic.NatCode
public import EthLib.Execution.Proofs.Evm.Logic.Steps
public import EthLib.Execution.Proofs.Evm.Logic.Fault
public import EthLib.Execution.Proofs.Evm.Logic.LessGas

/-!
# `EthLib.Execution.Proofs.Evm.Logic`

A program logic over EVM bytecode.

It has the frames that a frame reaches, triples over them, rules for opcodes and for loops.

A triple over frames that send messages takes an assumption on the frames that end the messages.

Its run may also abort, when the runner of messages fails.

Another form of triple lets the runner fail with any error.

It names the messages on which a run may stop because the runner fails.

A rule for calls in that form also follows an EIP-7702 delegation to the code of the delegate.

A code can be stored as one number, and a tactic steps through its opcodes.

With the one-counter meter, a run with less gas follows the run with more gas, or it fails.
-/
