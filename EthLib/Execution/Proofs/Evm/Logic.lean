module

-- The frames that a frame reaches.
public import EthLib.Execution.Proofs.Evm.Logic.Reach
-- Triples over them.
public import EthLib.Execution.Proofs.Evm.Logic.Triple
public import EthLib.Execution.Proofs.Evm.Logic.Symbolic
-- Rules for loops.
public import EthLib.Execution.Proofs.Evm.Logic.Loop
public import EthLib.Execution.Proofs.Evm.Logic.Subroutine
-- A triple over frames that send messages takes an assumption on the frames that end the messages.
--
-- Its run may also abort, when the runner of messages fails.
public import EthLib.Execution.Proofs.Evm.Logic.Message
-- Another form of triple lets the runner fail with any error.
--
-- It names the messages on which a run may stop because the runner fails.
public import EthLib.Execution.Proofs.Evm.Logic.FailsOn
-- A rule for calls in that form also follows an EIP-7702 delegation to the code of the delegate.
public import EthLib.Execution.Proofs.Evm.Logic.Route
public import EthLib.Execution.Proofs.Evm.Logic.Call
public import EthLib.Execution.Proofs.Evm.Logic.CallSteps
public import EthLib.Execution.Proofs.Evm.Logic.Keeps
public import EthLib.Execution.Proofs.Evm.Logic.Log
public import EthLib.Execution.Proofs.Evm.Logic.Static
public import EthLib.Execution.Proofs.Evm.Logic.Create
public import EthLib.Execution.Proofs.Evm.Logic.Deposit
public import EthLib.Execution.Proofs.Evm.Logic.Callee
-- Rules for opcodes.
public import EthLib.Execution.Proofs.Evm.Logic.Rules
public import EthLib.Execution.Proofs.Evm.Logic.Copy
public import EthLib.Execution.Proofs.Evm.Logic.Region
public import EthLib.Execution.Proofs.Evm.Logic.Known
public import EthLib.Execution.Proofs.Evm.Logic.Slots
public import EthLib.Execution.Proofs.Evm.Logic.Effect
public import EthLib.Execution.Proofs.Evm.Logic.NewAccount
public import EthLib.Execution.Proofs.Evm.Logic.Branch
public import EthLib.Execution.Proofs.Evm.Logic.Stack
-- A code can be stored as one number.
public import EthLib.Execution.Proofs.Evm.Logic.NatCode
-- A tactic steps through the opcodes of a code.
public import EthLib.Execution.Proofs.Evm.Logic.Steps
public import EthLib.Execution.Proofs.Evm.Logic.GasMono
public import EthLib.Execution.Proofs.Evm.Logic.RunMono
public import EthLib.Execution.Proofs.Evm.Logic.NoAbort
public import EthLib.Execution.Proofs.Evm.Logic.Fault
-- By steps monotone in gas, a run with less gas follows the run with more gas, or it fails.
public import EthLib.Execution.Proofs.Evm.Logic.LessGas
-- A specification to frames with no error gives a run that succeeds.
public import EthLib.Execution.Proofs.Evm.Logic.RunsOk
public import EthLib.Execution.Proofs.Evm.Logic.Marks

/-!
# `EthLib.Execution.Proofs.Evm.Logic`

A program logic over EVM bytecode.

Over steps monotone in gas, a specification to a halt fixes the end of every run that succeeds.
-/
