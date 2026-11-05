module

public import EthLib.Execution.Exports.Blocks
public import EthLib.Execution.Exports.Evm
public import EthLib.Execution.Exports.Proofs.Evm
public import EthLib.Execution.Exports.Fees
public import EthLib.Execution.Exports.Network
public import EthLib.Execution.Exports.Snap
public import EthLib.Execution.Exports.Pow
public import EthLib.Execution.Exports.Precompiles
public import EthLib.Execution.Exports.State
public import EthLib.Execution.Exports.Transactions
public import EthLib.Execution.Exports.Transition
public import EthLib.Execution.Exports.Trie

/-!
# `EthLib.Execution.Exports`

The C exports of the execution layer, for the Python bindings.

They are compiled by the `Exports` Lake library.
The specification does not import them, so a Lean project that imports `EthLib` gets no `@[export]` symbol.
-/
