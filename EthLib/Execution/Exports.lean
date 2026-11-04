module

public import EthLib.Execution.Exports.Blocks
public import EthLib.Execution.Exports.Modexp
public import EthLib.Execution.Exports.Ripemd160
public import EthLib.Execution.Exports.Sha256
public import EthLib.Execution.Exports.Ecrecover
public import EthLib.Execution.Exports.Precompiles
public import EthLib.Execution.Exports.State

/-!
# `EthLib.Execution.Exports`

The C exports of the execution layer, for the Python bindings.

They are compiled by the `Exports` Lake library.
The specification does not import them, so a Lean project that imports `EthLib` gets no `@[export]` symbol.
-/
