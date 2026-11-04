module

public import EthLib.Execution.Proofs.Blocks
public import EthLib.Execution.Proofs.Evm
public import EthLib.Execution.Proofs.Fees
public import EthLib.Execution.Proofs.Network
public import EthLib.Execution.Proofs.State
public import EthLib.Execution.Proofs.Transactions
public import EthLib.Execution.Proofs.Trie

/-!
# `EthLib.Execution.Proofs`

Machine-checked properties of the execution-layer specifications.

The tree mirrors the definitions it proves things about.

The proofs for `EthLib.Execution.Foo` live in `EthLib.Execution.Proofs.Foo`.

They build in the `Proofs` Lake library, which the library code does not depend on.

So nothing here is linked into the Python extension.
-/
