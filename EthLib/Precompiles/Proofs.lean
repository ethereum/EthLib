import EthLib.Precompiles.Proofs.Modexp
import EthLib.Precompiles.Proofs.Ripemd160

/-!
# `EthLib.Precompiles.Proofs`

Machine-checked properties of the precompile specifications.

The tree mirrors the definitions it proves things about.

The proofs for `EthLib.Precompiles.Foo` live in `EthLib.Precompiles.Proofs.Foo`.

They build in the `Proofs` Lake library, which the library code does not depend on.

So nothing here is linked into the Python extension.
-/
