import EthLib.Cryptography.Proofs.Bls
import EthLib.Cryptography.Proofs.Kzg
import EthLib.Cryptography.Proofs.Xmss

/-!
# `EthLib.Cryptography.Proofs`

Machine-checked properties of the executable specification. This tree
mirrors the layout of the definitions it proves things about: proofs for
`EthLib.Cryptography.Foo.Bar` live in `EthLib.Cryptography.Proofs.Foo.Bar`.

The proofs are compiled by the `Proofs` Lake library, which the runtime
code does not depend on: nothing here is linked into the Python extension.
-/
