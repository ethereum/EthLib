import EthLib.Networking.Proofs.Encoding.Varint

/-!
# `EthLib.Networking.Proofs`

Machine-checked properties of the networking specifications. This tree
mirrors the layout of the definitions it proves things about: proofs for
`EthLib.Networking.Foo.Bar` live in `EthLib.Networking.Proofs.Foo.Bar`.

The proofs are compiled by the `Proofs` Lake library, which the runtime
code does not depend on: nothing here is linked into the Python extension.
-/
