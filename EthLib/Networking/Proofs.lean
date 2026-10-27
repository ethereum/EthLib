import EthLib.Networking.Proofs.Encoding.Varint

/-!
# `EthLib.Networking.Proofs`

Machine-checked properties of the networking specifications.

The tree mirrors the definitions it proves things about:

```text
    EthLib.Networking.Foo.Bar          the definitions
    EthLib.Networking.Proofs.Foo.Bar   the theorems about them
```

The proofs build in their own Lake library.

The runtime code never imports them, so nothing here is linked into the Python extension.
-/
