module

public import EthLib.Fees.Proofs.BaseFee
public import EthLib.Fees.Proofs.BlobBaseFee

/-!
# `EthLib.Fees.Proofs`

Machine-checked properties of the fee specifications.

The tree mirrors the definitions it proves things about:

```text
    EthLib.Fees.Foo          the definitions
    EthLib.Fees.Proofs.Foo   the theorems about them
```

The proofs build in their own Lake library.

The runtime code never imports them, so nothing here is linked into the Python extension.
-/
