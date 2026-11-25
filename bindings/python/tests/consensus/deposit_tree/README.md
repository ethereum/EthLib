# EIP-4881 deposit tree test cases

`test_cases.yaml` holds the 512 test cases of EIP-4881, the deposit contract snapshot interface.
Each case is one deposit: its data, the root of that data, and the deposit data of the execution block that holds it.
It also gives the snapshot that a tree finalized at that block takes, after every deposit up to this one.
The suite pushes the roots in order, and checks every deposit root and snapshot against them.

- Repository: [`ethereum/EIPs`](https://github.com/ethereum/EIPs).
- Commit: `b055feec322fbc37e9d77a393a50b3ff56b31c92`.
- File: `assets/eip-4881/test_cases.yaml`.
- Licence: CC0-1.0, as the EIP states.

The file is copied byte for byte, and `SHA256SUMS` pins it.
To check the pin, run this from the directory:

```text
sha256sum -c SHA256SUMS
```
