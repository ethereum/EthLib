import EthLib.Consensus
import EthLib.Cryptography
import EthLib.Networking
import EthLib.Precompiles

/-!
# `EthLib`

Ethereum specifications, written in Lean.

Each domain lives in its own subtree:

- `EthLib.Consensus` holds the consensus-layer specifications.
- `EthLib.Cryptography` holds the cryptographic primitives.
- `EthLib.Networking` holds the wire formats of the networking layer.
- `EthLib.Precompiles` holds the precompiled contracts of the EVM.
-/
