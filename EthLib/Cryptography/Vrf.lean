module

public import EthLib.Cryptography.Vrf.Constants
public import EthLib.Cryptography.Vrf.Types
public import EthLib.Cryptography.Vrf.Hash
public import EthLib.Cryptography.Vrf.KeyGen
public import EthLib.Cryptography.Vrf.Verify
public import EthLib.Cryptography.Vrf.Serialization

/-!
# The VRF tree

The VRF tree is a Merkle tree over `2^32` leaf secrets.

It fixes one verifiable random output per index.
-/
