module

public import EthLib.Cryptography.Sphincs.Constants
public import EthLib.Cryptography.Sphincs.Types
public import EthLib.Cryptography.Sphincs.Errors
public import EthLib.Cryptography.Sphincs.Address
public import EthLib.Cryptography.Sphincs.TweakableHash
public import EthLib.Cryptography.Sphincs.Encoding
public import EthLib.Cryptography.Sphincs.Ots
public import EthLib.Cryptography.Sphincs.Tree
public import EthLib.Cryptography.Sphincs.Fors
public import EthLib.Cryptography.Sphincs.Digest
public import EthLib.Cryptography.Sphincs.Verify
public import EthLib.Cryptography.Sphincs.Serialization
public import EthLib.Cryptography.Sphincs.KeyGen
public import EthLib.Cryptography.Sphincs.Sign

/-!
# leanSPHINCS

leanSPHINCS: FORS under a hypertree of WOTS+C keys, three layers of heights 8, 8 and 10.

A stateless hash-based signature for post-quantum Ethereum, for `2^30` signatures per key.

It is SLH-DSA of FIPS 205 on Keccak-256, with WOTS+C as its one-time signature.
-/
