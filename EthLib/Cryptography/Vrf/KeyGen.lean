import EthLib.Cryptography.Vrf.Tree

/-!
# `Vrf.KeyGen`

A whole tree from one 32-byte seed.

```text
    s_i = keccak256(PQ_VRF_SECRET | seed | LE32(i))
```

The holder stores the seed, not the `2^32` secrets.

It recomputes a secret, or a subtree, when it opens an index.

Verification never sees the seed, so this derivation is not consensus-critical.

It is specified so that any implementation rebuilds the same tree from the same seed.

The draft leaves this derivation to the holder, so it is EthLib's own.

It is the pseudorandom key generation of RFC 8391, `sk[i] = PRF(S, i)`, with Keccak-256 keyed by a prefix.

Source: [RFC 8391](https://www.rfc-editor.org/rfc/rfc8391) §3.1.7 and §5.1.
-/

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants

/-- The bytes a secret hash reads: the secret prefix, the seed, then the index. -/
def secretInput (seed : Seed) (i : UInt32) : ByteArray :=
  packBytes VRF_SECRET_DST ++ packBytes seed ++ packBytes (indexBytes i)

/-- `s_i`: the secret of leaf `i`. -/
def secret (seed : Seed) (i : UInt32) : Digest :=
  hash (secretInput seed i)

/-- The root of the tree of a seed: what the holder publishes.

The seed must be 32 uniformly random bytes, kept secret. -/
def keyGen (seed : Seed) : Digest :=
  root (secret seed)

/-- The opening at index `i` of the tree of a seed. -/
def prove (seed : Seed) (i : UInt32) : Opening :=
  opening (secret seed) i

/-- The output at index `i` of the tree of a seed. -/
def evaluate (seed : Seed) (i : UInt32) : Digest :=
  outputHash (secret seed i)

end EthLib.Cryptography.Vrf
