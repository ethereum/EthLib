import EthLib.Cryptography.Sphincs.Fors

/-!
# `Sphincs.Digest`

The message digest, and the randomizer the signer hashes into it.

```text
    R   = H_0(P | A_rnd | S | m)
    D_c = H(P | A_msg(c) | m | R),   c = 0, 1
    D   = D_0 | D_1
```

`D` is read as one 512-bit little-endian number, so `D_0` holds its low 256 bits.

Its low `h + k a = 266` bits are the fields:

```text
    [ idx: 26 | leaf_0: 10 | leaf_1: 10 | ... | leaf_23: 10 ]
```

- `idx` is bits 0 to 25: the bottom leaf, and so the FORS instance and the path up the hypertree.
- `leaf_kappa` is bits `26 + 10 kappa` to `35 + 10 kappa`: the leaf of FORS tree `kappa` that the signature opens.

The index is in `D_0`, and leaf 23 straddles the two calls.

The public key's root is not hashed: `P` already binds the digest to the key.

Source: `deriveRandomizer`, `messageDigest`, `digestIndex` and `digestLeaves` in [FORS/Scheme.lean](https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/formal/sphincs/FORS/Scheme.lean).
-/

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-! ## The randomizer -/

/-- `R`: the randomizer of a message, the first half of one hash of the seed and the message.

The seed is in the input, so the randomizer is unpredictable to anyone without the secret key.

Every index is a leaf of this key, so the first randomizer is always kept.

The note's signer would try `R + i delta` for `i = 1, 2, ...` only if an index could miss the key. -/
def randomizer (pp : PublicParam) (seed : Seed) (m : Message) : Randomizer :=
  th pp addrRnd (packBytes seed ++ packBytes m)

/-! ## The digest -/

/-- The bytes of the message digest: the outputs of its two calls, call 0 first. -/
abbrev MessageDigest := Vector UInt8 (DIGEST_CALLS * HASH_LEN)

/-- `D = D_0 | D_1`, with `D_c = H(P | A_msg(c) | m | R)`.

Each call's input is 80 bytes, one Keccak-256 block. -/
def messageDigest (pp : PublicParam) (m : Message) (rho : Randomizer) : MessageDigest :=
  -- The calls hash the same payload, and only their address differs.
  (Vector.ofFn fun call => thFull pp (addrMsg call) (packBytes m ++ packBytes rho)).flatten

/-- `idx`: the low 26 bits of the digest. -/
def digestIndex (d : MessageDigest) : Nat :=
  fromLittleEndian d % 2 ^ HEIGHT

/-- The leaf of each FORS tree: bits `26 + 10 kappa` to `35 + 10 kappa` of the digest. -/
def digestLeaves (d : MessageDigest) : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES :=
  -- The digest is read once, as one 512-bit little-endian integer.
  let value := fromLittleEndian d
  Vector.ofFn fun kappa =>
    ⟨value / 2 ^ (HEIGHT + FORS_HEIGHT * kappa.val) % 2 ^ FORS_HEIGHT, Nat.mod_lt _ (by decide)⟩

end EthLib.Cryptography.Sphincs
