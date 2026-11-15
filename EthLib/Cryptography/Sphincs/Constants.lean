module

/-!
# leanSPHINCS parameters

The leanSPHINCS parameter set: lifetime `2^30`, Keccak-256, FORS, three layers.

- Few-time signature: FORS, 24 trees of height 10.
- One-time signature: WOTS+C, 64 chains of 4 positions, target sum 128.
- Hypertree: three layers of heights 8, 8 and 10, from the bottom.

Source: the layered key of `2^30` in [leanSPHINCS.tex][note] §1, with FORS of 24 trees of height 10.

The layout is that of [FIPS 205][fips205], except where a file says otherwise.

[note]: https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/leanSPHINCS.tex
[fips205]: https://doi.org/10.6028/NIST.FIPS.205
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Constants

/-! ## Hash and object sizes -/

/-- `n`: the length in bytes of a hash value, of `PK.seed` and of a Merkle node.

128 bits, the security parameter of the SLH-DSA parameter sets at NIST level 1. -/
def N : Nat := 16

/-- The length in bytes of an address `ADRS`: eight 32-bit words, as in FIPS 205 §4.2. -/
def ADRS_LEN : Nat := 32

/-- The bytes before the payload of an addressed hash: `PK.seed | ADRS`. -/
def PREFIX_LEN : Nat := N + ADRS_LEN

/-- The message length in bytes.

leanSPHINCS signs a 256-bit message hash, so the caller hashes the real message first. -/
def MESSAGE_LEN : Nat := 32

/-- The length in bytes of the randomizer `R`, which is `n`.

It is hashed with the message into the digest that picks the FORS instance and its leaves. -/
def RANDOMIZER_LEN : Nat := N

/-- The length in bytes of `SK.seed`, the whole secret key. -/
def SEED_LEN : Nat := 32

/-- The scheme's name, `"leanSPHINCS"` in ASCII.

It is hashed before `SK.seed` in the key expansion, and it is the context of `PRF_msg`. -/
def SEED_TAG : List UInt8 := "leanSPHINCS".toList.map fun c => UInt8.ofNat c.toNat

/-- The length in bytes of a WOTS+C counter, a big-endian 32-bit word. -/
def COUNTER_LEN : Nat := 4

/-- The length in bytes of one output of Keccak-256, and of `SK.prf`. -/
def HASH_LEN : Nat := 32

/-- The length in bytes of the framed message `M' = 0x00 | len(ctx) | ctx | M` of `PRF_msg`. -/
def FRAMED_LEN : Nat := 2 + SEED_TAG.length + MESSAGE_LEN

/-! ## WOTS+C -/

/-- `w`: the bits of a chain position, FIPS 205's `lg_w`. -/
def W : Nat := 2

/-- The positions of one hash chain, `2^w = 4`, from `0` to `3`.

A digit of `w = 2` bits names one of them. -/
def CHAIN_LENGTH : Nat := 4

/-- `v`: the chains of one one-time key, `8n / w`.

A 16-byte digest has 128 bits, so it carries exactly 64 digits of 2 bits. -/
def V : Nat := 64

/-- `T`: the sum of the digits of a codeword.

It replaces the Winternitz checksum.

`128` is above the mean digit sum `96`, so the verifier walks fewer steps.

The signer pays with about 14,670 counter trials per one-time signature. -/
def TARGET_SUM : Nat := 128

/-- Chain steps one verification walks for one one-time signature, `(2^w - 1) v - T`.

The digit sum is fixed, so the count is fixed. -/
def CHAIN_HASHES : Nat := 64

/-- `C_max`: the counters a one-time signature may try.

A counter is a 32-bit word, so `2^32` is every counter there is. -/
def MAX_COUNTER_TRIALS : Nat := 2 ^ 32

/-! ## The hypertree -/

/-- `h_2`: the height of the top layer's one tree. -/
def TOP_HEIGHT : Nat := 10

/-- `h_0 = h_1`: the height of each tree on the two layers below the top. -/
def LOWER_HEIGHT : Nat := 8

/-- `d`: the layers of the hypertree. -/
def LAYERS : Nat := 3

/-- `h = h_0 + h_1 + h_2`: the bits of an index.

An index names a bottom leaf, and the FORS instance under it. -/
def HEIGHT : Nat := TOP_HEIGHT + 2 * LOWER_HEIGHT

/-! ## FORS -/

/-- `k`: the trees of one FORS instance. -/
def FORS_TREES : Nat := 24

/-- `a`: the height of each FORS tree, so each tree has `2^10 = 1024` leaves. -/
def FORS_HEIGHT : Nat := 10

/-! ## The message digest

FIPS 205 Algorithm 19 splits the digest into three fields of whole bytes. -/

/-- The bytes of `md`, the FORS leaves: `ceil(k a / 8) = 30`. -/
def MD_BYTES : Nat := (FORS_TREES * FORS_HEIGHT + 7) / 8

/-- The bytes of the tree index: `ceil((h - h_0) / 8) = 3`. -/
def TREE_INDEX_BYTES : Nat := (HEIGHT - LOWER_HEIGHT + 7) / 8

/-- The bytes of the bottom leaf index: `ceil(h_0 / 8) = 1`. -/
def LEAF_INDEX_BYTES : Nat := (LOWER_HEIGHT + 7) / 8

/-- `m`: the bytes of `H_msg`, the three fields together. -/
def DIGEST_BYTES : Nat := MD_BYTES + TREE_INDEX_BYTES + LEAF_INDEX_BYTES

/-- The Keccak-256 calls of `H_msg`, `ceil(m / 32)`.

34 bytes need two calls of 32 bytes. -/
def DIGEST_CALLS : Nat := (DIGEST_BYTES + HASH_LEN - 1) / HASH_LEN

/-! ## The signature limit -/

/-- The signatures one key may make: the lifetime `2^30`.

The parameters target their security level only up to this many signatures.

Each signature from a reused FORS instance weakens it, so the level falls past the limit.

The signer does not count its signatures, so the caller must. -/
def SIGNATURE_LIMIT : Nat := 2 ^ 30

/-! ## Serialized sizes -/

/-- Bytes in a serialized public key: `PK.seed`, then `PK.root`. -/
def PUB_KEY_SIZE : Nat := 2 * N

/-- Bytes in one FORS tree's opening: the secret, then `a` path nodes.

An abbreviation, so an opening's bytes have this type by definition. -/
abbrev TREE_OPENING_SIZE : Nat := N + FORS_HEIGHT * N

/-- Bytes in one layer's signature of height `height`: counter, chain values, path. -/
def layerSigSize (height : Nat) : Nat := COUNTER_LEN + V * N + height * N

/--
Bytes in a serialized signature.

It holds the randomizer, the FORS opening, then the three layers from the bottom up.
-/
def SIG_SIZE : Nat :=
  RANDOMIZER_LEN + FORS_TREES * TREE_OPENING_SIZE
    + 2 * layerSigSize LOWER_HEIGHT + layerSigSize TOP_HEIGHT

/-! ## The cost of verification -/

/-- The bytes Keccak-256 absorbs per permutation of Keccak-f[1600], its rate. -/
def KECCAK_RATE : Nat := 136

/-- The permutations Keccak-256 makes on an input of `len` bytes: `floor(len / 136) + 1`. -/
def permutations (len : Nat) : Nat := len / KECCAK_RATE + 1

/-- The permutations of one verification, counted call by call.

- `H_msg`: two calls of 84 bytes.
- FORS: per tree, a leaf of 64 bytes and `a` nodes of 80 bytes.
- `T_k` over the 24 roots: 432 bytes.
- Encodings: one of 68 bytes per layer.
- Chains: `(2^w - 1) v - T = 64` steps of 64 bytes per layer.
- `T_v` over 64 chain ends: 1072 bytes per layer.
- Paths: `h` nodes of 80 bytes.
-/
def VERIFY_PERMUTATIONS : Nat :=
  DIGEST_CALLS * permutations (3 * N + MESSAGE_LEN + COUNTER_LEN)
    + FORS_TREES * (permutations (PREFIX_LEN + N) + FORS_HEIGHT * permutations (PREFIX_LEN + 2 * N))
    + permutations (PREFIX_LEN + FORS_TREES * N)
    + LAYERS * permutations (PREFIX_LEN + N + COUNTER_LEN)
    + LAYERS * (CHAIN_HASHES + permutations (PREFIX_LEN + V * N))
    + HEIGHT * permutations (PREFIX_LEN + 2 * N)

end EthLib.Cryptography.Sphincs.Constants
