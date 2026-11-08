module

/-!
# leanSPHINCS parameters

The leanSPHINCS parameter set: lifetime `2^30`, Keccak-256, FORS, three layers.

- Few-time signature: FORS, 24 trees of height 10.
- One-time signature: WOTS+C, 64 chains of 4 positions, target sum 128.
- Hypertree: three layers of heights 8, 8 and 10, from the bottom.

Source: the parameter table of [main.tex][main] §2, and its sizes and costs in §6.4.

The note follows [FIPS 205][fips205] except where its §1 says otherwise.

[main]: https://github.com/leanEthereum/leanVM/blob/5e3ade21d339a45e1b3b0dba97ad9300ab50e49b/doc/lean_sphincs/main.tex
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

/-- The permutations of one verification, by the count of main.tex §6.4.

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

/-! ## Identities the parameter set must satisfy -/

/-- A chain has `2^w` positions. -/
theorem chain_length_eq : CHAIN_LENGTH = 2 ^ W := by decide

/-- A digest is exactly 64 digits of 2 bits. -/
theorem digits_fill_digest : W * V = 8 * N := by decide

/-- The target sum is reachable: it does not exceed the maximum digit sum. -/
theorem target_sum_le_max : TARGET_SUM ≤ V * (CHAIN_LENGTH - 1) := by decide

/-- The verifier's step count is what the target sum leaves unwalked. -/
theorem chain_hashes_eq : V * (CHAIN_LENGTH - 1) - TARGET_SUM = CHAIN_HASHES := by decide

/-- An index has 26 bits: `8 + 8 + 10`. -/
theorem height_eq : HEIGHT = 26 := by decide

/-- The lifetime is within the model's proved limit of 1,182,000,000 signatures. -/
theorem signature_limit_le : SIGNATURE_LIMIT ≤ 1182000000 := by decide

/-- The digest has `m = 34` bytes: 30 for the FORS leaves, 3 for the tree, 1 for the leaf. -/
theorem digest_bytes_eq :
    MD_BYTES = 30 ∧ TREE_INDEX_BYTES = 3 ∧ LEAF_INDEX_BYTES = 1 ∧ DIGEST_BYTES = 34 := by
  decide

/-- Two Keccak-256 calls give the 34 bytes of the digest, and one would not. -/
theorem digest_calls_eq :
    DIGEST_CALLS = 2 ∧ HASH_LEN < DIGEST_BYTES ∧ DIGEST_BYTES ≤ DIGEST_CALLS * HASH_LEN := by
  decide

/-- The FORS leaves fill `md` exactly: 24 leaves of 10 bits are 30 bytes. -/
theorem fors_leaves_fill_md : FORS_TREES * FORS_HEIGHT = 8 * MD_BYTES := by decide

/-- The tree index and the bottom leaf fit their bytes. -/
theorem index_fields_fit :
    HEIGHT - LOWER_HEIGHT ≤ 8 * TREE_INDEX_BYTES ∧ LOWER_HEIGHT ≤ 8 * LEAF_INDEX_BYTES := by
  decide

/-- A FORS tree index `kappa 2^a + s` fits the 32-bit word of the address. -/
theorem fors_tree_index_fits : FORS_TREES * 2 ^ FORS_HEIGHT ≤ 2 ^ 32 := by decide

/-- A tree number of any layer fits the 64 bits that the tree address holds. -/
theorem tree_fits : 2 ^ (HEIGHT - LOWER_HEIGHT) ≤ 2 ^ 64 := by decide

/-- A leaf of any layer fits the 32-bit key pair word of the address. -/
theorem leaf_fits : 2 ^ TOP_HEIGHT ≤ 2 ^ 32 := by decide

/-- The framed message is 45 bytes. -/
theorem framed_len_eq : FRAMED_LEN = 45 := by decide

/-- The advertised public key size. -/
theorem pub_key_size_eq : PUB_KEY_SIZE = 32 := by decide

/-- The advertised FORS opening size: 24 trees of 176 bytes. -/
theorem fors_size_eq : FORS_TREES * TREE_OPENING_SIZE = 4224 := by decide

/-- The advertised size of a lower layer's signature. -/
theorem lower_layer_sig_size_eq : layerSigSize LOWER_HEIGHT = 1156 := by decide

/-- The advertised size of the top layer's signature. -/
theorem top_layer_sig_size_eq : layerSigSize TOP_HEIGHT = 1188 := by decide

/-- The advertised signature size, `7740` bytes, as in main.tex §6.4.

It is `n + k (1 + a) n + d (4 + v n) + h n`. -/
theorem sig_size_eq : SIG_SIZE = 7740 ∧
    SIG_SIZE = N + FORS_TREES * (1 + FORS_HEIGHT) * N + LAYERS * (COUNTER_LEN + V * N)
      + HEIGHT * N := by
  decide

/-- The advertised verification cost, `515` permutations, as in main.tex §6.4.

It is `2 + k (1 + a) + 4 + d + d ((2^w - 1) v - T + 8) + h`. -/
theorem verify_permutations_eq : VERIFY_PERMUTATIONS = 515 ∧
    VERIFY_PERMUTATIONS = 2 + FORS_TREES * (1 + FORS_HEIGHT) + 4 + LAYERS
      + LAYERS * (CHAIN_HASHES + 8) + HEIGHT := by
  decide

/-- The scheme's name is these 11 bytes. -/
theorem seed_tag_eq :
    SEED_TAG = [0x6c, 0x65, 0x61, 0x6e, 0x53, 0x50, 0x48, 0x49, 0x4e, 0x43, 0x53] := by
  decide

end EthLib.Cryptography.Sphincs.Constants
