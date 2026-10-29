/-!
# `Sphincs.Constants`

The leanSPHINCS parameter set: lifetime `2^30`, Keccak-256, FORS, layered.

- Few-time signature: FORS, 24 trees of height 10.
- One-time signature: WOTS+C, 64 chains of 4 positions, target sum 128.
- Hypertree: three layers of heights 10, 8 and 8, top first.

Source: the layered key of `2^30` in [leanSPHINCS.tex](https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/leanSPHINCS.tex) §1, which is `Params.layered 26 3 8 24 10` in [FORS/Scheme.lean](https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/formal/sphincs/FORS/Scheme.lean).
-/

namespace EthLib.Cryptography.Sphincs.Constants

/-! ## Hash and object sizes -/

/-- The hash value and Merkle node length in bytes, `n`.

128 bits, the digest size of the SLH-DSA parameter sets at NIST level 1. -/
def N : Nat := 16

/-- The public parameter length in bytes.

It is hashed into every call, which separates one key's hashes from another's. -/
def PUBLIC_PARAM_LEN : Nat := 16

/-- The address length in bytes.

An address separates the call sites of one key. -/
def ADDRESS_LEN : Nat := 16

/-- The message length in bytes.

leanSPHINCS signs a 256-bit message hash, so the caller hashes the real message first. -/
def MESSAGE_LEN : Nat := 32

/-- The randomizer length in bytes.

It is hashed with the message into the digest that picks the FORS instance and its leaves. -/
def RANDOMIZER_LEN : Nat := 16

/-- The secret key length in bytes.

The secret key is one uniform seed, and every other secret derives from it. -/
def SEED_LEN : Nat := 32

/-- The length in bytes of a WOTS+C counter, a little-endian 32-bit word. -/
def COUNTER_LEN : Nat := 4

/-- The length in bytes of one output of Keccak-256. -/
def HASH_LEN : Nat := 32

/-! ## WOTS+C -/

/-- The positions of one hash chain, `0` to `3`, so `w = 4`.

A digit of 2 bits names one of them. -/
def CHAIN_LENGTH : Nat := 4

/-- The chains of one one-time key, `v`.

A 16-byte digest has 128 bits, so it carries exactly 64 digits of 2 bits. -/
def V : Nat := 64

/-- The sum of a codeword's digits, `T`.

It replaces the Winternitz checksum.

`128` is above the mean digit sum `96`, so the verifier walks fewer steps.

The signer pays with about 14,700 counter trials per one-time signature. -/
def TARGET_SUM : Nat := 128

/-- Chain steps one verification walks for one one-time signature, `3v - T`.

The digit sum is fixed, so the count is fixed. -/
def CHAIN_HASHES : Nat := 64

/-- The counters a one-time signature may try, `C_max`.

A counter is a 32-bit word, so `2^32` is every counter there is. -/
def MAX_COUNTER_TRIALS : Nat := 2 ^ 32

/-! ## The hypertree -/

/-- The height of the top layer's one tree. -/
def TOP_HEIGHT : Nat := 10

/-- The height of each tree on the two layers below the top. -/
def LOWER_HEIGHT : Nat := 8

/-- The layers of the hypertree, `d`. -/
def LAYERS : Nat := 3

/-- The bits of an index, `h`: the three layers' heights added.

An index names a bottom leaf, and the FORS instance under it. -/
def HEIGHT : Nat := TOP_HEIGHT + 2 * LOWER_HEIGHT

/-! ## FORS -/

/-- The trees of one FORS instance, `k`.

The note takes 24 trees of height 10 for every lifetime from `2^28` up. -/
def FORS_TREES : Nat := 24

/-- The height of each FORS tree, `a`: each tree has `2^10 = 1024` leaves. -/
def FORS_HEIGHT : Nat := 10

/-! ## The message digest -/

/-- The bits of the message digest that are read: the index, then one leaf per FORS tree.

```text
    h + k a = 26 + 24 * 10 = 266
```
-/
def DIGEST_BITS : Nat := HEIGHT + FORS_TREES * FORS_HEIGHT

/-- The Keccak-256 calls that give the digest, `ceil((h + k a) / 256)`.

266 bits need two calls of 256 bits. -/
def DIGEST_CALLS : Nat := (DIGEST_BITS + 8 * HASH_LEN - 1) / (8 * HASH_LEN)

/-! ## The signature limit -/

/-- The signatures one key may make: the lifetime `2^30`.

The model proves more, up to `N = 1,182,000,000` signatures, about `2^30.14`.

Up to `N`, a forgery has probability at most `q / 2^127` for `q` hash queries, in the random-oracle model.

That is `h26_layered` in [FORS/Main.lean](https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/formal/sphincs/FORS/Main.lean). -/
def SIGNATURE_LIMIT : Nat := 2 ^ 30

/-! ## Serialized sizes -/

/-- Bytes in a serialized public key: the root, then the public parameter. -/
def PUB_KEY_SIZE : Nat := N + PUBLIC_PARAM_LEN

/-- Bytes in one FORS tree's opening: the secret, then `a` path nodes.

An abbreviation, so an opening's bytes have this type by definition. -/
abbrev TREE_OPENING_SIZE : Nat := N + FORS_HEIGHT * N

/-- Bytes in one layer's signature of height `height`: counter, chain values, path. -/
def layerSigSize (height : Nat) : Nat := COUNTER_LEN + V * N + height * N

/-- Bytes in a serialized signature: randomizer, FORS opening, then the three layers from the bottom up. -/
def SIG_SIZE : Nat :=
  RANDOMIZER_LEN + FORS_TREES * TREE_OPENING_SIZE
    + 2 * layerSigSize LOWER_HEIGHT + layerSigSize TOP_HEIGHT

/-! ## Identities the parameter set must satisfy -/

/-- A digest is exactly 64 digits of 2 bits. -/
theorem digits_fill_digest : 2 * V = 8 * N := by decide

/-- The target sum is reachable: it does not exceed the maximum digit sum. -/
theorem target_sum_le_max : TARGET_SUM ≤ V * (CHAIN_LENGTH - 1) := by decide

/-- The verifier's step count is what the target sum leaves unwalked. -/
theorem chain_hashes_eq : V * (CHAIN_LENGTH - 1) - TARGET_SUM = CHAIN_HASHES := by decide

/-- The chain starts come in pairs, one hash for two chains. -/
theorem chains_even : 2 * (V / 2) = V := by decide

/-- An index has 26 bits: `10 + 8 + 8`. -/
theorem height_eq : HEIGHT = 26 := by decide

/-- The lifetime is within the model's proved limit of 1,182,000,000 signatures. -/
theorem signature_limit_le : SIGNATURE_LIMIT ≤ 1182000000 := by decide

/-- Two digest calls give the 266 bits the signature reads, and one would not. -/
theorem digest_calls_eq :
    DIGEST_CALLS = 2 ∧ 8 * HASH_LEN < DIGEST_BITS ∧ DIGEST_BITS ≤ DIGEST_CALLS * (8 * HASH_LEN) := by
  decide

/-- A digest call number fits the 24-bit address field `hi`. -/
theorem digest_calls_le : DIGEST_CALLS ≤ 2 ^ 24 := by decide

/-- The FORS leaf secrets come in pairs, one hash for two leaves. -/
theorem fors_leaves_even : 2 * (2 ^ FORS_HEIGHT / 2) = 2 ^ FORS_HEIGHT := by decide

/-- An index fits the 32-bit address field `lo`. -/
theorem index_fits_lo : 2 ^ HEIGHT ≤ 2 ^ 32 := by decide

/-- A FORS tree and a position in it fit the 24-bit address field `hi`.

The position of a node is `level + 16 j`, below `16 * 2^10`, and the tree adds `64` times it. -/
theorem fors_position_fits_hi : FORS_TREES + 64 * (16 * 2 ^ FORS_HEIGHT) ≤ 2 ^ 24 := by decide

/-- A FORS tree number fits the 6 bits of `hi` below the position. -/
theorem fors_trees_lt : FORS_TREES ≤ 64 := by decide

/-- A FORS level fits the 4 bits of a position below the node index. -/
theorem fors_height_lt : FORS_HEIGHT ≤ 16 := by decide

/-- The advertised public key size. -/
theorem pub_key_size_eq : PUB_KEY_SIZE = 32 := by decide

/-- The advertised FORS opening size: 24 trees of 176 bytes. -/
theorem fors_size_eq : FORS_TREES * TREE_OPENING_SIZE = 4224 := by decide

/-- The advertised size of a lower layer's signature. -/
theorem lower_layer_sig_size_eq : layerSigSize LOWER_HEIGHT = 1156 := by decide

/-- The advertised size of the top layer's signature. -/
theorem top_layer_sig_size_eq : layerSigSize TOP_HEIGHT = 1188 := by decide

/-- The advertised signature size, `7740` bytes, as in [leanSPHINCS.tex](https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/leanSPHINCS.tex) §1.

It is `signature_size` of [FORS/Scheme/Layout.lean](https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/formal/sphincs/FORS/Scheme/Layout.lean): `16 + 16 k (a + 1) + 1028 d + 16 h`. -/
theorem sig_size_eq : SIG_SIZE = 7740 ∧
    SIG_SIZE = 16 + 16 * FORS_TREES * (FORS_HEIGHT + 1) + 1028 * LAYERS + 16 * HEIGHT := by
  decide

end EthLib.Cryptography.Sphincs.Constants
