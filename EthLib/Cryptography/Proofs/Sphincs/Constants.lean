module

public import EthLib.Cryptography.Sphincs.Constants

/-!
# Proofs: leanSPHINCS parameters
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Constants

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

/-- The signature size, `7740` bytes, as in the table of the note's §1.

It is `n + k (1 + a) n + d (4 + v n) + h n`. -/
theorem sig_size_eq : SIG_SIZE = 7740 ∧
    SIG_SIZE = N + FORS_TREES * (1 + FORS_HEIGHT) * N + LAYERS * (COUNTER_LEN + V * N)
      + HEIGHT * N := by
  decide

/-- The verification cost, `515` permutations.

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
