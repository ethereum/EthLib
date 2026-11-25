module

public import EthLib.Cryptography.Xmss.Constants

/-!
# Proofs: leanXMSS parameters
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Constants

/-! ## The values of the parameters -/

/-- `v = 58` chains per one-time key. -/
theorem v_eq : V = 58 := rfl

/-- 4 positions per chain. -/
theorem chain_length_eq : CHAIN_LENGTH = 4 := rfl

/-- 64 digits per digest. -/
theorem digits_eq : DIGITS = 64 := rfl

/-- `T = 106`. -/
theorem target_sum_eq : TARGET_SUM = 106 := rfl

/-- `h = 16` levels per tree. -/
theorem layer_height_eq : LAYER_HEIGHT = 16 := rfl

/-! ## Identities the parameter set must satisfy -/

/-- A digest is exactly 64 digits of 2 bits. -/
theorem digits_fill_digest : 2 * DIGITS = 8 * DIGEST_LEN := by decide

/-- The 58 chains leave 6 digits that every codeword sets to zero. -/
theorem zero_digits : DIGITS - V = 6 := by decide

/-- The chain secrets come in pairs, one hash for two chains. -/
theorem chains_even : 2 * (V / 2) = V := by decide

/-- The target sum is reachable: it does not exceed the maximum digit sum. -/
theorem target_sum_le_max : TARGET_SUM ≤ V * (CHAIN_LENGTH - 1) := by decide

/-- The verifier's step count is what the target sum leaves unwalked. -/
theorem chain_hashes_eq : V * (CHAIN_LENGTH - 1) - TARGET_SUM = CHAIN_HASHES := by decide

/-- A leaf index is the two layers' indices side by side. -/
theorem log_lifetime_eq : LOG_LIFETIME = 8 * LEAF_INDEX_SIZE := by decide

/-- The scheme's name, byte by byte. -/
theorem seed_tag_eq : SEED_TAG = [0x6c, 0x65, 0x61, 0x6e, 0x58, 0x4d, 0x53, 0x53] := by decide

/-- The advertised public key size. -/
theorem pub_key_size_eq : PUB_KEY_SIZE = 32 := by decide

/-- The advertised layer signature size. -/
theorem layer_sig_size_eq : LAYER_SIG_SIZE = 1200 := by decide

/-- The advertised signature size. -/
theorem sig_size_eq : SIG_SIZE = 2404 := by decide

end EthLib.Cryptography.Xmss.Constants
