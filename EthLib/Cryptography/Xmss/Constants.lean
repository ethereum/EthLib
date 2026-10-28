/-!
# `Xmss.Constants`

The leanXMSS parameter set.

Source: the leanXMSS specification draft, section "Hashing and parameters".
-/

namespace EthLib.Cryptography.Xmss.Constants

/-! ## Hash and object sizes -/

/-- The hash value and Merkle node length in bytes, `n` in the specification.

128 bits, the digest size of the SLH-DSA parameter sets at NIST level 1. -/
def DIGEST_LEN : Nat := 16

/-- The public parameter length in bytes.

It is hashed into every call, which separates one key's hashes from another's. -/
def PUBLIC_PARAM_LEN : Nat := 16

/-- The address length in bytes.

An address separates the call sites of one key. -/
def ADDRESS_LEN : Nat := 16

/-- The message length in bytes.

leanXMSS signs a 256-bit message hash, so the caller hashes the real message first.

Two messages that share a hash share a signature. -/
def MESSAGE_LEN : Nat := 32

/-- The randomizer length in bytes.

The signer grinds it until the message digest is a codeword. -/
def RANDOMIZER_LEN : Nat := 16

/-- The secret key length in bytes.

The secret key is one uniform seed, and every other secret derives from it. -/
def SEED_LEN : Nat := 32

/-- The scheme's name, hashed in front of the seed.

No other scheme derives its secrets from the same bytes.

It is the 8-byte ASCII string `leanXMSS`, one byte per character. -/
def SEED_TAG : List UInt8 := "leanXMSS".toList.map fun c => UInt8.ofNat c.toNat

/-! ## WOTS+C -/

/-- The positions of one hash chain, `0` to `3`.

A digit of 2 bits names one of them. -/
def CHAIN_LENGTH : Nat := 4

/-- The digits a 16-byte digest carries: 128 bits, 2 bits each. -/
def DIGITS : Nat := 64

/-- The chains of one one-time key, `v` in the specification.

The last `64 - 58 = 6` digits of a codeword are zero, so they have no chain. -/
def V : Nat := 58

/-- The sum of a codeword's digits, `T` in the specification.

It replaces the Winternitz checksum.

`106` is above the mean digit sum `87`, so the verifier walks fewer steps. -/
def TARGET_SUM : Nat := 106

/-- Chain steps one verification walks on one layer, `3v - T`.

The digit sum is fixed, so the count is fixed. -/
def CHAIN_HASHES : Nat := 68

/-- The randomizer trials allowed per one-time signature, `A_max`.

A digest is a codeword with probability about `2^-20`.

So all `2^32` trials fail with probability below `exp(-2^11)`. -/
def MAX_RANDOMIZER_TRIALS : Nat := 2 ^ 32

/-! ## Trees -/

/-- The height of each layer's trees, `h` in the specification. -/
def LAYER_HEIGHT : Nat := 16

/-- The bits of a leaf index: one layer's height for each of the two layers. -/
def LOG_LIFETIME : Nat := 2 * LAYER_HEIGHT

/-! ## Serialized sizes -/

/-- Bytes in a serialized public key: the root, then the public parameter. -/
def PUB_KEY_SIZE : Nat := DIGEST_LEN + PUBLIC_PARAM_LEN

/-- Bytes in a serialized leaf index, a little-endian 32-bit word. -/
def LEAF_INDEX_SIZE : Nat := 4

/-- Bytes in one layer's signature: randomizer, chain values, path. -/
def LAYER_SIG_SIZE : Nat := RANDOMIZER_LEN + V * DIGEST_LEN + LAYER_HEIGHT * DIGEST_LEN

/-- Bytes in a serialized signature: the leaf index, then the bottom and top layers. -/
def SIG_SIZE : Nat := LEAF_INDEX_SIZE + 2 * LAYER_SIG_SIZE

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
