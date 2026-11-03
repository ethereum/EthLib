module

public import EthLib.Execution.Evm.Precompiles.Sha256
public import EthLib.Execution.Proofs.Evm.Words
public import EthLib.Cryptography.Proofs.Hash.Sha256
public import EthLib.Cryptography.Proofs.Hash.Ripemd160

/-!
# Proofs: `Sha256`

The SHA-256 precompile at address `0x02` charges `60 + 12 * ceil(len / 32)` gas.
It fails exactly when the gas is below that price, and otherwise returns the 32-byte SHA-256 digest of the call data.

The digest is the FIPS 180-4 hash of `Cryptography.Proofs.Hash.Sha256` whenever the call data is shorter than 2^61 bytes.
Every call that succeeds with less than `60 + 12 * 2^56` gas has such call data.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Sha256

open EthLib.Execution.Evm (wordCount_eq)

-- Only the hex and ASCII helpers of the RIPEMD-160 known answers, so `sha256` keeps naming the precompile.
open EthLib.Cryptography.Hash.Ripemd160 (hexBytes ascii)

/-! ## Gas -/

/-- The price in closed form, `60 + 12 * ceil(size / 32)`. -/
theorem gasCost_eq (size : Nat) : gasCost size = 60 + 12 * ((size + 31) / 32) := by
  rw [gasCost, wordCount_eq]
  rfl

/-- Longer call data never costs less. -/
theorem gasCost_mono {short long : Nat} (le : short ≤ long) : gasCost short ≤ gasCost long := by
  rw [gasCost_eq, gasCost_eq]
  omega

/-- Below 2^63 bytes of call data, the price fits in 64 bits, so the C export reports it exactly. -/
theorem gasCost_lt_two_pow_64 {size : Nat} (bounded : size < 2 ^ 63) : gasCost size < 2 ^ 64 := by
  rw [gasCost_eq]
  have : (2 : Nat) ^ 63 = 9223372036854775808 := rfl
  have : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  omega

/-- Empty call data costs the base price alone. -/
theorem gasCost_zero : gasCost 0 = 60 := by
  rw [gasCost_eq]

/-- One byte already costs one whole word. -/
theorem gasCost_one : gasCost 1 = 72 := by
  rw [gasCost_eq]

/-- Thirty-two bytes still cost one word. -/
theorem gasCost_32 : gasCost 32 = 72 := by
  rw [gasCost_eq]

/-- The thirty-third byte starts a second word. -/
theorem gasCost_33 : gasCost 33 = 84 := by
  rw [gasCost_eq]

/-! ## The call -/

/-- With less gas than the price, the call runs out of gas. -/
theorem sha256_out_of_gas (data : ByteArray) (gas : Nat) (short : gas < gasCost data.size) :
    sha256 data gas = .error (.outOfGas (gasCost data.size) gas) := by
  simp only [sha256, short, ↓reduceIte]

/-- With at least the price, the call returns the SHA-256 digest of the whole call data. -/
theorem sha256_ok (data : ByteArray) (gas : Nat) (enough : gasCost data.size ≤ gas) :
    sha256 data gas = .ok (Cryptography.Hash.sha256 data) := by
  simp only [sha256, Nat.not_lt.mpr enough, ↓reduceIte]

/-- A call succeeds exactly when the gas covers the price, and then returns the digest. -/
theorem sha256_eq_ok_iff (data : ByteArray) (gas : Nat) (out : ByteArray) :
    sha256 data gas = .ok out ↔ gasCost data.size ≤ gas ∧ out = Cryptography.Hash.sha256 data := by
  by_cases short : gas < gasCost data.size
  · rw [sha256_out_of_gas data gas short]
    constructor
    · intro wrong
      simp at wrong
    · intro ⟨enough, _⟩
      omega
  · rw [sha256_ok data gas (by omega)]
    constructor
    · intro same
      -- Injectivity, rather than `cases`, so the digest is never unfolded.
      exact ⟨by omega, (Except.ok.inj same).symm⟩
    · intro ⟨_, same⟩
      rw [same]

/-- A call fails exactly when the gas is below the price, and the error carries both. -/
theorem sha256_eq_error_iff (data : ByteArray) (gas : Nat) (e : Sha256Error) :
    sha256 data gas = .error e ↔ gas < gasCost data.size ∧ e = .outOfGas (gasCost data.size) gas := by
  by_cases short : gas < gasCost data.size
  · rw [sha256_out_of_gas data gas short]
    constructor
    · intro same
      exact ⟨short, (Except.error.inj same).symm⟩
    · intro ⟨_, same⟩
      rw [same]
  · rw [sha256_ok data gas (by omega)]
    constructor
    · intro wrong
      simp at wrong
    · intro ⟨below, _⟩
      exact absurd below short

/-- Every output is 32 bytes. -/
theorem sha256_ok_size {data : ByteArray} {gas : Nat} {out : ByteArray} (ok : sha256 data gas = .ok out) :
    out.size = OUTPUT_BYTES := by
  rw [((sha256_eq_ok_iff data gas out).mp ok).2]
  exact Cryptography.Hash.Sha256.hash_size data

/-! ## Agreement with FIPS 180-4 -/

/-- Below 2^61 bytes of call data, the output is the SHA-256 of FIPS 180-4 §6.2.

FIPS 180-4 §5.1.1 admits messages of fewer than 2^64 bits, which is 2^61 bytes. -/
theorem sha256_ok_eq_spec {data : ByteArray} {gas : Nat} {out : ByteArray} (ok : sha256 data gas = .ok out)
    (admitted : data.size < 2 ^ 61) : out = Cryptography.Hash.Sha256.Spec.hash data := by
  rw [((sha256_eq_ok_iff data gas out).mp ok).2]
  exact Cryptography.Hash.Sha256.hash_eq_spec data admitted

/-- The price of 2^61 bytes of call data, `60 + 12 * 2^56`. -/
theorem gasCost_admitted : gasCost (2 ^ 61) = 864691128455135292 := by
  rw [gasCost_eq]

/-- A call that succeeds with less than `60 + 12 * 2^56` gas returns the SHA-256 of FIPS 180-4 §6.2.

So the length hypothesis of `sha256_ok_eq_spec` follows from the gas. -/
theorem sha256_ok_eq_spec_of_gas {data : ByteArray} {gas : Nat} {out : ByteArray}
    (ok : sha256 data gas = .ok out) (bounded : gas < gasCost (2 ^ 61)) :
    out = Cryptography.Hash.Sha256.Spec.hash data := by
  have enough := ((sha256_eq_ok_iff data gas out).mp ok).1
  apply sha256_ok_eq_spec ok
  -- Call data of 2^61 bytes or more would cost at least the bound.
  apply Nat.lt_of_not_le
  intro long
  have := gasCost_mono long
  omega

/-! ## Known answers

The inputs and digests are NIST CAVP vectors from `bindings/python/tests/sha256/cavp/SHA256ShortMsg.rsp`, and the FIPS 180-4 example `"abc"`.
Each is called with exactly its price, and with one gas less. -/

/-- The digest of the empty message, `Len = 0` in `SHA256ShortMsg.rsp`. -/
private theorem digest_empty :
    Cryptography.Hash.sha256 ByteArray.empty =
      hexBytes "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" := by
  decide +kernel

/-- Known answer: empty call data with 60 gas. -/
theorem sha256_empty :
    sha256 ByteArray.empty 60 =
      .ok (hexBytes "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855") := by
  rw [sha256_ok _ _ (by decide), digest_empty]

/-- Known answer: empty call data with 59 gas runs out of gas. -/
theorem sha256_empty_out_of_gas : sha256 ByteArray.empty 59 = .error (.outOfGas 60 59) := by
  rw [sha256_out_of_gas _ _ (by decide)]
  rfl

/-- The 32-byte message of `Len = 256` in `SHA256ShortMsg.rsp`. -/
def message32 : ByteArray :=
  hexBytes "09fc1accc230a205e4a208e64a8f204291f581a12756392da4b8c0cf5ef02b95"

/-- The 33-byte message of `Len = 264` in `SHA256ShortMsg.rsp`. -/
def message33 : ByteArray :=
  hexBytes "0546f7b8682b5b95fd32385faf25854cb3f7b40cc8fa229fbd52b16934aab388a7"

private theorem message32_size : message32.size = 32 := by decide +kernel

private theorem message33_size : message33.size = 33 := by decide +kernel

/-- The digest of `message32`, as `SHA256ShortMsg.rsp` lists it. -/
private theorem digest_32 :
    Cryptography.Hash.sha256 message32 =
      hexBytes "4f44c1c7fbebb6f9601829f3897bfd650c56fa07844be76489076356ac1886a4" := by
  decide +kernel

/-- The digest of `message33`, as `SHA256ShortMsg.rsp` lists it. -/
private theorem digest_33 :
    Cryptography.Hash.sha256 message33 =
      hexBytes "b31ad3cd02b10db282b3576c059b746fb24ca6f09fef69402dc90ece7421cbb7" := by
  decide +kernel

/-- Known answer: thirty-two bytes with 72 gas, the price of one word. -/
theorem sha256_32 :
    sha256 message32 72 =
      .ok (hexBytes "4f44c1c7fbebb6f9601829f3897bfd650c56fa07844be76489076356ac1886a4") := by
  rw [sha256_ok _ _ (by rw [message32_size, gasCost_32] <;> decide), digest_32]

/-- Known answer: thirty-two bytes with 71 gas runs out of gas. -/
theorem sha256_32_out_of_gas : sha256 message32 71 = .error (.outOfGas 72 71) := by
  rw [sha256_out_of_gas _ _ (by rw [message32_size, gasCost_32] <;> decide), message32_size, gasCost_32]

/-- Known answer: thirty-three bytes with 84 gas, the price of two words. -/
theorem sha256_33 :
    sha256 message33 84 =
      .ok (hexBytes "b31ad3cd02b10db282b3576c059b746fb24ca6f09fef69402dc90ece7421cbb7") := by
  rw [sha256_ok _ _ (by rw [message33_size, gasCost_33] <;> decide), digest_33]

/-- Known answer: thirty-three bytes with 83 gas runs out of gas. -/
theorem sha256_33_out_of_gas : sha256 message33 83 = .error (.outOfGas 84 83) := by
  rw [sha256_out_of_gas _ _ (by rw [message33_size, gasCost_33] <;> decide), message33_size, gasCost_33]

/-- The FIPS 180-4 example message `"abc"`, as in `tests/cryptography/sha256/hash/hash_case_fips_abc`. -/
private theorem digest_abc :
    Cryptography.Hash.sha256 (ascii "abc") =
      hexBytes "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" := by
  decide +kernel

/-- Known answer: the call data `"abc"` with 72 gas. -/
theorem sha256_abc :
    sha256 (ascii "abc") 72 =
      .ok (hexBytes "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad") := by
  rw [sha256_ok _ _ (by decide +kernel), digest_abc]

end EthLib.Execution.Evm.Precompiles.Sha256
