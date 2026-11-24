module

public import EthLib.Execution.Evm.Precompiles.Sha256
public import EthLib.Base.Proofs.Except
public import EthLib.Execution.Proofs.Evm.Words
public import EthLib.Cryptography.Proofs.Hash.Sha256
import EthLib.Base.Proofs.CodeInjective

/-!
# Proofs: `Sha256`

The SHA-256 precompile at address `0x02` charges `60 + 12 * ceil(len / 32)` gas.
It fails exactly when the gas is below that price, and otherwise returns the 32-byte SHA-256 digest of the call data.

The digest is the FIPS 180-4 hash of `Cryptography.Proofs.Hash.Sha256` whenever the call data is shorter than 2^61 bytes.
Every call that succeeds with less than `60 + 12 * 2^56` gas has such call data.

The price grows with the size, and fits in 64 bits below 2^63 bytes.

Two errors with one code come from one constructor.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Sha256

open EthLib.Execution.Evm (wordPrice_eq wordPrice_mono wordPrice_le)

/-! ## Gas -/

/-- The price in closed form, `60 + 12 * ceil(size / 32)`. -/
theorem gasCost_eq (size : Nat) : gasCost size = 60 + 12 * ((size + 31) / 32) :=
  wordPrice_eq _ _ size

/-- Longer call data never costs less. -/
theorem gasCost_mono {short long : Nat} (le : short ≤ long) : gasCost short ≤ gasCost long :=
  wordPrice_mono _ _ le

/-- Below 2^63 bytes of call data, the price fits in 64 bits.

So a call with a 64-bit gas amount can pay it. -/
theorem gasCost_lt_two_pow_64 {size : Nat} (bounded : size < 2 ^ 63) : gasCost size < 2 ^ 64 := by
  -- Such call data fits in 2^58 words.
  have covers : size ≤ 32 * 2 ^ 58 := by
    have : (2 : Nat) ^ 63 = 32 * 2 ^ 58 := by decide
    omega
  exact Nat.lt_of_le_of_lt (wordPrice_le _ _ covers) (by decide)

/-! ## The call -/

/-- With less gas than the price, the call runs out of gas. -/
theorem sha256_outOfGas (data : ByteArray) (gas : Nat) (short : gas < gasCost data.size) :
    sha256 data gas = .error (.outOfGas (gasCost data.size) gas) := by
  simp only [sha256, short, ↓reduceIte]

/-- With at least the price, the call returns the SHA-256 digest of the whole call data. -/
theorem sha256_ok (data : ByteArray) (gas : Nat) (enough : gasCost data.size ≤ gas) :
    sha256 data gas = .ok (Cryptography.Hash.sha256 data) := by
  simp only [sha256, Nat.not_lt.mpr enough, ↓reduceIte]

/-- A call succeeds exactly when the gas covers the price, and then returns the digest. -/
theorem sha256_eq_ok_iff (data : ByteArray) (gas : Nat) (out : ByteArray) :
    sha256 data gas = .ok out ↔ gasCost data.size ≤ gas ∧ out = Cryptography.Hash.sha256 data := by
  -- The digest stays a term of the statement, never unfolded.
  unfold sha256
  exact Base.ite_lt_eq_ok_iff

/-- A call fails exactly when the gas is below the price, and the error carries both. -/
theorem sha256_eq_error_iff (data : ByteArray) (gas : Nat) (e : Sha256Error) :
    sha256 data gas = .error e ↔ gas < gasCost data.size ∧ e = .outOfGas (gasCost data.size) gas := by
  unfold sha256
  exact Base.ite_lt_eq_error_iff

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

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem Sha256Error.code_injective (e₁ e₂ : Sha256Error) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  code_injective Sha256Error.code

end EthLib.Execution.Evm.Precompiles.Sha256
