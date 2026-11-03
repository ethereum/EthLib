module

public import EthLib.Execution.Evm.Precompiles.Identity
public import EthLib.Execution.Proofs.Evm.Words

/-!
# Proofs: `Identity`

The IDENTITY precompile at address `0x04` charges `15 + 3 * ceil(len / 32)` gas.
It fails exactly when the gas is below that price.
Otherwise it returns the call data, byte for byte.

The theorems hold for all call data and all gas.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Identity

open EthLib.Execution.Evm (wordCount wordCount_eq)

/-! ## Gas -/

/-- The price in closed form, `15 + 3 * ceil(size / 32)`. -/
theorem gasCost_eq (size : Nat) : gasCost size = 15 + 3 * ((size + 31) / 32) := by
  rw [gasCost, wordCount_eq]
  rfl

/-- Every call costs at least the base price. -/
theorem gasCost_base_le (size : Nat) : GAS_BASE ≤ gasCost size := by
  rw [gasCost_eq, GAS_BASE]
  omega

/-- Longer call data never costs less. -/
theorem gasCost_mono {short long : Nat} (le : short ≤ long) : gasCost short ≤ gasCost long := by
  rw [gasCost_eq, gasCost_eq]
  omega

/-- `k` whole EVM words of call data cost `15 + 3 * k`. -/
theorem gasCost_mul (k : Nat) : gasCost (32 * k) = 15 + 3 * k := by
  rw [gasCost_eq]
  omega

/-- One byte past `k` whole EVM words costs one EVM word more, `18 + 3 * k`. -/
theorem gasCost_mul_add_one (k : Nat) : gasCost (32 * k + 1) = 18 + 3 * k := by
  rw [gasCost_eq]
  omega

/-- Below 2^64 bytes of call data, the price is below 2^64. -/
theorem gasCost_lt_two_pow_64 {size : Nat} (bounded : size < 2 ^ 64) : gasCost size < 2 ^ 64 := by
  rw [gasCost_eq]
  have : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  omega

/-- Below 2^64 bytes of call data, the conversion of the price to `UInt64` keeps its value.

The C export returns the price as a `UInt64`. -/
theorem toNat_ofNat_gasCost {size : Nat} (bounded : size < 2 ^ 64) :
    (UInt64.ofNat (gasCost size)).toNat = gasCost size :=
  UInt64.toNat_ofNat_of_lt' (gasCost_lt_two_pow_64 bounded)

/-! ## The call -/

/-- With less gas than the price, the call runs out of gas. -/
theorem identity_out_of_gas (data : ByteArray) (gas : Nat) (short : gas < gasCost data.size) :
    identity data gas = .error (.outOfGas (gasCost data.size) gas) := by
  simp only [identity, short, ↓reduceIte]

/-- With at least the price, the call returns the call data. -/
theorem identity_ok (data : ByteArray) (gas : Nat) (enough : gasCost data.size ≤ gas) :
    identity data gas = .ok data := by
  simp only [identity, Nat.not_lt.mpr enough, ↓reduceIte]

/-- A call succeeds exactly when the gas covers the price, and then its output is the call data. -/
theorem identity_eq_ok_iff (data : ByteArray) (gas : Nat) (out : ByteArray) :
    identity data gas = .ok out ↔ gasCost data.size ≤ gas ∧ out = data := by
  by_cases short : gas < gasCost data.size
  · rw [identity_out_of_gas data gas short]
    constructor
    · intro wrong
      cases wrong
    · intro ⟨enough, _⟩
      omega
  · rw [identity_ok data gas (by omega)]
    constructor
    · intro same
      exact ⟨by omega, (Except.ok.inj same).symm⟩
    · intro ⟨_, same⟩
      rw [same]

/-- A call fails exactly when the gas is below the price, and the error carries both. -/
theorem identity_eq_error_iff (data : ByteArray) (gas : Nat) (e : IdentityError) :
    identity data gas = .error e ↔ gas < gasCost data.size ∧ e = .outOfGas (gasCost data.size) gas := by
  by_cases short : gas < gasCost data.size
  · rw [identity_out_of_gas data gas short]
    constructor
    · intro same
      exact ⟨short, (Except.error.inj same).symm⟩
    · intro ⟨_, same⟩
      rw [same]
  · rw [identity_ok data gas (by omega)]
    constructor
    · intro wrong
      cases wrong
    · intro ⟨below, _⟩
      exact absurd below short

/-- An output has the length of the call data. -/
theorem identity_ok_size {data : ByteArray} {gas : Nat} {out : ByteArray} (ok : identity data gas = .ok out) :
    out.size = data.size := by
  rw [((identity_eq_ok_iff data gas out).mp ok).2]

/-- Each byte of an output is the byte of the call data at the same index. -/
theorem identity_ok_getElem? {data : ByteArray} {gas : Nat} {out : ByteArray} (ok : identity data gas = .ok out)
    (i : Nat) : out[i]? = data[i]? := by
  rw [((identity_eq_ok_iff data gas out).mp ok).2]

/-! ## Known answers

Each call data is called with exactly its price, and with one gas less.
The prices are `15 + 3 * ceil(len / 32)`, worked out for each length.
The expected output is the call data, as `identity` in execution-specs sets `evm.output = data`. -/

/-- Known answer: empty call data with 15 gas, the base price alone, returns empty output. -/
theorem identity_empty : identity ByteArray.empty 15 = .ok ByteArray.empty := by
  rw [identity_ok _ _ (by decide)]

/-- Known answer: empty call data with 14 gas runs out of gas. -/
theorem identity_empty_out_of_gas : identity ByteArray.empty 14 = .error (.outOfGas 15 14) := by
  rw [identity_out_of_gas _ _ (by decide)]
  rfl

/-- Known answer: one byte with 18 gas, the price of one EVM word, returns that byte. -/
theorem identity_one : identity ⟨#[0xff]⟩ 18 = .ok ⟨#[0xff]⟩ := by
  rw [identity_ok _ _ (by decide)]

/-- Known answer: one byte with 17 gas runs out of gas. -/
theorem identity_one_out_of_gas : identity ⟨#[0xff]⟩ 17 = .error (.outOfGas 18 17) := by
  rw [identity_out_of_gas _ _ (by decide)]
  rfl

/-- The 32 bytes `0x00, 0x01, ..., 0x1f`: exactly one EVM word. -/
def bytes32 : ByteArray :=
  ⟨#[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
     0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f]⟩

/-- The 33 bytes `0x00, 0x01, ..., 0x20`: one byte into a second EVM word. -/
def bytes33 : ByteArray :=
  ⟨#[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
     0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20]⟩

/-- Known answer: 32 bytes with 18 gas, the price of one EVM word, returns the same 32 bytes. -/
theorem identity_32 : identity bytes32 18 = .ok bytes32 := by
  rw [identity_ok _ _ (by decide)]

/-- Known answer: 32 bytes with 17 gas runs out of gas. -/
theorem identity_32_out_of_gas : identity bytes32 17 = .error (.outOfGas 18 17) := by
  rw [identity_out_of_gas _ _ (by decide)]
  rfl

/-- Known answer: 33 bytes with 21 gas, the price of two EVM words, returns the same 33 bytes. -/
theorem identity_33 : identity bytes33 21 = .ok bytes33 := by
  rw [identity_ok _ _ (by decide)]

/-- Known answer: 33 bytes with 20 gas runs out of gas. -/
theorem identity_33_out_of_gas : identity bytes33 20 = .error (.outOfGas 21 20) := by
  rw [identity_out_of_gas _ _ (by decide)]
  rfl

end EthLib.Execution.Evm.Precompiles.Identity
