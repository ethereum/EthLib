module

public import EthLib.Execution.Evm.Gas.Prices
public import EthLib.Execution.Proofs.Evm.Words

/-!
# Proofs: `Evm.Gas.Prices`

A call passes on at most the gas it has, and at least 63 64ths of it.

From Berlin, an access to an account or a slot pays the cold or the warm price.

The token prices of EIP-7623 and the refund of EIP-3529 agree with the prices they derive from.

The prices that EIP-8038 derives from other prices have the values of its table.

From Shapella on, the limit of init code is twice the limit of code, as EIP-3860 defines it.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)
open GasCosts

/-- A call passes on at most the gas it has. -/
theorem maxMessageCallGas_le (gas : Nat) : maxMessageCallGas gas ≤ gas := by
  unfold maxMessageCallGas
  omega

/-- A call passes on at least 63 64ths of the gas it has. -/
theorem maxMessageCallGas_ge (gas : Nat) : 63 * gas ≤ 64 * maxMessageCallGas gas := by
  unfold maxMessageCallGas
  omega

/-- The price of init code as 2 times the length rounded up to whole words, over 32. -/
theorem initCodeCost_eq (initCodeLength : Nat) :
    initCodeCost initCodeLength = CODE_INIT_PER_WORD * ceil32 initCodeLength / 32 := by
  have := ceil32_mod initCodeLength
  unfold initCodeCost wordCount WORD_BYTES CODE_INIT_PER_WORD
  omega

/-- From Berlin, SLOAD pays the price of a cold or a warm access to the slot. -/
theorem sloadCost_of_berlin_le {fork : Fork} (h : fork ≥ .berlin) (cold : Bool) :
    sloadCost fork cold = if cold then COLD_STORAGE_ACCESS else WARM_ACCESS := by
  simp [sloadCost, h]

/-- From Berlin, BALANCE pays the price of a cold or a warm access to the account. -/
theorem balanceCost_of_berlin_le {fork : Fork} (h : fork ≥ .berlin) (cold : Bool) :
    balanceCost fork cold = accountAccessCost fork cold := by
  simp [balanceCost, h]

/-- From Berlin to Glamsterdam, EXTCODESIZE and EXTCODECOPY pay the price of an access. -/
theorem externalBaseCost_of_berlin_le {fork : Fork} (h : fork ≥ .berlin)
    (h' : fork < .glamsterdam) (cold : Bool) :
    externalBaseCost fork cold = accountAccessCost fork cold := by
  have hn : ¬ fork ≥ Fork.glamsterdam := Nat.not_le.mpr h'
  simp [externalBaseCost, h, hn]

/-- From Glamsterdam, EXTCODESIZE and EXTCODECOPY also pay a warm access to read the code. -/
theorem externalBaseCost_of_glamsterdam_le {fork : Fork} (h : fork ≥ .glamsterdam)
    (cold : Bool) : externalBaseCost fork cold = accountAccessCost fork cold + WARM_ACCESS := by
  simp [externalBaseCost, h]

/-- From Berlin, EXTCODEHASH pays the price of a cold or a warm access to the account. -/
theorem extcodehashCost_of_berlin_le {fork : Fork} (h : fork ≥ .berlin) (cold : Bool) :
    extcodehashCost fork cold = accountAccessCost fork cold := by
  simp [extcodehashCost, h]

/-- From Berlin, the calls pay the price of a cold or a warm access to the account. -/
theorem callBaseCost_of_berlin_le {fork : Fork} (h : fork ≥ .berlin) (cold : Bool) :
    callBaseCost fork cold = accountAccessCost fork cold := by
  simp [callBaseCost, h]

/-- From Istanbul, a byte of call data costs the standard price of its tokens.

A zero byte is one token, and a nonzero byte is four, so EIP-7623 keeps the price of EIP-2028. -/
theorem txData_of_istanbul_le {fork : Fork} (h : fork ≥ .istanbul) :
    TX_DATA_PER_ZERO = TX_DATA_TOKEN_STANDARD ∧
      (gasSchedule fork).TX_DATA_PER_NON_ZERO = 4 * TX_DATA_TOKEN_STANDARD := by
  simp [gasSchedule, h, TX_DATA_PER_ZERO, TX_DATA_TOKEN_STANDARD]

/-- Before Glamsterdam, from London, the refund to clear a slot adds the reset and a listed key.

The reset price is the price to change a slot, and the key is the price of a key of an access list.

EIP-3529 defines it so, with the reset price of EIP-2929, which excludes the cold access. -/
theorem refundStorageClear_of_london_le {fork : Fork} (h : fork ≥ .london)
    (h' : fork < .glamsterdam) :
    (gasSchedule fork).REFUND_STORAGE_CLEAR =
      COLD_STORAGE_WRITE - COLD_STORAGE_ACCESS + (gasSchedule fork).TX_ACCESS_LIST_STORAGE_KEY := by
  have h'' : ¬ fork ≥ Fork.glamsterdam := Nat.not_le.mpr h'
  simp [gasSchedule, h, h'', COLD_STORAGE_WRITE, COLD_STORAGE_ACCESS]

/-- From Glamsterdam, four prices of the gas schedule have the values that EIP-8038 lists.

An address of an access list costs 2900, and a storage key costs 2000.

A cold access to an account costs 3000, and the refund to clear a slot is 11616. -/
theorem gasSchedule_of_glamsterdam_le {fork : Fork} (h : fork ≥ .glamsterdam) :
    (gasSchedule fork).TX_ACCESS_LIST_ADDRESS = 2900 ∧
      (gasSchedule fork).TX_ACCESS_LIST_STORAGE_KEY = 2000 ∧
      (gasSchedule fork).COLD_ACCOUNT_ACCESS = 3000 ∧
      (gasSchedule fork).REFUND_STORAGE_CLEAR = 11616 := by
  simp [gasSchedule, h, WARM_ACCESS, COLD_STORAGE_ACCESS, STORAGE_WRITE]

/-- The price to access and write the account of a creation is 12000, as EIP-8038 lists it. -/
theorem createAccess_eq : CREATE_ACCESS = 12000 := by
  decide

/-- At every fork with a limit of code, the limit of init code is twice that limit.

EIP-3860 sets that ratio from Shapella on.

Before Shapella the value has the same ratio, but no rule reads it. -/
theorem maxInitCodeSize_eq_two_mul {fork : Fork} {n : Nat} (h : maxCodeSize fork = some n) :
    maxInitCodeSize fork = 2 * n := by
  unfold maxCodeSize at h
  unfold maxInitCodeSize
  split at h
  · cases h
    simp [*]
  · split at h
    · cases h
      have : ¬ fork ≥ Fork.glamsterdam := by assumption
      simp [this]
    · cases h

end EthLib.Execution.Evm
