module

public import EthLib.Execution.Blocks.Validate
public import EthLib.Execution.Proofs.Blocks.Receipt

/-!
# Proofs: the checks of a header

A header passes exactly when every one of its checks holds.

So a valid header uses at most its gas limit, and the gas limit rule accepts its gas limit.

It also has the base fee that its parent gives.

From Dencun, it also has the excess blob gas that its parent gives.

From Fusaka, a block passes the size check exactly when its RLP form fits in the limit.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Fees

/-- The checks pass exactly when every condition holds. -/
theorem firstFailure_eq_ok_iff (checks : List (Bool × BlockError)) :
    firstFailure checks = .ok () ↔ ∀ c ∈ checks, c.1 = true := by
  induction checks with
  | nil => simp [firstFailure]
  | cons c rest ih =>
    obtain ⟨condition, error⟩ := c
    cases condition <;> simp [firstFailure, ih]

variable {parentFork fork : Fork} {hLondon : .london ≤ parentFork} {hFork : parentFork ≤ fork}
  {hParis : .paris ≤ fork} {parent : Header parentFork} {header : Header fork}

/-- A valid header passes each of its checks. -/
theorem check_of_validateHeader (hv : validateHeader hLondon hFork hParis parent header = .ok ())
    {c : Bool × BlockError} (hc : c ∈ headerChecks hLondon hFork parent header) : c.1 = true :=
  (firstFailure_eq_ok_iff _).mp hv c hc

/-- A valid header uses at most its gas limit. -/
theorem gasUsed_le_of_validateHeader
    (hv : validateHeader hLondon hFork hParis parent header = .ok ()) :
    header.gasUsed ≤ header.gasLimit := by
  have := check_of_validateHeader hv (c := (decide (header.gasUsed ≤ header.gasLimit),
    .gasUsedAboveLimit)) (by simp [headerChecks])
  simpa using this

/-- A valid header has a gas limit that the rule of the gas limit accepts. -/
theorem checkGasLimit_of_validateHeader
    (hv : validateHeader hLondon hFork hParis parent header = .ok ()) :
    GasLimit.checkGasLimit header.gasLimit parent.gasLimit = true :=
  check_of_validateHeader hv (c := (GasLimit.checkGasLimit header.gasLimit parent.gasLimit,
    .invalidGasLimit)) (by simp [headerChecks])

/-- A valid header has the base fee that its parent gives. -/
theorem baseFee_of_validateHeader
    (hv : validateHeader hLondon hFork hParis parent header = .ok ()) :
    header.baseFeePerGas (Nat.le_trans hLondon hFork) =
      BaseFee.calculateBaseFeePerGas parent.gasLimit parent.gasUsed
        (parent.baseFeePerGas hLondon) := by
  have := check_of_validateHeader hv
    (c := (decide (header.baseFeePerGas (Nat.le_trans hLondon hFork) =
        expectedBaseFee hLondon parent),
      .wrongBaseFee (expectedBaseFee hLondon parent)
        (header.baseFeePerGas (Nat.le_trans hLondon hFork))))
    (by simp [headerChecks])
  exact of_decide_eq_true this

/-- From Dencun, a valid header has the excess blob gas that its parent gives. -/
theorem excessBlobGas_of_validateHeader (h : .dencun ≤ fork)
    (hv : validateHeader hLondon hFork hParis parent header = .ok ()) :
    (header.excessBlobGas h).toNat = expectedExcessBlobGas hLondon h parent := by
  have := check_of_validateHeader hv
    (c := (decide ((header.excessBlobGas h).toNat = expectedExcessBlobGas hLondon h parent),
      .wrongExcessBlobGas (expectedExcessBlobGas hLondon h parent)
        (header.excessBlobGas h).toNat))
    (by simp [headerChecks, h])
  simpa using this

/-- A valid header follows its parent: one number higher, and later in time. -/
theorem number_timestamp_of_validateHeader
    (hv : validateHeader hLondon hFork hParis parent header = .ok ()) :
    header.number = parent.number + 1 ∧ parent.timestamp.toNat < header.timestamp.toNat := by
  constructor
  · simpa using check_of_validateHeader hv
      (c := (decide (header.number = parent.number + 1), .wrongNumber)) (by simp [headerChecks])
  · simpa using check_of_validateHeader hv
      (c := (decide (parent.timestamp.toNat < header.timestamp.toNat), .timestampNotAfterParent))
      (by simp [headerChecks])

/-- A block passes the size check exactly when its fork is before Fusaka, or its RLP form fits.

The RLP form fits when it has at most 8 MiB, that is 8,388,608 bytes. -/
theorem validateBlockSize_eq_ok_iff {fork : Fork} {Tx : Type} [Serialization.Rlp.Codec Tx]
    (block : Block fork Tx) :
    validateBlockSize block = .ok () ↔
      fork < .fusaka ∨ ∃ bytes, Serialization.Rlp.Codec.encode block = .ok bytes ∧
        bytes.size ≤ MAX_RLP_BLOCK_SIZE := by
  unfold validateBlockSize
  by_cases hfork : fork ≥ .fusaka
  · have hnot : ¬ fork < .fusaka := fun hlt => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hfork)
    simp only [hfork, ↓reduceIte, hnot, false_or]
    cases Serialization.Rlp.Codec.encode block with
    | error e => simp [Except.mapError, bind, Except.bind]
    | ok bytes => simp [Except.mapError, bind, Except.bind, firstFailure_eq_ok_iff]
  · have hlt : fork < .fusaka := Nat.lt_of_not_le hfork
    simp [hfork, hlt]

/-- Two errors with one code come from one constructor. -/
theorem BlockError.code_injective (e₁ e₂ : BlockError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [BlockError.code] at h; exact absurd h (by decide))

/-- A block error never has the code of an RLP error. -/
theorem BlockError.code_ne_rlp (e : BlockError) (r : Serialization.Rlp.RlpError) :
    e.code ≠ r.code := by
  cases e <;> cases r <;> simp only [BlockError.code, Serialization.Rlp.RlpError.code] <;> decide

/-- A block error never has the code of a receipt error. -/
theorem BlockError.code_ne_receipt (e : BlockError) (r : ReceiptError) : e.code ≠ r.code := by
  cases e <;> cases r <;> simp only [BlockError.code, ReceiptError.code] <;> decide

end EthLib.Execution.Blocks
