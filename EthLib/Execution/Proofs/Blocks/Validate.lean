module

public import EthLib.Execution.Blocks.Validate
public import EthLib.Execution.Proofs.Blocks.Receipt

/-!
# Proofs: the checks of a header

A header passes exactly when every one of its checks holds.

So a valid header uses at most its gas limit, and the gas limit rule accepts its gas limit.

From London, it also has the base fee that its parent gives, or the initial one at the first block.

From Dencun, it also has the excess blob gas that its parent gives under its blob schedule.

Before Paris, it has the difficulty that its parent gives, and a valid proof of work.

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

variable {parentFork fork : Fork} {hFork : parentFork ≤ fork} {parent : Header parentFork}
  {header : Header fork} {schedule : Since .dencun fork BlobSchedule}

/-- A valid header passes every check but the proof of work. -/
theorem checkHeader_of_validateHeader
    (hv : validateHeader hFork parent header schedule = .ok ()) :
    checkHeader hFork parent header schedule = .ok () := by
  unfold validateHeader at hv
  cases hc : checkHeader hFork parent header schedule with
  | error e => simp [hc, bind, Except.bind] at hv
  | ok u => rfl

/-- A valid header passes each of its checks. -/
theorem check_of_validateHeader (hv : validateHeader hFork parent header schedule = .ok ())
    {c : Bool × BlockError} (hc : c ∈ headerChecks hFork parent header schedule) : c.1 = true :=
  (firstFailure_eq_ok_iff _).mp (checkHeader_of_validateHeader hv) c hc

/-- A valid header uses at most its gas limit. -/
theorem gasUsed_le_of_validateHeader
    (hv : validateHeader hFork parent header schedule = .ok ()) :
    header.gasUsed ≤ header.gasLimit := by
  have := check_of_validateHeader hv (c := (decide (header.gasUsed ≤ header.gasLimit),
    .gasUsedAboveLimit)) (by simp [headerChecks])
  simpa using this

/-- A valid header has a gas limit that the rule accepts, across a London transition too. -/
theorem checkGasLimitAcross_of_validateHeader
    (hv : validateHeader hFork parent header schedule = .ok ()) :
    GasLimit.checkGasLimitAcross parentFork fork header.gasLimit parent.gasLimit = true :=
  check_of_validateHeader hv (c := (GasLimit.checkGasLimitAcross parentFork fork header.gasLimit
    parent.gasLimit, .invalidGasLimit)) (by simp [headerChecks])

/-- With a parent from London on, a valid header has a gas limit that the plain rule accepts. -/
theorem checkGasLimit_of_validateHeader (hLondon : .london ≤ parentFork)
    (hv : validateHeader hFork parent header schedule = .ok ()) :
    GasLimit.checkGasLimit header.gasLimit parent.gasLimit = true := by
  have h := checkGasLimitAcross_of_validateHeader hv
  have hnot : ¬ (parentFork < .london ∧ .london ≤ fork) := fun ⟨hlt, _⟩ =>
    Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hLondon)
  simpa [GasLimit.checkGasLimitAcross, GasLimit.parentGasLimitForCheck, hnot] using h

/-- From London on, a valid header has the base fee that the rule across forks gives. -/
theorem baseFeeAcross_of_validateHeader (h : .london ≤ fork)
    (hv : validateHeader hFork parent header schedule = .ok ()) :
    header.baseFeePerGas h = expectedBaseFeeAcross parent := by
  have := check_of_validateHeader hv
    (c := (decide (header.baseFeePerGas h = expectedBaseFeeAcross parent),
      .wrongBaseFee (expectedBaseFeeAcross parent) (header.baseFeePerGas h)))
    (by simp [headerChecks, h])
  exact of_decide_eq_true this

/-- With a parent from London on, a valid header has the base fee that its parent gives. -/
theorem baseFee_of_validateHeader (hLondon : .london ≤ parentFork)
    (hv : validateHeader hFork parent header schedule = .ok ()) :
    header.baseFeePerGas (Nat.le_trans hLondon hFork) =
      BaseFee.calculateBaseFeePerGas parent.gasLimit parent.gasUsed
        (parent.baseFeePerGas hLondon) := by
  rw [baseFeeAcross_of_validateHeader _ hv]
  simp [expectedBaseFeeAcross, hLondon, expectedBaseFee]

/-- The first London block, whose parent is before London, has the initial base fee. -/
theorem baseFee_of_validateHeader_first (h : .london ≤ fork) (hParent : ¬ .london ≤ parentFork)
    (hv : validateHeader hFork parent header schedule = .ok ()) :
    header.baseFeePerGas h = INITIAL_BASE_FEE := by
  rw [baseFeeAcross_of_validateHeader h hv]
  simp [expectedBaseFeeAcross, hParent]

/-- From Dencun, with a parent from London on, a header has the excess blob gas its parent gives. -/
theorem excessBlobGas_of_validateHeader (hLondon : .london ≤ parentFork) (h : .dencun ≤ fork)
    (hv : validateHeader hFork parent header schedule = .ok ()) :
    (header.excessBlobGas h).toNat = expectedExcessBlobGas hLondon h parent schedule := by
  have := check_of_validateHeader hv
    (c := (decide ((header.excessBlobGas h).toNat =
        expectedExcessBlobGas hLondon h parent schedule),
      .wrongExcessBlobGas (expectedExcessBlobGas hLondon h parent schedule)
        (header.excessBlobGas h).toNat))
    (by simp [headerChecks, h, hLondon])
  simpa using this

/-- From Paris on, a valid header has a parent from London on. -/
theorem london_le_of_validateHeader (h : .paris ≤ fork)
    (hv : validateHeader hFork parent header schedule = .ok ()) : .london ≤ parentFork := by
  have := check_of_validateHeader hv
    (c := (decide (.london ≤ parentFork), .parentBeforeLondon)) (by simp [headerChecks, h])
  simpa using this

/-- A valid header follows its parent: one number higher, and later in time. -/
theorem number_timestamp_of_validateHeader
    (hv : validateHeader hFork parent header schedule = .ok ()) :
    header.number = parent.number + 1 ∧ parent.timestamp.toNat < header.timestamp.toNat := by
  constructor
  · simpa using check_of_validateHeader hv
      (c := (decide (header.number = parent.number + 1), .wrongNumber)) (by simp [headerChecks])
  · simpa using check_of_validateHeader hv
      (c := (decide (parent.timestamp.toNat < header.timestamp.toNat), .timestampNotAfterParent))
      (by simp [headerChecks])

/-- Before Paris, a valid header has the difficulty that its parent gives. -/
theorem difficulty_of_validateHeader (h : fork < .paris)
    (hv : validateHeader hFork parent header schedule = .ok ()) :
    header.difficulty = expectedDifficulty parent header := by
  have := check_of_validateHeader hv
    (c := (decide (header.difficulty = expectedDifficulty parent header),
      .wrongDifficulty (expectedDifficulty parent header) header.difficulty))
    (by simp [headerChecks, h])
  simpa using this

/-- Before Paris, a valid header carries a valid proof of work. -/
theorem checkProofOfWork_of_validateHeader (h : fork < .paris)
    (hv : validateHeader hFork parent header schedule = .ok ()) :
    checkProofOfWork header = .ok () := by
  unfold validateHeader at hv
  rw [checkHeader_of_validateHeader hv] at hv
  simp only [h, ↓reduceIte, bind, Except.bind] at hv
  cases hp : checkProofOfWork header with
  | error e => simp [hp, Except.mapError] at hv
  | ok u => rfl

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
