module

public import EthLib.Execution.Evm.Instructions.Storage
public import EthLib.Execution.Proofs.Evm.Instructions.Storage

/-!
# Proofs: the status of a slot that SSTORE writes

The original, current and new values of a slot fall in nine classes, from the cases of EIP-2200.

The writes that it neither refunds nor charges apart form one class.

At every fork, the price, the refund and the state gas of SSTORE depend only on that class.

Each price in execution gas fits 15 bits, and each refund a signed 16-bit integer.

Source: [EIP-2200](https://eips.ethereum.org/EIPS/eip-2200#specification).
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)
open GasCosts

/-- The class of a write to a slot, by its original, current and new values. -/
inductive SstoreStatus where
  /-- The write keeps the current value, or changes a dirty slot that holds a value other than 0.

  In the second case the new value is neither 0 nor the original. -/
  | assigned
  /-- A clean slot of 0 gets a value other than 0. -/
  | added
  /-- A clean slot of a value other than 0 gets 0. -/
  | deleted
  /-- A clean slot of a value other than 0 gets another value other than 0. -/
  | modified
  /-- A slot that was cleared in the transaction gets a value other than 0 and the original. -/
  | deletedAdded
  /-- A slot that changed in the transaction, from a value other than 0, gets 0. -/
  | modifiedDeleted
  /-- A slot that was cleared in the transaction gets its original value back. -/
  | deletedRestored
  /-- A slot of original 0 that got a value in the transaction gets 0 back. -/
  | addedDeleted
  /-- A slot that changed in the transaction to a value other than 0 gets its original value back.

  That original value is not 0. -/
  | modifiedRestored
  deriving DecidableEq, Repr

/-- The class of a write of `new` to a slot of value `current` and of original value `original`.

The original value is the value before the transaction. -/
def sstoreStatus (original current new : U256) : SstoreStatus :=
  -- A write of the current value changes nothing.
  if current = new then .assigned
  -- A clean slot holds its original value.
  else if original = current then
    if original = 0 then .added else if new = 0 then .deleted else .modified
  -- A dirty slot, cleared in the transaction.
  else if original ≠ 0 ∧ current = 0 then
    if original = new then .deletedRestored else .deletedAdded
  -- A dirty slot of original other than 0, which holds a value other than 0.
  else if original ≠ 0 ∧ new = 0 then .modifiedDeleted
  else if original ≠ 0 ∧ original = new then .modifiedRestored
  -- A dirty slot of original 0, which holds a value other than 0.
  else if original = 0 ∧ new = 0 then .addedDeleted
  else .assigned

/-- A write of each class: its original, current and new values, from 0, 1 and 2. -/
def SstoreStatus.witness : SstoreStatus → U256 × U256 × U256
  | .assigned => (0, 0, 0)
  | .added => (0, 0, 1)
  | .deleted => (1, 1, 0)
  | .modified => (1, 1, 2)
  | .deletedAdded => (1, 0, 2)
  | .modifiedDeleted => (1, 2, 0)
  | .deletedRestored => (1, 0, 1)
  | .addedDeleted => (0, 1, 0)
  | .modifiedRestored => (1, 2, 1)

/-- The witness of each class is a write of that class. -/
theorem sstoreStatus_witness (status : SstoreStatus) :
    sstoreStatus status.witness.1 status.witness.2.1 status.witness.2.2 = status := by
  cases status <;> decide

/-- The price of SSTORE is the price of the witness of the class of the write. -/
theorem sstoreCost_eq_witness (fork : Fork) (original current new : U256) (cold : Bool) :
    let w := (sstoreStatus original current new).witness
    sstoreCost fork original current new cold = sstoreCost fork w.1 w.2.1 w.2.2 cold := by
  unfold sstoreStatus
  by_cases h1 : current = new <;> by_cases h2 : original = current <;>
    by_cases h3 : original = 0 <;> by_cases h4 : current = 0 <;> by_cases h5 : new = 0 <;>
    by_cases h6 : original = new <;> simp_all [sstoreCost_eq, SstoreStatus.witness]

/-- The refund of SSTORE is the refund of the witness of the class of the write. -/
theorem sstoreRefund_eq_witness (fork : Fork) (original current new : U256) :
    let w := (sstoreStatus original current new).witness
    sstoreRefund fork original current new = sstoreRefund fork w.1 w.2.1 w.2.2 := by
  unfold sstoreStatus
  by_cases h1 : current = new <;> by_cases h2 : original = current <;>
    by_cases h3 : original = 0 <;> by_cases h4 : current = 0 <;> by_cases h5 : new = 0 <;>
    by_cases h6 : original = new <;> simp_all [sstoreRefund_eq, SstoreStatus.witness]

/-- The state gas that SSTORE charges is that of the witness of the class of the write. -/
theorem sstoreStateGas_eq_witness (fork : Fork) (original current new : U256) :
    let w := (sstoreStatus original current new).witness
    sstoreStateGas fork original current new = sstoreStateGas fork w.1 w.2.1 w.2.2 := by
  unfold sstoreStatus
  by_cases h1 : current = new <;> by_cases h2 : original = current <;>
    by_cases h3 : original = 0 <;> by_cases h4 : current = 0 <;> by_cases h5 : new = 0 <;>
    by_cases h6 : original = new <;> simp_all [sstoreStateGas_eq, SstoreStatus.witness]

/-- The state gas that SSTORE refills is that of the witness of the class of the write. -/
theorem sstoreStateRefill_eq_witness (fork : Fork) (original current new : U256) :
    let w := (sstoreStatus original current new).witness
    sstoreStateRefill fork original current new = sstoreStateRefill fork w.1 w.2.1 w.2.2 := by
  unfold sstoreStatus
  by_cases h1 : current = new <;> by_cases h2 : original = current <;>
    by_cases h3 : original = 0 <;> by_cases h4 : current = 0 <;> by_cases h5 : new = 0 <;>
    by_cases h6 : original = new <;> simp_all [sstoreStateRefill_eq, SstoreStatus.witness]

/-- At every fork, the price of SSTORE depends only on the class of the write. -/
theorem sstoreCost_eq_of_sstoreStatus_eq {fork : Fork} {original current new original' current'
    new' : U256} (h : sstoreStatus original current new = sstoreStatus original' current' new')
    (cold : Bool) :
    sstoreCost fork original current new cold = sstoreCost fork original' current' new' cold := by
  rw [sstoreCost_eq_witness, sstoreCost_eq_witness fork original', h]

/-- At every fork, the refund of SSTORE depends only on the class of the write. -/
theorem sstoreRefund_eq_of_sstoreStatus_eq {fork : Fork} {original current new original' current'
    new' : U256} (h : sstoreStatus original current new = sstoreStatus original' current' new') :
    sstoreRefund fork original current new = sstoreRefund fork original' current' new' := by
  rw [sstoreRefund_eq_witness, sstoreRefund_eq_witness fork original', h]

/-- At every fork, the state gas that SSTORE charges depends only on the class of the write. -/
theorem sstoreStateGas_eq_of_sstoreStatus_eq {fork : Fork} {original current new original'
    current' new' : U256}
    (h : sstoreStatus original current new = sstoreStatus original' current' new') :
    sstoreStateGas fork original current new = sstoreStateGas fork original' current' new' := by
  rw [sstoreStateGas_eq_witness, sstoreStateGas_eq_witness fork original', h]

/-- At every fork, the state gas that SSTORE refills depends only on the class of the write. -/
theorem sstoreStateRefill_eq_of_sstoreStatus_eq {fork : Fork} {original current new original'
    current' new' : U256}
    (h : sstoreStatus original current new = sstoreStatus original' current' new') :
    sstoreStateRefill fork original current new =
      sstoreStateRefill fork original' current' new' := by
  rw [sstoreStateRefill_eq_witness, sstoreStateRefill_eq_witness fork original', h]

/-- At every fork, the price of SSTORE in execution gas is below `2^15`. -/
theorem sstoreCost_lt (fork : Fork) (original current new : U256) (cold : Bool) :
    sstoreCost fork original current new cold < 2 ^ 15 := by
  rw [sstoreCost_eq_witness]
  cases sstoreStatus original current new <;> cases fork <;> cases cold <;> decide

/-- At every fork, the refund of SSTORE fits a signed 16-bit integer. -/
theorem sstoreRefund_mem (fork : Fork) (original current new : U256) :
    -2 ^ 15 ≤ sstoreRefund fork original current new ∧
      sstoreRefund fork original current new < 2 ^ 15 := by
  rw [sstoreRefund_eq_witness]
  cases sstoreStatus original current new <;> cases fork <;> decide

end EthLib.Execution.Evm
