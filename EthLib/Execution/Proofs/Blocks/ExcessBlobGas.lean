module

public import EthLib.Execution.Proofs.Blocks.Transition
public import EthLib.Execution.Proofs.Blocks.Validate
public import EthLib.Execution.Proofs.Blocks.BodyGas
public import EthLib.Execution.Proofs.Fees.BlobBaseFee

/-!
# Proofs: the excess blob gas along a chain of headers

From Dencun, a header has the excess blob gas that its parent gives under its blob schedule.

A parent within the maximum of that schedule raises it by at most `GAS_PER_BLOB * (max - target)`.

So along headers that each pass the header check, the excess grows at most that much per header.

Along blocks that pass their transitions, the same holds when no blob maximum falls.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Fees
open EthLib.Execution.Fees.BlobBaseFee (GAS_PER_BLOB chainBlobSchedule)

/-- A bound on the rise of the excess blob gas over `k` headers, under their schedules.

Header `i + 1` adds `GAS_PER_BLOB * (max - target)` of its own schedule. -/
def excessBlobGasGrowth {forks : Nat → Fork} (dencun : ∀ i, .dencun ≤ forks i)
    (schedules : (i : Nat) → Since .dencun (forks i) BlobSchedule) (k : Nat) : Nat :=
  ((List.range k).map fun i =>
    GAS_PER_BLOB *
      ((schedules (i + 1) (dencun (i + 1))).max -
        (schedules (i + 1) (dencun (i + 1))).target)).sum

/-- One more header adds the bound of its own schedule. -/
theorem excessBlobGasGrowth_succ {forks : Nat → Fork} (dencun : ∀ i, .dencun ≤ forks i)
    (schedules : (i : Nat) → Since .dencun (forks i) BlobSchedule) (k : Nat) :
    excessBlobGasGrowth dencun schedules (k + 1) =
      excessBlobGasGrowth dencun schedules k + GAS_PER_BLOB *
        ((schedules (k + 1) (dencun (k + 1))).max -
          (schedules (k + 1) (dencun (k + 1))).target) := by
  simp [excessBlobGasGrowth, List.range_succ]

/-- Along valid headers from Dencun, the excess grows by at most the bounds of the children.

Header `i + 1` passes the header check against header `i`, under its own blob schedule.

Each parent uses at most the blob gas of the maximum of its child's schedule. -/
theorem excessBlobGas_le_of_checkHeader {forks : Nat → Fork} {k : Nat}
    (mono : ∀ i < k, forks i ≤ forks (i + 1)) (dencun : ∀ i, .dencun ≤ forks i)
    {headers : (i : Nat) → Header (forks i)}
    {schedules : (i : Nat) → Since .dencun (forks i) BlobSchedule}
    (valid : ∀ i (hi : i < k),
      checkHeader (mono i hi) (headers i) (headers (i + 1)) (schedules (i + 1)) = .ok ())
    (used : ∀ i < k, ((headers i).blobGasUsed (dencun i)).toNat ≤
      GAS_PER_BLOB * (schedules (i + 1) (dencun (i + 1))).max) :
    ((headers k).excessBlobGas (dencun k)).toNat ≤
      ((headers 0).excessBlobGas (dencun 0)).toNat + excessBlobGasGrowth dencun schedules k := by
  induction k with
  | zero => simp [excessBlobGasGrowth]
  | succ k ih =>
    have hk := valid k (Nat.lt_succ_self k)
    have hLondon : .london ≤ forks k := Nat.le_trans (by decide) (dencun k)
    have hExcess := excessBlobGas_of_checkHeader hLondon (dencun (k + 1)) hk
    have hUsed := used k (Nat.lt_succ_self k)
    -- The parent's excess and blob gas used are its fields, since it is from Dencun.
    have hStep : ((headers (k + 1)).excessBlobGas (dencun (k + 1))).toNat ≤
        ((headers k).excessBlobGas (dencun k)).toNat +
          GAS_PER_BLOB * ((schedules (k + 1) (dencun (k + 1))).max -
            (schedules (k + 1) (dencun (k + 1))).target) := by
      rw [hExcess]
      simp only [expectedExcessBlobGas, parentExcessBlobGas, parentBlobGasUsed, dencun k,
        ↓reduceDIte]
      exact BlobBaseFee.calcExcessBlobGas_le _ _ hUsed
    rw [excessBlobGasGrowth_succ]
    have := ih (fun i hi => mono i (Nat.lt_succ_of_lt hi))
      (fun i hi => valid i (Nat.lt_succ_of_lt hi)) (fun i hi => used i (Nat.lt_succ_of_lt hi))
    omega

/-- Under one blob schedule throughout, `k` headers add at most `k` times its bound.

The bound is `GAS_PER_BLOB * (max - target)` of that schedule. -/
theorem excessBlobGasGrowth_of_eq {forks : Nat → Fork} {dencun : ∀ i, .dencun ≤ forks i}
    {schedules : (i : Nat) → Since .dencun (forks i) BlobSchedule} {schedule : BlobSchedule}
    {k : Nat} (same : ∀ i, 0 < i → i ≤ k → schedules i (dencun i) = schedule) :
    excessBlobGasGrowth dencun schedules k =
      k * (GAS_PER_BLOB * (schedule.max - schedule.target)) := by
  induction k with
  | zero => simp [excessBlobGasGrowth]
  | succ k ih =>
    rw [excessBlobGasGrowth_succ, ih (fun i h1 h2 => same i h1 (Nat.le_succ_of_le h2)),
      same (k + 1) (Nat.succ_pos k) (Nat.le_refl _), Nat.succ_mul]

/-- From Dencun, a block that passes its transition uses at most the blob gas of its schedule.

That schedule is the one that its chain gives the block, and the bound is `GAS_PER_BLOB * max`. -/
theorem blobGasUsed_le_of_stateTransition {fork : Fork} (h : .dencun ≤ fork)
    {chain : BlockChain} {block : Block fork Transactions.Transaction} {checkSeal : Bool}
    {post : State.State} (applied : stateTransition chain block checkSeal = .ok post) :
    (block.header.blobGasUsed h).toNat ≤ GAS_PER_BLOB *
      (chainBlobSchedule chain.config fork block.header.number
        block.header.timestamp.toNat h).max := by
  obtain ⟨-, -, -, hashes, output, roots, -, hApply, -, hChecks, -⟩ := stateTransition_eq_ok applied
  obtain ⟨_, _, txs, _, _, _, _, hTxs, _, _, _, _, _, _, hGas, _⟩ := applyBody_eq_ok hApply
  rw [← blobGasUsed_of_outputChecks h hChecks, hGas]
  have := applyTransactions_blob_le hTxs
  simpa [Transactions.maxBlobGasPerBlock, h, blockEnvironment] using this

/-- A block that passes its transition on the chain after its parent passes the header check.

The check is against the parent, under the schedule that the chain gives the block. -/
private theorem checkHeader_of_addBlock {fork parentFork : Fork} {chain : BlockChain}
    {parent : Block parentFork Transactions.Transaction} {post : State.State}
    {block : Block fork Transactions.Transaction} {checkSeal : Bool} {post' : State.State}
    (applied : stateTransition (chain.addBlock parent post) block checkSeal = .ok post') :
    ∃ hFork : parentFork ≤ fork, checkHeader hFork parent.header block.header
      (chainBlobSchedule chain.config fork block.header.number
        block.header.timestamp.toNat) = .ok () := by
  obtain ⟨-, -, hCheck, -⟩ := stateTransition_eq_ok applied
  obtain ⟨p, hp, hFork, hc⟩ := checkBlock_checkHeader hCheck
  rw [BlockChain.addBlock_getLast?, Option.some.injEq] at hp
  subst hp
  exact ⟨hFork, hc⟩

/-- Along blocks that follow each other on a chain, the configuration stays the same. -/
private theorem config_eq_of_next {forks : Nat → Fork}
    {blocks : (i : Nat) → Block (forks i) Transactions.Transaction}
    {chains : Nat → BlockChain} {posts : Nat → State.State} {k : Nat}
    (next : ∀ i < k, chains (i + 1) = (chains i).addBlock (blocks i) (posts i)) :
    ∀ i ≤ k, (chains i).config = (chains 0).config := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    rw [next i hi, ← ih (Nat.le_of_lt hi)]
    rfl

/-- Along blocks from Dencun that pass their transitions, the excess grows by at most the bounds.

Each block runs on the chain after the block before it, and passes its transition there.

The bound of block `i + 1` is that of the schedule that the chain gives it.

It assumes that no block has a lower blob maximum than its parent. -/
theorem excessBlobGas_le_of_stateTransition {forks : Nat → Fork} (dencun : ∀ i, .dencun ≤ forks i)
    {blocks : (i : Nat) → Block (forks i) Transactions.Transaction}
    {chains : Nat → BlockChain} {posts : Nat → State.State} {checkSeal : Bool} {k : Nat}
    (next : ∀ i < k, chains (i + 1) = (chains i).addBlock (blocks i) (posts i))
    (applied : ∀ i ≤ k, stateTransition (chains i) (blocks i) checkSeal = .ok (posts i))
    (grows : ∀ i < k,
      (chainBlobSchedule (chains 0).config (forks i) (blocks i).header.number
        (blocks i).header.timestamp.toNat (dencun i)).max ≤
      (chainBlobSchedule (chains 0).config (forks (i + 1)) (blocks (i + 1)).header.number
        (blocks (i + 1)).header.timestamp.toNat (dencun (i + 1))).max) :
    ((blocks k).header.excessBlobGas (dencun k)).toNat ≤
      ((blocks 0).header.excessBlobGas (dencun 0)).toNat +
        excessBlobGasGrowth dencun (fun i => chainBlobSchedule (chains 0).config (forks i)
          (blocks i).header.number (blocks i).header.timestamp.toNat) k := by
  have hConfig := config_eq_of_next next
  -- Each step gives the header check of block `i + 1` against block `i`.
  have step : ∀ i (hi : i < k), ∃ hFork : forks i ≤ forks (i + 1),
      checkHeader hFork (blocks i).header (blocks (i + 1)).header
        (chainBlobSchedule (chains 0).config (forks (i + 1)) (blocks (i + 1)).header.number
          (blocks (i + 1)).header.timestamp.toNat) = .ok () := by
    intro i hi
    have h := applied (i + 1) hi
    rw [next i hi] at h
    rw [← hConfig i (Nat.le_of_lt hi)]
    exact checkHeader_of_addBlock h
  have used : ∀ i < k, ((blocks i).header.blobGasUsed (dencun i)).toNat ≤
      GAS_PER_BLOB * (chainBlobSchedule (chains 0).config (forks (i + 1))
        (blocks (i + 1)).header.number (blocks (i + 1)).header.timestamp.toNat
        (dencun (i + 1))).max := by
    intro i hi
    have h1 := blobGasUsed_le_of_stateTransition (dencun i) (applied i (Nat.le_of_lt hi))
    rw [hConfig i (Nat.le_of_lt hi)] at h1
    exact Nat.le_trans h1 (Nat.mul_le_mul_left _ (grows i hi))
  exact excessBlobGas_le_of_checkHeader (headers := fun i => (blocks i).header)
    (schedules := fun i => chainBlobSchedule (chains 0).config (forks i)
      (blocks i).header.number (blocks i).header.timestamp.toNat)
    (fun i hi => (step i hi).1) dencun (fun i hi => (step i hi).2) used

end EthLib.Execution.Blocks
