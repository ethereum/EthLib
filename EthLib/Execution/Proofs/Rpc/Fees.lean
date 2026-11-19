module

public import EthLib.Execution.Rpc.Fees
public import EthLib.Execution.Proofs.Rpc.View

/-!
# Proofs: the fee history

A fee history lists the base fee of each block of its range, the header's or 0 before London.

Its list of base fees ends with the base fee that the header rule gives to the next block.

In a valid view, that is the base fee in the header of the next canonical block, from London on.

That holds for the first London block too, which takes the initial base fee.

`eth_baseFee` gives the last base fee of the history of the head alone.

Each list of base fees has one more entry than the list of gas ratios.

Each reward of a block with transactions, and as many receipts, is the tip of one of them.

Along strictly increasing percentiles, the rewards of a block do not decrease.
-/

public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Transactions (effectiveGasPrice)

namespace ChainView

/-- The fork of the block after a block is never before the fork of the block. -/
private theorem nextFork_ge (r : BlockRecord) (config : ChainConfig) :
    r.fork ≤ r.nextFork config := by
  unfold BlockRecord.nextFork
  split
  · split
    · assumption
    · exact Nat.le_refl _
  · exact Nat.le_refl _

/-- A fee history succeeds exactly when its percentiles strictly increase.

The node must also hold the newest block, and the history is then that of its range. -/
theorem feeHistory_eq_ok {v : ChainView} {count : Nat} {newest : BlockParam}
    {ps : List Percentile} {h : FeeHistory} :
    v.feeHistory count newest ps = .ok h ↔
      percentilesIncreasing ps = true ∧ ∃ last, v.resolve newest = .ok (some last) ∧
        h = { oldestBlock := ((v.feeHistoryBlocks count last).head?.map
                (·.block.header.number)).getD (last.block.header.number + 1)
              baseFeePerGas :=
                (v.feeHistoryBlocks count last).map (·.baseFee) ++ [last.nextBaseFee v.config]
              baseFeePerBlobGas := (v.feeHistoryBlocks count last).map (·.blobGasPrice v.config) ++
                [last.nextBlobBaseFee v.config]
              gasUsedRatio := (v.feeHistoryBlocks count last).map
                fun r => (r.block.header.gasUsed, r.block.header.gasLimit)
              blobGasUsedRatio := (v.feeHistoryBlocks count last).map (·.blobGasRatio v.config)
              reward := if ps.isEmpty then none
                else some ((v.feeHistoryBlocks count last).map (·.rewards ps)) } := by
  unfold feeHistory
  cases hp : percentilesIncreasing ps <;> cases hr : v.resolve newest with
  | error e => simp [bind, Except.bind, throw, throwThe, MonadExcept.throw]
  | ok o =>
    cases o <;> simp [bind, Except.bind, throw, throwThe, MonadExcept.throw, pure, Except.pure] <;>
      exact eq_comm

/-- The base fee of each block of a history is that of its header, or 0 before London.

The last base fee is the one that the header rule gives to the next block, or 0 before London. -/
theorem feeHistory_baseFeePerGas {v : ChainView} {count : Nat} {newest : BlockParam}
    {ps : List Percentile} {h : FeeHistory} {last : BlockRecord}
    (hok : v.feeHistory count newest ps = .ok h) (hlast : v.resolve newest = .ok (some last)) :
    h.baseFeePerGas = (v.feeHistoryBlocks count last).map
        (fun r => if hl : .london ≤ r.fork then r.block.header.baseFeePerGas hl else 0) ++
      [if .london ≤ last.nextFork v.config then expectedBaseFeeAcross last.block.header
        else 0] := by
  obtain ⟨-, last', hr, rfl⟩ := feeHistory_eq_ok.mp hok
  rw [hlast] at hr
  cases hr
  rfl

/-- The lists of base fees of a history have one more entry than its list of gas ratios. -/
theorem feeHistory_length {v : ChainView} {count : Nat} {newest : BlockParam}
    {ps : List Percentile} {h : FeeHistory} (hok : v.feeHistory count newest ps = .ok h) :
    h.baseFeePerGas.length = h.gasUsedRatio.length + 1 ∧
      h.baseFeePerBlobGas.length = h.gasUsedRatio.length + 1 ∧
      h.blobGasUsedRatio.length = h.gasUsedRatio.length := by
  obtain ⟨-, last, -, rfl⟩ := feeHistory_eq_ok.mp hok
  simp

/-- `eth_baseFee` gives the last base fee of the history of the head alone, with no percentile. -/
theorem baseFee_eq_feeHistory (v : ChainView) :
    (v.feeHistory 1 (.tag .latest) []).map (·.baseFeePerGas.getLast?) = .ok (some v.baseFee) := by
  rw [feeHistory_eq_ok.mpr ⟨rfl, v.head, rfl, rfl⟩]
  simp [baseFee, Except.map]

/-- In a valid view, take a canonical block that is not the head.

Let the next block and the fork that the history gives it both be from London on.

The header rule gives the next block the base fee in the header of that next block. -/
theorem Valid.nextBaseFee {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal) {i : Nat}
    (hi : i + 1 < v.canonical.length) (hNext : .london ≤ v.canonical[i].nextFork v.config)
    (hl1 : .london ≤ v.canonical[i + 1].fork) :
    v.canonical[i].nextBaseFee v.config = v.canonical[i + 1].baseFee := by
  obtain ⟨hst, -⟩ := hv.follows i hi
  obtain ⟨parent, hlast, _hFork, hch⟩ := checkBlock_checkHeader (stateTransition_eq_ok hst).2.2.1
  rw [chainAt_getLast] at hlast
  cases hlast
  have hbf := (checkHeader_eq_ok_iff.mp hch).2.2.2.2.2.1 hl1
  simp only [BlockRecord.nextBaseFee, BlockRecord.baseFee, hNext, hl1, ↓reduceIte, ↓reduceDIte,
    hbf]
  rfl

/-- In a valid view, the block after a canonical block from London on is from London on.

So is the fork that the history gives it. -/
theorem Valid.london_le_next {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal) {i : Nat}
    (hi : i + 1 < v.canonical.length) (hLondon : .london ≤ v.canonical[i].fork) :
    .london ≤ v.canonical[i].nextFork v.config ∧ .london ≤ v.canonical[i + 1].fork := by
  obtain ⟨hst, -⟩ := hv.follows i hi
  obtain ⟨parent, hlast, hFork, -⟩ := checkBlock_checkHeader (stateTransition_eq_ok hst).2.2.1
  rw [chainAt_getLast] at hlast
  cases hlast
  exact ⟨Nat.le_trans hLondon (nextFork_ge _ _), Nat.le_trans hLondon hFork⟩

end ChainView

namespace BlockRecord

/-- The tip at a percentile of two or more entries: the first one's, or one of the rest. -/
private theorem tipAt_cons_cons (p : Percentile) (total before tip gas : Nat) (b : Nat × Nat)
    (rest : List (Nat × Nat)) :
    tipAt p total before ((tip, gas) :: b :: rest) =
      if p.num * total ≤ (before + gas) * 100 * 10 ^ p.exponent then tip
      else tipAt p total (before + gas) (b :: rest) := rfl

/-- The tip at a percentile of a nonempty list is the tip of one of its entries. -/
private theorem tipAt_mem (p : Percentile) (total : Nat) :
    ∀ (before : Nat) (l : List (Nat × Nat)), l ≠ [] → tipAt p total before l ∈ l.map (·.1)
  | _, [], h => absurd rfl h
  | _, [(tip, _)], _ => by simp [tipAt]
  | before, (tip, gas) :: b :: rest, _ => by
    rw [tipAt_cons_cons]
    split
    · simp
    · exact List.mem_cons_of_mem _ (tipAt_mem p total _ (b :: rest) (by simp))

/-- A gas share that reaches a percentile also reaches any lower percentile. -/
private theorem reaches_of_lt {p q : Percentile} (hpq : p.lt q = true) {total s : Nat}
    (h : q.num * total ≤ s * 10 ^ q.exponent) : p.num * total ≤ s * 10 ^ p.exponent := by
  simp only [Percentile.lt, decide_eq_true_eq] at hpq
  have hpos : 0 < 10 ^ q.exponent := Nat.pow_pos (by decide)
  apply Nat.le_of_mul_le_mul_right _ hpos
  calc p.num * total * 10 ^ q.exponent = p.num * 10 ^ q.exponent * total := by ac_rfl
    _ ≤ q.num * 10 ^ p.exponent * total := Nat.mul_le_mul_right _ (Nat.le_of_lt hpq)
    _ = q.num * total * 10 ^ p.exponent := by ac_rfl
    _ ≤ s * 10 ^ q.exponent * 10 ^ p.exponent := Nat.mul_le_mul_right _ h
    _ = s * 10 ^ p.exponent * 10 ^ q.exponent := by ac_rfl

/-- On tips sorted in ascending order, the tip at a lower percentile is not above. -/
private theorem tipAt_mono {p q : Percentile} (hpq : p.lt q = true) (total : Nat) :
    ∀ (before : Nat) (l : List (Nat × Nat)), l.Pairwise (fun a b => a.1 ≤ b.1) →
      tipAt p total before l ≤ tipAt q total before l
  | _, [], _ => Nat.le_refl _
  | _, [_], _ => Nat.le_refl _
  | before, (tip, gas) :: b :: rest, hl => by
    rw [tipAt_cons_cons, tipAt_cons_cons]
    split
    · split
      · exact Nat.le_refl _
      · obtain ⟨c, hc, hce⟩ := List.mem_map.mp (tipAt_mem q total (before + gas) (b :: rest)
          (by simp))
        rw [← hce]
        exact (List.pairwise_cons.mp hl).1 c hc
    · split
      · rename_i h1 h2
        exact absurd (reaches_of_lt hpq h2) h1
      · exact tipAt_mono hpq total _ _ (List.pairwise_cons.mp hl).2

/-- A map that does not decrease along each step of increasing percentiles is sorted. -/
private theorem pairwise_of_increasing {f : Percentile → Nat}
    (hf : ∀ p q, p.lt q = true → f p ≤ f q) :
    ∀ ps, percentilesIncreasing ps = true → (ps.map f).Pairwise (· ≤ ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => by simp
  | p :: q :: rest, h => by
    simp only [percentilesIncreasing, Bool.and_eq_true] at h
    have ih := pairwise_of_increasing hf (q :: rest) h.2
    rw [List.map_cons, List.pairwise_cons]
    refine ⟨?_, ih⟩
    rw [List.map_cons, List.pairwise_cons] at ih
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hf _ _ h.1
    · exact Nat.le_trans (hf _ _ h.1) (ih.1 x hx)

/-- Each reward of a block with transactions, and as many receipts, is a tip.

It is the price per gas that one of its transactions pays, minus the base fee of the block. -/
theorem mem_rewards {r : BlockRecord} {ps : List Percentile} {x : Nat}
    (hlen : r.receipts.length = r.block.transactions.length) (hne : r.block.transactions ≠ [])
    (hx : x ∈ r.rewards ps) :
    ∃ tx ∈ r.block.transactions, x = effectiveGasPrice r.baseFee tx - r.baseFee := by
  simp only [rewards, List.mem_map] at hx
  obtain ⟨p, -, rfl⟩ := hx
  have hlenG : r.gasUsedList.length = r.block.transactions.length := by
    simp [gasUsedList, hlen]
  have htips : r.tips.map (·.1) =
      r.block.transactions.map fun tx => effectiveGasPrice r.baseFee tx - r.baseFee := by
    simp [tips, List.map_fst_zip, hlenG]
  have hperm : r.sortedTips.Perm r.tips := List.mergeSort_perm _ _
  have hne' : r.sortedTips ≠ [] := by
    intro h0
    have := hperm.length_eq
    rw [h0] at this
    simp [tips, hlenG] at this
    exact hne (List.length_eq_zero_iff.mp this.symm)
  have hm := (hperm.map (·.1)).subset (tipAt_mem p (r.sortedTips.map (·.2)).sum 0 _ hne')
  rw [htips, List.mem_map] at hm
  obtain ⟨tx, htx, heq⟩ := hm
  exact ⟨tx, htx, heq.symm⟩

/-- The rewards of a block without transactions are all 0. -/
theorem rewards_nil {r : BlockRecord} (h : r.block.transactions = []) (ps : List Percentile) :
    r.rewards ps = ps.map fun _ => 0 := by
  simp [rewards, sortedTips, tips, h, tipAt]

/-- Along strictly increasing percentiles, the rewards of a block do not decrease. -/
theorem rewards_sorted (r : BlockRecord) {ps : List Percentile}
    (hps : percentilesIncreasing ps = true) : (r.rewards ps).Pairwise (· ≤ ·) := by
  have hs : r.sortedTips.Pairwise (fun a b => a.1 ≤ b.1) :=
    (List.pairwise_mergeSort (le := fun a b => decide (a.1 ≤ b.1))
      (fun _ _ _ h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simpa using Nat.le_total a.1 b.1) r.tips).imp (by simp)
  exact pairwise_of_increasing (fun p q hpq => tipAt_mono hpq _ 0 _ hs) ps hps

end BlockRecord

end EthLib.Execution.Rpc
