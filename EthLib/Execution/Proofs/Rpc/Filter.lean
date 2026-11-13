module

public import EthLib.Execution.Rpc.Methods
public import EthLib.Execution.Proofs.Rpc.Receipt
public import EthLib.Execution.Proofs.Blocks.Bloom

/-!
# Proofs: the log filters

The logs that a filter returns match it, and lie in the blocks that it reads.

Each log of those blocks that matches the filter is returned.

A range reads the canonical blocks between its bounds, and a number bound lies within the chain.

In a valid view, take a canonical block after the lowest.

The Bloom filter of its header covers the logs of its receipts.

Suppose its Bloom filter excludes the addresses or a topic position of a filter.

Then the block has no log that the filter selects.
-/

public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Transactions

/-- A transaction that enters the body adds one receipt, and its logs to those of the body. -/
private theorem applyTransaction_logs {fork : Fork} {env : Evm.BlockEnvironment fork}
    {index : Nat} {before after : BodyOutput fork} {tx : Transaction}
    (h : applyTransaction env index before tx = .ok after) :
    ∃ outcome logs, after.receipts =
      before.receipts ++ [(tx.type, makeReceipt outcome after.cumulativeGasUsed logs)] ∧
      after.logs = before.logs ++ logs := by
  unfold applyTransaction at h
  obtain ⟨included, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨out, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨body, -, h⟩ := bind_ok_iff.mp h
  dsimp only at h
  split at h <;>
    (obtain ⟨_, -, h⟩ := bind_ok_iff.mp h; cases h; exact ⟨_, _, rfl, rfl⟩)

/-- The logs of the receipts of the transactions of a body are the logs of the body. -/
private theorem applyTransactions_logs {fork : Fork} {env : Evm.BlockEnvironment fork}
    {body : BodyState} {transactions : List Transaction} {output : BodyOutput fork}
    (h : applyTransactions env body transactions = .ok output) :
    output.receipts.flatMap (·.2.logs) = output.logs := by
  obtain ⟨hR, -⟩ := applyTransactions_steps
    (fun a b : BodyOutput fork =>
      a.receipts.flatMap (·.2.logs) = a.logs → b.receipts.flatMap (·.2.logs) = b.logs)
    (fun _ => id) (fun h₁ h₂ x => h₂ (h₁ x))
    (fun {index before after tx} hstep hinv => by
      obtain ⟨outcome, logs, hr, hl⟩ := applyTransaction_logs hstep
      rw [hr, hl, List.flatMap_append, hinv]
      simp [makeReceipt]) h
  exact hR rfl

/-- A body that runs keeps the receipts and logs of its transactions, which run on some body. -/
private theorem applyBody_run {fork : Fork} {config : ChainConfig}
    {env : Evm.BlockEnvironment fork} {block : Block fork Transaction} {start : State.BlockState}
    {output : BlockOutput fork} (h : applyBody config env block start = .ok output) :
    ∃ body txs, applyTransactions env body block.transactions = .ok txs ∧
      output.receipts = txs.receipts ∧ output.logs = txs.logs := by
  unfold applyBody at h
  dsimp only at h
  obtain ⟨state, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨body, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨txs, hTxs, h⟩ := bind_ok_iff.mp h
  refine ⟨body, txs, hTxs, ?_⟩
  split at h
  · obtain ⟨tx, -, h⟩ := bind_ok_iff.mp h
    obtain ⟨withdrawn, -, h⟩ := bind_ok_iff.mp h
    obtain ⟨⟨requested, requests⟩, -, h⟩ := bind_ok_iff.mp h
    dsimp only at h
    obtain ⟨rewarded, -, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
    cases h
    exact ⟨rfl, rfl⟩
  · obtain ⟨withdrawn, -, h⟩ := bind_ok_iff.mp h
    obtain ⟨⟨requested, requests⟩, -, h⟩ := bind_ok_iff.mp h
    dsimp only at h
    obtain ⟨rewarded, -, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
    cases h
    exact ⟨rfl, rfl⟩

namespace ChainView

/-- The logs that the method returns are the matching ones among the receipt objects of the blocks.

They are those of the objects that one call per block gives. -/
private theorem getLogs_eq_ok {v : ChainView} {f : Filter} {logs : List LogInfo}
    (h : v.getLogs f = .ok logs) :
    ∃ blocks infos, v.filterBlocks f.blocks = .ok blocks ∧
      blocks.mapM (·.receiptInfos v.config) = .ok infos ∧
      logs = (infos.flatten.flatMap (·.logs)).filter (f.selects ·.log) := by
  unfold getLogs at h
  obtain ⟨blocks, hb, h⟩ := bind_ok_iff.mp h
  unfold matchingLogs at h
  obtain ⟨infos, hi, h⟩ := bind_ok_iff.mp h
  exact ⟨blocks, infos, hb, hi, by simpa [pure, Except.pure] using h.symm⟩

/-- A number bound resolves to itself, between the lowest block and the head. -/
theorem boundNumber_number {v : ChainView} {n m : Nat}
    (h : v.boundNumber (some (.number n)) = .ok m) :
    m = n ∧ v.lowest.block.header.number ≤ n ∧ n ≤ v.head.block.header.number := by
  unfold boundNumber at h
  by_cases h1 : v.head.block.header.number < n
  · simp [h1] at h
  · by_cases h2 : n < v.lowest.block.header.number
    · simp [h1, h2] at h
    · simp only [h1, h2, ite_false] at h
      cases h
      omega

/-- A range reads exactly the canonical blocks between its two bounds, which are in order. -/
theorem filterBlocks_range {v : ChainView} {fromBlock toBlock : Option BlockParam}
    {blocks : List BlockRecord} (h : v.filterBlocks (.range fromBlock toBlock) = .ok blocks) :
    ∃ first last, v.boundNumber fromBlock = .ok first ∧ v.boundNumber toBlock = .ok last ∧
      first ≤ last ∧ blocks = v.canonical.filter fun r =>
        first ≤ r.block.header.number && r.block.header.number ≤ last := by
  unfold filterBlocks at h
  obtain ⟨first, h1, h⟩ := bind_ok_iff.mp h
  obtain ⟨last, h2, h⟩ := bind_ok_iff.mp h
  by_cases hl : last < first
  · simp [hl, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp only [hl, ite_false, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h
    exact ⟨first, last, h1, h2, by omega, h.symm⟩

/-- A block hash reads the one block of that hash that the node holds. -/
theorem filterBlocks_hash {v : ChainView} {hash : Hash32} {blocks : List BlockRecord}
    (h : v.filterBlocks (.hash hash) = .ok blocks) :
    ∃ r, blocks = [r] ∧ r ∈ v.canonical ++ v.side ∧ r.hash = hash := by
  unfold filterBlocks at h
  rcases hf : v.byHash hash with _ | r
  · simp [hf] at h
  · simp only [hf] at h
    cases h
    have := List.find?_some (p := fun r : BlockRecord => r.hash == hash) hf
    exact ⟨r, rfl, List.mem_of_find?_eq_some hf, by simpa using this⟩

/-- Soundness: every log that a filter returns matches it, and is a log of a block that it reads.

The log is in the receipt object of a transaction of that block. -/
theorem getLogs_sound {v : ChainView} {f : Filter} {logs : List LogInfo}
    (h : v.getLogs f = .ok logs) :
    ∃ blocks, v.filterBlocks f.blocks = .ok blocks ∧ ∀ l ∈ logs, f.selects l.log = true ∧
      ∃ r ∈ blocks, ∃ infos, r.receiptInfos v.config = .ok infos ∧
        ∃ info ∈ infos, l ∈ info.logs := by
  obtain ⟨blocks, infos, hb, hi, rfl⟩ := getLogs_eq_ok h
  refine ⟨blocks, hb, fun l hl => ?_⟩
  obtain ⟨hl, hs⟩ := List.mem_filter.mp hl
  refine ⟨by simpa using hs, ?_⟩
  obtain ⟨info, hinfo, hlinfo⟩ := List.mem_flatMap.mp hl
  obtain ⟨is, his, hinfo⟩ := List.mem_flatten.mp hinfo
  obtain ⟨r, hr, hri⟩ := mapM_ok_mem hi is his
  exact ⟨r, hr, is, hri, info, hinfo, hlinfo⟩

/-- Completeness: every log of a block that a filter reads, which matches the filter, is returned.

That holds whenever the method returns logs. -/
theorem getLogs_complete {v : ChainView} {f : Filter} {logs : List LogInfo}
    (h : v.getLogs f = .ok logs) {blocks : List BlockRecord}
    (hb : v.filterBlocks f.blocks = .ok blocks) {r : BlockRecord} (hr : r ∈ blocks)
    {infos : List ReceiptInfo} (hi : r.receiptInfos v.config = .ok infos) {info : ReceiptInfo}
    (hinfo : info ∈ infos) {l : LogInfo} (hl : l ∈ info.logs) (hs : f.selects l.log = true) :
    l ∈ logs := by
  obtain ⟨blocks', infos', hb', hi', rfl⟩ := getLogs_eq_ok h
  obtain rfl : blocks = blocks' := Except.ok.inj (hb.symm.trans hb')
  obtain ⟨is, his, hris⟩ := exists_mem_of_mapM_ok hi' hr
  obtain rfl : infos = is := Except.ok.inj (hi.symm.trans hris)
  refine List.mem_filter.mpr ⟨List.mem_flatMap.mpr
    ⟨info, List.mem_flatten.mpr ⟨infos, his, hinfo⟩, hl⟩, by simpa using hs⟩

/-- In a valid view, the logs of the receipts of a canonical block after the lowest are its logs. -/
theorem Valid.logs_receipts {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal) {i : Nat}
    (hi : i + 1 < v.canonical.length) :
    v.canonical[i + 1].receipts.flatMap (·.2.logs) = v.canonical[i + 1].logs := by
  obtain ⟨-, result, hrun, hrec, hlog⟩ := hv.follows i hi
  obtain ⟨hashes, -, happly, -⟩ := Blocks.runBody_eq_ok.mp hrun
  obtain ⟨body, txs, htxs, hr, hl⟩ := applyBody_run happly
  rw [← hrec, ← hlog, hr, hl]
  exact applyTransactions_logs htxs

/-- In a valid view, the Bloom filter of a canonical block after the lowest is that of its logs. -/
theorem Valid.logsBloom_eq {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal) {i : Nat}
    (hi : i + 1 < v.canonical.length) :
    logsBloom v.canonical[i + 1].logs = v.canonical[i + 1].block.header.bloom := by
  obtain ⟨hst, result, hbody, -, hlog⟩ := hv.follows i hi
  obtain ⟨-, -, -, hashes, output, roots, hh, hout, hroots, hchecks, -⟩ :=
    stateTransition_eq_ok hst
  obtain ⟨hashes', hh', hout', -⟩ := runBody_eq_ok.mp hbody
  obtain rfl : hashes = hashes' := Except.ok.inj (hh.symm.trans hh')
  obtain rfl : output = result.output := Except.ok.inj (hout.symm.trans hout')
  rw [← hlog]
  exact (of_outputChecks hchecks).2.2

/-- In a valid view, take a canonical block after the lowest, and a filter.

Suppose that the Bloom filter of its header has none of the addresses that the filter takes.

Or suppose that at some position, the filter takes some topics and the Bloom filter has none.

Then no log of the block matches the filter. -/
theorem Valid.not_selects_of_bloom {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal)
    {i : Nat} (hi : i + 1 < v.canonical.length) {f : Filter} {bloom : BitVec 2048}
    (hb : Bloom.toBytes bloom = v.canonical[i + 1].block.header.bloom)
    (hex : (∃ addresses, f.address = some addresses ∧
        ∀ a : Address, a ∈ addresses → Bloom.mayContain bloom ⟨a.toArray⟩ = false) ∨
      ∃ (k : Nat) (ts : List Hash32), f.topics[k]? = some (some ts) ∧ ts ≠ [] ∧
        ∀ t : Hash32, t ∈ ts → Bloom.mayContain bloom ⟨t.toArray⟩ = false) :
    ∀ log ∈ v.canonical[i + 1].logs, f.selects log = false := by
  intro log hlog
  have hbloom : bloom = Bloom.ofLogs v.canonical[i + 1].logs :=
    Bloom.toBytes_injective (hb.trans (hv.logsBloom_eq hi).symm)
  subst hbloom
  rcases hex with ⟨addresses, hf, hno⟩ | ⟨k, ts, hk, hne, hno⟩
  · have hnot : log.address ∉ addresses := fun hmem => by
      have := hno _ hmem
      rw [Bloom.mayContain_address hlog] at this
      exact absurd this (by simp)
    simp [Filter.selects, hf, hnot]
  · have hk' : (some ts, k) ∈ f.topics.zipIdx := by
      obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hk
      exact List.mem_iff_getElem?.mpr ⟨k, by simp [hk]⟩
    have hfalse : Filter.takesTopic (some ts) log.topics[k]? = false := by
      rcases hl : log.topics[k]? with _ | t
      · cases ts with
        | nil => exact absurd rfl hne
        | cons _ _ => rfl
      · have ht : t ∈ log.topics := List.mem_of_getElem? hl
        have hnot : t ∉ ts := fun hmem => by
          have := hno _ hmem
          rw [Bloom.mayContain_topic hlog ht] at this
          exact absurd this (by simp)
        cases ts with
        | nil => exact absurd rfl hne
        | cons _ _ => simpa [Filter.takesTopic] using hnot
    have hall : f.topics.zipIdx.all (fun (taken, k) => Filter.takesTopic taken log.topics[k]?)
        = false := by
      rw [Bool.eq_false_iff]
      intro h
      have := List.all_eq_true.mp h _ hk'
      simp only at this
      rw [hfalse] at this
      exact absurd this (by simp)
    simp [Filter.selects, hall]

end ChainView

end EthLib.Execution.Rpc
