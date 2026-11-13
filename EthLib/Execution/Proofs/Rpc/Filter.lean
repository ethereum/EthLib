module

public import EthLib.Execution.Rpc.Methods
public import EthLib.Execution.Proofs.Rpc.Receipt
public import EthLib.Execution.Proofs.Blocks.Bloom

/-!
# Proofs: the log filters

The logs that a filter returns match it, and lie in the blocks that it reads.

Each log of those blocks that matches the filter is returned.

A range reads the canonical blocks between its bounds.

It lies between the lowest block that the node holds and the head.

A number bound above the head is an invalid range, whatever the other bound.

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

/-- A log with fewer topics than a filter has topic positions does not match it.

This holds whatever each position takes. -/
theorem Filter.selects_eq_false_of_length_lt {f : Filter} {log : Log}
    (h : log.topics.length < f.topics.length) : f.selects log = false := by
  simp [Filter.selects, Nat.not_le.mpr h]

namespace ChainView

/-- The logs that the method returns are the matching ones among the receipt objects of the blocks.

They come in the order of the blocks, then of the logs in each block. -/
theorem getLogs_eq_ok {v : ChainView} {f : Filter} {logs : List LogInfo}
    (h : v.getLogs f = .ok logs) :
    ∃ blocks infos, v.filterBlocks f.blocks = .ok blocks ∧
      blocks.mapM (·.receiptInfos v.config) = .ok infos ∧
      logs = (infos.flatten.flatMap (·.logs)).filter (f.selects ·.log) := by
  unfold getLogs at h
  obtain ⟨blocks, hb, h⟩ := bind_ok_iff.mp h
  unfold matchingLogs at h
  obtain ⟨infos, hi, h⟩ := bind_ok_iff.mp h
  exact ⟨blocks, infos, hb, hi, by simpa [pure, Except.pure] using h.symm⟩

/-- Each log object of a receipt object of a block has the hash of that block. -/
private theorem receiptInfo_blockHash {r : BlockRecord} {config : ChainConfig}
    {index before firstLog : Nat} {tx : Transaction} {receipt : Receipt r.fork}
    {info : ReceiptInfo} (h : r.receiptInfo config index before firstLog tx receipt = .ok info) :
    ∀ l ∈ info.logs, l.blockHash = r.hash := by
  unfold BlockRecord.receiptInfo at h
  obtain ⟨ti, hti, h⟩ := bind_ok_iff.mp h
  obtain ⟨sender, hash, -, -, rfl⟩ := BlockRecord.transactionInfo_eq_ok.mp hti
  rcases hto : tx.to with _ | a
  · rcases hc : (Evm.createAddress sender tx.nonce.toNat) with e | ca
    · simp [hto, hc, bind, Except.bind, Functor.map, Except.map, Except.mapError] at h
    · simp [hto, hc, bind, Except.bind, pure, Except.pure, Functor.map, Except.map,
        Except.mapError] at h
      subst h
      simp only [List.mem_map, Prod.exists]
      rintro l ⟨x, i, -, rfl⟩
      rfl
  · simp [hto, bind, Except.bind, pure, Except.pure] at h
    subst h
    simp only [List.mem_map, Prod.exists]
    rintro l ⟨x, i, -, rfl⟩
    rfl

/-- A number bound above the head makes the range invalid, whatever the other bound. -/
theorem filterBlocks_aboveHead {v : ChainView} {fromBlock toBlock : Option BlockParam} {n : Nat}
    (hn : v.head.block.header.number < n)
    (hb : fromBlock = some (.number n) ∨ toBlock = some (.number n)) :
    v.filterBlocks (.range fromBlock toBlock) = .error (invalidRange "beyond the head") := by
  have hA : (v.aboveHead fromBlock || v.aboveHead toBlock) = true := by
    rcases hb with rfl | rfl <;> simp [aboveHead, hn]
  unfold filterBlocks
  simp [hA, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- A range whose bounds resolve above the head or out of order is invalid.

A pruned block does not change that error. -/
theorem filterBlocks_invalid {v : ChainView} {fromBlock toBlock : Option BlockParam}
    {first last : Nat} (h1 : v.boundNumber fromBlock = .ok first)
    (h2 : v.boundNumber toBlock = .ok last)
    (hl : v.head.block.header.number < last ∨ last < first) :
    ∃ reason, v.filterBlocks (.range fromBlock toBlock) = .error (invalidRange reason) := by
  unfold filterBlocks
  by_cases hA : (v.aboveHead fromBlock || v.aboveHead toBlock) = true
  · refine ⟨"beyond the head", ?_⟩
    simp [hA, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · by_cases hh : v.head.block.header.number < last
    · refine ⟨"beyond the head", ?_⟩
      simp [hA, h1, h2, hh, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
    · have hl : last < first := hl.resolve_left hh
      refine ⟨"the first bound is above the last", ?_⟩
      simp [hA, h1, h2, hh, hl, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- A range reads exactly the canonical blocks between its two bounds.

Its first bound is at least the lowest block, and at most its last, which is at most the head. -/
theorem filterBlocks_range {v : ChainView} {fromBlock toBlock : Option BlockParam}
    {blocks : List BlockRecord} (h : v.filterBlocks (.range fromBlock toBlock) = .ok blocks) :
    ∃ first last, v.boundNumber fromBlock = .ok first ∧ v.boundNumber toBlock = .ok last ∧
      v.lowest.block.header.number ≤ first ∧ first ≤ last ∧ last ≤ v.head.block.header.number ∧
      blocks = v.canonical.filter fun r =>
        first ≤ r.block.header.number && r.block.header.number ≤ last := by
  unfold filterBlocks at h
  by_cases hA : (v.aboveHead fromBlock || v.aboveHead toBlock) = true
  · simp [hA, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp only [hA, ite_false, Bool.false_eq_true, bind, Except.bind] at h
    obtain ⟨first, h1, h⟩ := bind_ok_iff.mp h
    obtain ⟨last, h2, h⟩ := bind_ok_iff.mp h
    by_cases hh : v.head.block.header.number < last
    · simp [hh, throw, throwThe, MonadExceptOf.throw] at h
    · by_cases hl : last < first
      · simp [hh, hl, throw, throwThe, MonadExceptOf.throw] at h
      · by_cases hp : first < v.lowest.block.header.number
        · simp [hh, hl, hp, throw, throwThe, MonadExceptOf.throw] at h
        · simp only [hh, hl, hp, ite_false, pure, Except.pure] at h
          cases h
          exact ⟨first, last, h1, h2, by omega, by omega, by omega, rfl⟩

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

/-- Completeness for the logs of a block: each log of its receipts that matches is returned.

It comes as an object of the block that it is a log of.

That holds whenever the method returns logs. -/
theorem getLogs_complete_log {v : ChainView} {f : Filter} {logs : List LogInfo}
    (h : v.getLogs f = .ok logs) {blocks : List BlockRecord}
    (hb : v.filterBlocks f.blocks = .ok blocks) {r : BlockRecord} (hr : r ∈ blocks) {log : Log}
    (hl : log ∈ r.receipts.flatMap (·.2.logs)) (hs : f.selects log = true) :
    ∃ l ∈ logs, l.log = log ∧ l.blockHash = r.hash := by
  obtain ⟨blocks', infos', hb', hi', -⟩ := getLogs_eq_ok h
  obtain rfl : blocks = blocks' := Except.ok.inj (hb.symm.trans hb')
  obtain ⟨is, -, hris⟩ := exists_mem_of_mapM_ok hi' hr
  obtain ⟨hlen, -, hall⟩ := BlockRecord.receiptInfos_eq_ok hris
  obtain ⟨p, hp, hlp⟩ := List.mem_flatMap.mp hl
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hp
  have hk' : k < is.length := by omega
  obtain ⟨tx, receipt, -, hrec, hri⟩ := hall k hk'
  obtain ⟨-, -, -, -, -, hlogs, -⟩ := BlockRecord.receiptInfo_eq_ok hri
  have hrp : receipt = r.receipts[k].2 := by
    simp [List.getElem?_eq_getElem hk] at hrec
    exact hrec.symm
  rw [hrp] at hlogs
  obtain ⟨l, hlmem, hll⟩ := List.mem_map.mp (hlogs ▸ hlp : log ∈ is[k].logs.map (·.log))
  refine ⟨l, getLogs_complete h hb hr hris (List.getElem_mem hk') hlmem
    (by rw [hll]; exact hs), hll, receiptInfo_blockHash hri l hlmem⟩

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
    (hex : (∃ addresses, f.address = some addresses ∧ addresses ≠ [] ∧
        ∀ a : Address, a ∈ addresses → Bloom.mayContain bloom ⟨a.toArray⟩ = false) ∨
      ∃ (k : Nat) (ts : List Hash32), f.topics[k]? = some (some ts) ∧ ts ≠ [] ∧
        ∀ t : Hash32, t ∈ ts → Bloom.mayContain bloom ⟨t.toArray⟩ = false) :
    ∀ log ∈ v.canonical[i + 1].logs, f.selects log = false := by
  intro log hlog
  have hbloom : bloom = Bloom.ofLogs v.canonical[i + 1].logs :=
    Bloom.toBytes_injective (hb.trans (hv.logsBloom_eq hi).symm)
  subst hbloom
  rcases hex with ⟨addresses, hf, hne, hno⟩ | ⟨k, ts, hk, hne, hno⟩
  · have hnot : log.address ∉ addresses := fun hmem => by
      have := hno _ hmem
      rw [Bloom.mayContain_address hlog] at this
      exact absurd this (by simp)
    have hemp : addresses.isEmpty = false := by simpa using hne
    simp [Filter.selects, hf, hnot, hemp]
  · rcases Nat.lt_or_ge log.topics.length f.topics.length with hlen | hlen
    · exact Filter.selects_eq_false_of_length_lt hlen
    obtain ⟨hk1, hget⟩ := List.getElem?_eq_some_iff.mp hk
    have hk2 : k < log.topics.length := by omega
    have hk' : (some ts, log.topics[k]) ∈ f.topics.zip log.topics := by
      rw [List.mem_iff_getElem]
      exact ⟨k, by simp; omega, by simp [hget]⟩
    have hnot : log.topics[k] ∉ ts := fun hmem => by
      have := hno _ hmem
      rw [Bloom.mayContain_topic hlog (List.getElem_mem hk2)] at this
      exact absurd this (by simp)
    have hfalse : Filter.takesTopic (some ts) log.topics[k] = false := by
      cases ts with
      | nil => exact absurd rfl hne
      | cons _ _ => simpa [Filter.takesTopic] using hnot
    have hall : (f.topics.zip log.topics).all (fun (taken, t) => Filter.takesTopic taken t)
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
