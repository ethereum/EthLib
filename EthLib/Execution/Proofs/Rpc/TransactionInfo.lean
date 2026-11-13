module

public import EthLib.Execution.Rpc.TransactionInfo
public import EthLib.Execution.Proofs.Rpc.View
public import EthLib.Execution.Proofs.Transactions.Inclusion

/-!
# Proofs: the transactions that the chain view returns

A lookup by hash returns only a transaction of that hash, in a block that the node holds.

It reads a canonical block first, whenever one has a transaction of that hash.

It finds nothing only when no block of the node has a transaction of that hash.

A lookup by block and index returns the transaction at that index of the block that it names.

In a valid view, the run of each canonical block after the lowest checked each of its transactions.

The sender and the gas price of each are those of that inclusion check.
-/

public section

namespace EthLib.Execution.Rpc.ChainView

open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Transactions

/-- The object of a transaction of a block holds its context, its sender, its hash and its price. -/
theorem _root_.EthLib.Execution.Rpc.BlockRecord.transactionInfo_eq_ok {r : BlockRecord}
    {index : Nat} {tx : Transaction}
    {info : TransactionInfo} :
    r.transactionInfo index tx = .ok info ↔ ∃ sender hash, recoverSender r.fork tx = .ok sender ∧
      transactionHash tx = .ok hash ∧
      info = { blockHash := r.hash, blockNumber := r.block.header.number
               blockTimestamp := r.block.header.timestamp.toNat, index, sender, hash
               gasPrice := effectiveGasPrice r.baseFee tx, tx } := by
  unfold BlockRecord.transactionInfo
  constructor
  · intro h
    obtain ⟨sender, hs, h⟩ := bind_ok_iff.mp h
    obtain ⟨hash, hh, h⟩ := bind_ok_iff.mp h
    cases h
    exact ⟨sender, hash, mapError_ok_iff.mp hs, mapError_ok_iff.mp hh, rfl⟩
  · rintro ⟨sender, hash, hs, hh, rfl⟩
    simp [bind, Except.bind, Base.mapError_ok_iff.mpr hs, Base.mapError_ok_iff.mpr hh, pure,
      Except.pure]

/-- A transaction has a hash that is `hash` exactly when its hash is `hash`. -/
private theorem hasHash_iff {hash : Hash32} {tx : Transaction} :
    hasHash hash tx = true ↔ transactionHash tx = .ok hash := by
  unfold hasHash
  rcases h : transactionHash tx with e | x <;> simp

/-- A transaction that a search of a block finds has its hash and sits at its index. -/
private theorem findTransaction_block_some {r : BlockRecord} {hash : Hash32} {tx : Transaction}
    {index : Nat} (h : r.findTransaction hash = some (tx, index)) :
    r.block.transactions[index]? = some tx ∧ transactionHash tx = .ok hash := by
  unfold BlockRecord.findTransaction at h
  exact ⟨List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some h),
    hasHash_iff.mp (by simpa using List.find?_some h)⟩

/-- A search of a block finds nothing exactly when no transaction of the block has the hash. -/
private theorem findTransaction_block_none {r : BlockRecord} {hash : Hash32} :
    r.findTransaction hash = none ↔
      ∀ tx ∈ r.block.transactions, transactionHash tx ≠ .ok hash := by
  unfold BlockRecord.findTransaction
  rw [List.find?_eq_none]
  constructor
  · intro h tx htx hh
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem htx
    exact h (r.block.transactions[i], i)
      (List.mem_zipIdx_iff_getElem?.mpr (by simp)) (by simpa using hasHash_iff.mpr hh)
  · rintro h ⟨tx, i⟩ hm hp
    have := List.mem_zipIdx_iff_getElem?.mp hm
    exact h tx (List.mem_of_getElem? this) (hasHash_iff.mp (by simpa using hp))

/-- A search of some blocks that finds a transaction names a block among them. -/
private theorem findSome_mem {l : List BlockRecord} {hash : Hash32} {r : BlockRecord}
    {tx : Transaction} {index : Nat}
    (h : l.findSome? (fun r => (r.findTransaction hash).map fun p => (r, p)) =
      some (r, tx, index)) :
    r ∈ l ∧ r.findTransaction hash = some (tx, index) := by
  obtain ⟨l₁, a, l₂, hl, hf, -⟩ := List.findSome?_eq_some_iff.mp h
  obtain ⟨p, hp, hq⟩ := Option.map_eq_some_iff.mp hf
  cases hq
  exact ⟨by simp [hl], hp⟩

/-- A search of the blocks of the node finds a transaction with that hash, at its index. -/
theorem findTransaction_some {v : ChainView} {hash : Hash32} {r : BlockRecord} {tx : Transaction}
    {index : Nat} (h : v.findTransaction hash = some (r, tx, index)) :
    r ∈ v.canonical ++ v.side ∧ r.block.transactions[index]? = some tx ∧
      transactionHash tx = .ok hash :=
  have ⟨hr, hf⟩ := findSome_mem h
  ⟨hr, findTransaction_block_some hf⟩

/-- A lookup by hash returns a transaction of that hash, at its index in a block of the node. -/
theorem transactionByHash_some {v : ChainView} {hash : Hash32} {info : TransactionInfo}
    (h : v.transactionByHash hash = .ok (some info)) :
    ∃ r ∈ v.canonical ++ v.side, r.block.transactions[info.index]? = some info.tx ∧
      r.transactionInfo info.index info.tx = .ok info ∧ transactionHash info.tx = .ok hash ∧
      info.hash = hash := by
  unfold transactionByHash at h
  rcases hf : v.findTransaction hash with _ | ⟨r, tx, index⟩
  · simp [hf] at h
  · simp only [hf] at h
    obtain ⟨hr, hrf⟩ := findSome_mem hf
    obtain ⟨hget, hhash⟩ := findTransaction_block_some hrf
    cases hi : r.transactionInfo index tx with
    | error e => simp [hi, Functor.map, Except.map] at h
    | ok info' =>
      simp only [hi] at h
      cases h
      obtain ⟨sender, hash', -, hh, rfl⟩ := BlockRecord.transactionInfo_eq_ok.mp hi
      exact ⟨r, hr, hget, hi, hhash, (Except.ok.inj (hh.symm.trans hhash))⟩

/-- A lookup by hash finds nothing only when no block of the node has a transaction of it. -/
theorem transactionByHash_none {v : ChainView} {hash : Hash32}
    (h : v.transactionByHash hash = .ok none) :
    ∀ r ∈ v.canonical ++ v.side, ∀ tx ∈ r.block.transactions, transactionHash tx ≠ .ok hash := by
  unfold transactionByHash at h
  cases hf : v.findTransaction hash with
  | some p =>
    simp only [hf] at h
    cases hi : p.1.transactionInfo p.2.2 p.2.1 <;> simp [hi, Functor.map, Except.map] at h
  | none =>
    intro r hr
    have := List.findSome?_eq_none_iff.mp hf r hr
    exact findTransaction_block_none.mp (by simpa using this)

/-- A lookup by hash reads a canonical block whenever one has a transaction of that hash. -/
theorem transactionByHash_canonical {v : ChainView} {hash : Hash32} {info : TransactionInfo}
    (h : v.transactionByHash hash = .ok (some info))
    (hc : ∃ r ∈ v.canonical, ∃ tx ∈ r.block.transactions, transactionHash tx = .ok hash) :
    ∃ r ∈ v.canonical, r.block.transactions[info.index]? = some info.tx ∧
      r.transactionInfo info.index info.tx = .ok info := by
  obtain ⟨r0, hr0, tx0, ht0, hh0⟩ := hc
  have hsome : (v.canonical.findSome?
      fun r => (r.findTransaction hash).map fun p => (r, p)) ≠ none := by
    intro hn
    have := List.findSome?_eq_none_iff.mp hn r0 hr0
    exact findTransaction_block_none.mp (by simpa using this) tx0 ht0 hh0
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hsome
  have hf : v.findTransaction hash = some q := by
    simp [ChainView.findTransaction, List.findSome?_append, hq]
  obtain ⟨r, tx, index⟩ := q
  obtain ⟨hr, hrf⟩ := findSome_mem hq
  obtain ⟨hget, -⟩ := findTransaction_block_some hrf
  unfold transactionByHash at h
  simp only [hf] at h
  cases hi : r.transactionInfo index tx with
  | error e => simp [hi, Functor.map, Except.map] at h
  | ok info' =>
    simp only [hi] at h
    cases h
    obtain ⟨sender, hash', -, hh, rfl⟩ := BlockRecord.transactionInfo_eq_ok.mp hi
    exact ⟨r, hr, hget, hi⟩

/-- A lookup by block and index returns the transaction at that index of the block it names. -/
theorem transactionByBlockAndIndex_some {v : ChainView} {p : BlockParam} {index : Nat}
    {info : TransactionInfo} (h : v.transactionByBlockAndIndex p index = .ok (some info)) :
    ∃ r, v.resolve p = .ok (some r) ∧ r.block.transactions[index]? = some info.tx ∧
      r.transactionInfo index info.tx = .ok info := by
  unfold transactionByBlockAndIndex at h
  rcases hr : v.resolve p with e | _ | r
  · simp [hr, bind, Except.bind] at h
  · simp [hr, bind, Except.bind, pure, Except.pure] at h
  · simp only [hr, bind, Except.bind] at h
    rcases ht : r.block.transactions[index]? with _ | tx
    · simp [ht, pure, Except.pure] at h
    · simp only [ht] at h
      cases hi : r.transactionInfo index tx with
      | error e => simp [hi, Functor.map, Except.map] at h
      | ok info' =>
        simp only [hi] at h
        cases h
        obtain ⟨sender, hash', -, -, rfl⟩ := BlockRecord.transactionInfo_eq_ok.mp hi
        exact ⟨r, rfl, ht, hi⟩

/-- A lookup by block and index finds nothing exactly when the block is unknown or too short. -/
theorem transactionByBlockAndIndex_none {v : ChainView} {p : BlockParam} {index : Nat} :
    v.transactionByBlockAndIndex p index = .ok none ↔ v.resolve p = .ok none ∨
      ∃ r, v.resolve p = .ok (some r) ∧ r.block.transactions.length ≤ index := by
  unfold transactionByBlockAndIndex
  rcases hr : v.resolve p with e | _ | r
  · simp [bind, Except.bind]
  · simp [bind, Except.bind, pure, Except.pure]
  · simp only [bind, Except.bind]
    rcases ht : r.block.transactions[index]? with _ | tx
    · simp at ht
      simp [ht, pure, Except.pure]
    · have : index < r.block.transactions.length := (List.getElem?_eq_some_iff.mp ht).1
      cases hi : r.transactionInfo index tx <;> simp [hi, Functor.map, Except.map] <;> omega

/-- In a valid view, the run of a canonical block after the lowest applied each transaction.

It ran on the state of the block before, and reached the transaction after those before it. -/
theorem Valid.applyTransaction_at {v : ChainView} {checkSeal : Bool}
    (hv : v.Valid checkSeal) {i : Nat} (hi : i + 1 < v.canonical.length) {index : Nat}
    {tx : Transaction} (htx : v.canonical[i + 1].block.transactions[index]? = some tx) :
    ∃ hashes state body, ∃ before next : BodyOutput v.canonical[i + 1].fork,
      recentHashes (v.chainAt i (by omega)).recent = .ok hashes ∧
      daoTransfer v.config v.canonical[i + 1].fork v.canonical[i + 1].block.header.number
        ⟨v.canonical[i].state, ∅, ∅, ∅, ∅⟩ = .ok state ∧
      startSystemCalls (blockEnvironment v.config hashes v.canonical[i + 1].block.header)
        v.canonical[i + 1].block.header.parentHash (.init state) = .ok body ∧
      applyTransactions (blockEnvironment v.config hashes v.canonical[i + 1].block.header) body
        (v.canonical[i + 1].block.transactions.take index) = .ok before ∧
      Blocks.applyTransaction (blockEnvironment v.config hashes v.canonical[i + 1].block.header)
        index before tx = .ok next := by
  obtain ⟨-, result, hrun, -⟩ := hv.follows i hi
  obtain ⟨hashes, hrec, happly, -⟩ := Blocks.runBody_eq_ok.mp hrun
  obtain ⟨state, body, txs, -, -, hdao, hstart, htxs, -⟩ := Blocks.applyBody_eq_ok happly
  have hlt : index < v.canonical[i + 1].block.transactions.length :=
    (List.getElem?_eq_some_iff.mp htx).1
  obtain ⟨-, hsteps⟩ := Blocks.applyTransactions_steps (fun _ _ => True) (fun _ => trivial)
    (fun _ _ => trivial) (fun _ => trivial) htxs
  obtain ⟨before, next, hbefore, hnext, -⟩ := hsteps index hlt
  have hget : v.canonical[i + 1].block.transactions[index] = tx :=
    Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans htx)
  rw [hget] at hnext
  exact ⟨hashes, state, body, before, next, hrec, hdao, hstart, hbefore, hnext⟩

/-- In a valid view, the run of a canonical block after the lowest checked each transaction.

It ran on the state of the block before, and reached the transaction after those before it.

Its inclusion check passed there, and gave the sender and the gas price of the transaction. -/
theorem Valid.transactionInfo_inclusion {v : ChainView} {checkSeal : Bool}
    (hv : v.Valid checkSeal) {i : Nat} (hi : i + 1 < v.canonical.length) {index : Nat}
    {tx : Transaction} {info : TransactionInfo}
    (htx : v.canonical[i + 1].block.transactions[index]? = some tx)
    (h : v.canonical[i + 1].transactionInfo index tx = .ok info) :
    ∃ hashes state body, ∃ before : BodyOutput v.canonical[i + 1].fork, ∃ inc,
      recentHashes (v.chainAt i (by omega)).recent = .ok hashes ∧
      daoTransfer v.config v.canonical[i + 1].fork v.canonical[i + 1].block.header.number
        ⟨v.canonical[i].state, ∅, ∅, ∅, ∅⟩ = .ok state ∧
      startSystemCalls (blockEnvironment v.config hashes v.canonical[i + 1].block.header)
        v.canonical[i + 1].block.header.parentHash (.init state) = .ok body ∧
      applyTransactions (blockEnvironment v.config hashes v.canonical[i + 1].block.header) body
        (v.canonical[i + 1].block.transactions.take index) = .ok before ∧
      checkInclusion v.config.chainId
        (blockEnvironment v.config hashes v.canonical[i + 1].block.header) before.gas
        (.ofBlock before.block) tx = .ok inc ∧
      info.sender = inc.sender ∧ info.gasPrice = inc.gasPrice := by
  obtain ⟨hashes, state, body, before, next, hrec, hdao, hstart, hbefore, hnext⟩ :=
    hv.applyTransaction_at hi htx
  obtain ⟨inc, -, hinc, -⟩ := Blocks.applyTransaction_eq_ok hnext
  obtain ⟨hsender, -, -, -, -, -, -, hprice, -⟩ := checkInclusion_ok hinc
  obtain ⟨sender, hash, hs, -, rfl⟩ := BlockRecord.transactionInfo_eq_ok.mp h
  refine ⟨hashes, state, body, before, inc, hrec, hdao, hstart, hbefore, hinc, ?_, ?_⟩
  · exact Except.ok.inj (hs.symm.trans hsender)
  · simp [hprice, baseFeeOf, BlockRecord.baseFee, blockEnvironment]

end EthLib.Execution.Rpc.ChainView
