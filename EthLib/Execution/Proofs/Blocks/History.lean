module

public import EthLib.Execution.Proofs.Blocks.Replay

/-!
# Proofs: the history behind BLOCKHASH

The hashes that BLOCKHASH reads come from the recent blocks of the chain.

They are right only when the recent blocks form a chain.

Each one is numbered one above the one before, and names the hash of that one as its parent hash.

A chain with enough recent blocks keeps this property through each block that passes its transition.

On such a chain, BLOCKHASH finds the hash of each of the 256 blocks before the current one.

It never falls back to 0 inside that window.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Transactions
open EthLib.Execution.State (State)
open EthLib.Execution.Evm (blockHash)

/-- Two recent blocks are linked when the second is numbered one above the first.

It also names the hash of the first as its parent hash. -/
def Linked (a b : RecentBlock) : Prop :=
  b.header.number = a.header.number + 1 ∧ ∃ h, a.header.hash = .ok h ∧ b.header.parentHash = h

/-- A list of recent blocks is linked when each block is linked to the next one. -/
def LinkedList : List RecentBlock → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => Linked a b ∧ LinkedList (b :: rest)

/-- A chain has its history in order when its recent blocks are linked.

Its last block is numbered at least as high as it has recent blocks, up to 255. -/
def HistoryOK (chain : BlockChain) : Prop :=
  LinkedList chain.recent ∧ ∃ last, chain.recent.getLast? = some last ∧
    min last.header.number 255 ≤ chain.recent.length

/-! ## Linked lists -/

/-- A block linked to the last block of a linked list extends the list. -/
theorem LinkedList.append_singleton {l : List RecentBlock} {x : RecentBlock}
    (hl : LinkedList l) (hx : ∀ y, l.getLast? = some y → Linked y x) :
    LinkedList (l ++ [x]) := by
  induction l with
  | nil => trivial
  | cons a t ih =>
    cases t with
    | nil => exact ⟨hx a rfl, trivial⟩
    | cons b rest =>
      refine ⟨hl.1, ?_⟩
      exact ih hl.2 fun y hy => hx y (by simpa using hy)

/-- The end of a linked list is linked. -/
theorem LinkedList.drop {l : List RecentBlock} (hl : LinkedList l) (k : Nat) :
    LinkedList (l.drop k) := by
  induction k generalizing l with
  | zero => exact hl
  | succ k ih =>
    cases l with
    | nil => trivial
    | cons a t =>
      cases t with
      | nil => simp [LinkedList]
      | cons b rest => exact ih hl.2

/-- Two blocks next to each other in a linked list are linked. -/
theorem LinkedList.linked_getElem {l : List RecentBlock} (hl : LinkedList l) {i : Nat}
    (hi : i + 1 < l.length) : Linked l[i] l[i + 1] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    cases t with
    | nil => simp at hi
    | cons b rest =>
      cases i with
      | zero => exact hl.1
      | succ i => exact ih hl.2 (by simpa using hi)

/-- The number of each block of a linked list is its distance from the end below the last number. -/
theorem LinkedList.number_getElem {l : List RecentBlock} (hl : LinkedList l) {i : Nat}
    (hi : i < l.length) (hne : l ≠ []) :
    l[i].header.number + (l.length - 1 - i) = (l.getLast hne).header.number := by
  induction l generalizing i with
  | nil => exact absurd rfl hne
  | cons a t ih =>
    cases t with
    | nil =>
      have : i = 0 := by simpa using hi
      subst this
      simp
    | cons b rest =>
      cases i with
      | zero =>
        have h1 := ih hl.2 (i := 0) (by simp) (by simp)
        have h2 := hl.1.1
        have hlast : (a :: b :: rest).getLast hne = (b :: rest).getLast (by simp) :=
          List.getLast_cons_cons ..
        rw [hlast]
        simp only [List.getElem_cons_zero, List.length_cons] at h1 h2 ⊢
        omega
      | succ i =>
        have h1 := ih hl.2 (i := i) (by simpa using hi) (by simp)
        simpa [List.getLast_cons] using h1

/-! ## The history of a chain -/

variable {fork : Fork}

/-- A block that passes its transition keeps the history of its chain in order. -/
theorem stateTransition_historyOK {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State} (hok : HistoryOK chain)
    (h : stateTransition chain block checkSeal = .ok post) :
    HistoryOK (chain.addBlock block post) := by
  obtain ⟨hlinked, last, hlast, hlen⟩ := hok
  obtain ⟨-, -, hcheck, -⟩ := stateTransition_eq_ok h
  obtain ⟨parent, hparent, hnumber, hhash⟩ := checkBlock_link hcheck
  obtain rfl : parent = last := Option.some.inj (hparent.symm.trans hlast)
  have hnew : Linked parent ⟨fork, block.header, block.ommers⟩ :=
    ⟨hnumber, block.header.parentHash, hhash, rfl⟩
  refine ⟨?_, ⟨fork, block.header, block.ommers⟩, BlockChain.addBlock_getLast?, ?_⟩
  · have hextend :
        LinkedList (chain.recent ++ [(⟨fork, block.header, block.ommers⟩ : RecentBlock)]) := by
      refine hlinked.append_singleton fun y hy => ?_
      have hyl : y = parent := Option.some.inj (hy.symm.trans hlast)
      rw [hyl]
      exact hnew
    rw [BlockChain.addBlock_recent]
    exact hextend.drop _
  · simp only [BlockChain.addBlock, List.length_drop, List.length_append, List.length_singleton,
      hnumber]
    omega

/-- A chain whose only recent block is a genesis block has its history in order. -/
theorem genesis_historyOK {chain : BlockChain} {genesis : RecentBlock}
    (hrecent : chain.recent = [genesis]) (hnumber : genesis.header.number = 0) :
    HistoryOK chain := by
  refine ⟨by simp [hrecent, LinkedList], genesis, by simp [hrecent], ?_⟩
  simp [hrecent, hnumber]

/-- On a chain with its history in order, the hashes of a block are as many as the window asks.

They are the hashes of the 256 blocks before it, or of all of them when it has fewer. -/
theorem recentHashes_length {chain : BlockChain} {hashes : List Hash32} {last : RecentBlock}
    (hok : HistoryOK chain) (hlast : chain.recent.getLast? = some last)
    (h : recentHashes chain.recent = .ok hashes) :
    min (last.header.number + 1) 256 ≤ hashes.length := by
  obtain ⟨-, last', hlast', hlen⟩ := hok
  obtain rfl : last = last' := (Option.some.inj (hlast'.symm.trans hlast)).symm
  rcases recentHashes_eq_ok_iff.mp h with ⟨hnil, -⟩ | ⟨l, hash, hl, -, hh⟩
  · simp [hnil] at hlast
  · rw [hh, List.length_append, List.length_map, List.length_drop, List.length_singleton]
    omega

/-! ## The window of BLOCKHASH -/

/-- The number of a recent block of a chain with its history in order is set by its position. -/
theorem HistoryOK.number_getElem {chain : BlockChain} {last : RecentBlock}
    (hok : HistoryOK chain) (hlast : chain.recent.getLast? = some last) {i : Nat}
    (hi : i < chain.recent.length) :
    chain.recent[i].header.number + (chain.recent.length - 1 - i) = last.header.number := by
  have hne : chain.recent ≠ [] := by rintro h; simp [h] at hlast
  have := hok.1.number_getElem hi hne
  rw [this]
  have hl : chain.recent.getLast hne = last :=
    Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans hlast)
  rw [hl]

/-- Two recent blocks with one number are one block, on a chain with its history in order. -/
theorem HistoryOK.eq_of_number {chain : BlockChain} {last : RecentBlock}
    (hok : HistoryOK chain) (hlast : chain.recent.getLast? = some last) {a b : RecentBlock}
    (ha : a ∈ chain.recent) (hb : b ∈ chain.recent) (h : a.header.number = b.header.number) :
    a = b := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  have h1 := hok.number_getElem hlast hi
  have h2 := hok.number_getElem hlast hj
  have : i = j := by omega
  subst this
  rfl

/-- BLOCKHASH reads the hash of each of the last 256 blocks before the current one.

On a chain with its history in order, the current block is numbered one above the last recent block.

The hash of the block numbered `n` is the hash of the last block when `n` is its number.

Otherwise it is the parent hash of the recent block numbered `n + 1`.

When a recent block is numbered `n`, the hash is its hash.

The list of hashes is long enough, so the fallback to 0 for a short list is not used. -/
theorem blockHash_ancestor {chain : BlockChain} {hashes : List Hash32} {last : RecentBlock}
    (hok : HistoryOK chain) (hlast : chain.recent.getLast? = some last)
    (hhashes : recentHashes chain.recent = .ok hashes) {n : Nat}
    (hlt : n < last.header.number + 1) (hwin : last.header.number + 1 ≤ n + 256) :
    ∃ h, hashes.reverse[last.header.number + 1 - n - 1]? = some h ∧
      blockHash hashes (last.header.number + 1) n = U256.fromBeBytes h ∧
      ((n = last.header.number ∧ last.header.hash = .ok h) ∨
        ∃ b ∈ chain.recent, b.header.number = n + 1 ∧ b.header.parentHash = h) ∧
      ∀ b ∈ chain.recent, b.header.number = n → b.header.hash = .ok h := by
  obtain ⟨last', hlast', hlen⟩ := hok.2
  obtain rfl : last = last' := (Option.some.inj (hlast'.symm.trans hlast)).symm
  rcases recentHashes_eq_ok_iff.mp hhashes with ⟨hnil, -⟩ | ⟨l, hash, hl, hhash, hhs⟩
  · simp [hnil] at hlast
  obtain rfl : last = l := (Option.some.inj (hl.symm.trans hlast)).symm
  -- The kept blocks are the last 255 recent ones.
  have hKlen : (chain.recent.drop (chain.recent.length - 255)).length =
      min chain.recent.length 255 := by
    simp only [List.length_drop]
    omega
  -- The hashes, newest first, start with the hash of the last block.
  have hrev : hashes.reverse = hash ::
      ((chain.recent.drop (chain.recent.length - 255)).map (·.header.parentHash)).reverse := by
    rw [hhs]
    simp
  have hbh : blockHash hashes (last.header.number + 1) n =
      match hashes.reverse[last.header.number + 1 - n - 1]? with
      | some hash => U256.fromBeBytes hash
      | none => 0 := by
    have hc : n < last.header.number + 1 ∧ last.header.number + 1 ≤ n + 256 := ⟨hlt, hwin⟩
    simp only [blockHash, hc, and_self, ↓reduceIte]
    rfl
  by_cases hk : last.header.number = n
  · -- The block is the last one, whose hash comes first.
    have hzero : last.header.number + 1 - n - 1 = 0 := by omega
    have hget : hashes.reverse[last.header.number + 1 - n - 1]? = some hash := by
      rw [hzero, hrev]
      rfl
    refine ⟨hash, hget, by rw [hbh, hget], .inl ⟨hk.symm, hhash⟩, fun b hb hbn => ?_⟩
    have hmem : last ∈ chain.recent := List.mem_of_mem_getLast? (by simp [hlast])
    obtain rfl := hok.eq_of_number hlast hb hmem (by omega)
    exact hhash
  · -- The block is older than the last one: its hash is the parent hash of the block after it.
    obtain ⟨k, hk⟩ : ∃ k, last.header.number - n = k + 1 :=
      ⟨last.header.number - n - 1, by omega⟩
    have hkm : k + 1 ≤ (chain.recent.drop (chain.recent.length - 255)).length := by
      rw [hKlen]
      omega
    have hi : chain.recent.length - (k + 1) < chain.recent.length := by
      rw [hKlen] at hkm
      omega
    have hnum := hok.number_getElem hlast hi
    -- The block after it is numbered `n + 1`.
    have hnum' : chain.recent[chain.recent.length - (k + 1)].header.number = n + 1 := by omega
    have hidx : last.header.number + 1 - n - 1 = k + 1 := by omega
    have hpos : (chain.recent.drop (chain.recent.length - 255)).length - 1 - k +
        (chain.recent.length - 255) = chain.recent.length - (k + 1) := by
      rw [hKlen]
      omega
    have hget : hashes.reverse[last.header.number + 1 - n - 1]? =
        some chain.recent[chain.recent.length - (k + 1)].header.parentHash := by
      rw [hidx, hrev, List.getElem?_cons_succ, List.getElem?_reverse (by simp; omega),
        List.length_map, List.getElem?_map, List.getElem?_drop, Nat.add_comm, hpos,
        List.getElem?_eq_getElem hi]
      rfl
    refine ⟨_, hget, by rw [hbh, hget], .inr ⟨_, List.getElem_mem hi, hnum', rfl⟩,
      fun b hb hbn => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
    have hnj := hok.number_getElem hlast hj
    have hj1 : j + 1 < chain.recent.length := by omega
    obtain ⟨-, h', hh', hparent⟩ := hok.1.linked_getElem hj1
    have hsame : chain.recent[j + 1] = chain.recent[chain.recent.length - (k + 1)] := by
      simp only [show j + 1 = chain.recent.length - (k + 1) by omega]
    rw [hsame] at hparent
    rw [hparent]
    exact hh'

/-! ## Along a run of blocks -/

/-- A chain gives BLOCKHASH, in a block numbered `current`, the hash of each of the last 256 blocks.

For each such block number `n`, the list of hashes has an entry for it.

So the fallback to 0 is not used, and BLOCKHASH reads that entry. -/
def Window (chain : BlockChain) (current : Nat) : Prop :=
  ∀ hashes, recentHashes chain.recent = .ok hashes → ∀ n, n < current → current ≤ n + 256 →
    ∃ h, hashes.reverse[current - n - 1]? = some h ∧
      blockHash hashes current n = U256.fromBeBytes h

/-- A block that passes its transition on a chain with its history in order has its window. -/
theorem stateTransition_window {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State} (hok : HistoryOK chain)
    (h : stateTransition chain block checkSeal = .ok post) :
    Window chain block.header.number := by
  obtain ⟨-, -, hcheck, -⟩ := stateTransition_eq_ok h
  obtain ⟨parent, hparent, hnumber, -⟩ := checkBlock_link hcheck
  intro hashes hhashes n hlt hwin
  rw [hnumber] at hlt hwin ⊢
  obtain ⟨h, hget, hhash, -⟩ := blockHash_ancestor hok hparent hhashes hlt hwin
  exact ⟨h, hget, hhash⟩

/-- Every block of a run has its window, on the chain that it runs on.

The chain before the first block is `chain`.

The chain before each later block is the chain after the block before it. -/
def Windows : BlockChain → List ((fork : Fork) × Block fork Transaction) → Prop
  | _, [] => True
  | chain, ⟨_, block⟩ :: rest => ∃ checkSeal post,
      stateTransition chain block checkSeal = .ok post ∧ Window chain block.header.number ∧
        Windows (chain.addBlock block post) rest

/-- On a run of blocks from a chain with its history in order, every block has its window.

A run from a genesis block is such a run, by the theorem on genesis chains.

So BLOCKHASH finds the hash of each of the last 256 blocks, in every block of the run. -/
theorem ChainRun.windows {chain : BlockChain}
    {blocks : List ((fork : Fork) × Block fork Transaction)} (run : ChainRun chain blocks)
    (hok : HistoryOK chain) : Windows chain blocks := by
  induction run with
  | nil => trivial
  | cons checkSeal transition hnext tail ih =>
    subst hnext
    exact ⟨checkSeal, _, transition, stateTransition_window hok transition,
      ih (stateTransition_historyOK hok transition)⟩

end EthLib.Execution.Blocks
