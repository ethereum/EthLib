module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Blocks.Transition
public import EthLib.Execution.Proofs.Blocks.AccessListBuilder
public import EthLib.Execution.Proofs.Blocks.Validate

/-!
# Proofs: the state transition of a block

A block that passes the transition commits to the state after it.

The state root of its header is the root of that state.

It also used the gas that its header states, and its Bloom filter is the filter of its logs.

Its fork is the active fork of its chain at its number and its time.

A transaction that cannot enter the block makes the block invalid, with its own error.

The DAO transfer runs only before Paris, at the block that the chain configuration names.

Before Glamsterdam a body gives no block access list.

From Glamsterdam, the list that a body builds is well formed and fits the gas limit.

A block that passes the checks then commits to that list by the hash in its header.

From Hegotá the transition fails as not yet specified.

When the hash of the last recent block succeeds, the recent blocks give hashes.

They are the parent hashes of the last 255 blocks, then the hash of the last block.

So there are at most 256 of them.

Take at least 256 recent blocks, each the parent of the next.

Then the hashes are those of the last 256 blocks.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState State stateRoot)
open EthLib.Execution.Transactions
open EthLib.Cryptography.Hash.Keccak (keccak256)

variable {fork : Fork}

/-! ## The hashes of the recent blocks -/

/-- The hashes of the recent blocks of a chain, and when they exist.

With no recent block there is no hash.

Otherwise the hash of the header of the last block must succeed.

The hashes are then the parent hashes of the last 255 blocks, or of all of them if there are fewer.

The hash of the last block comes after them. -/
theorem recentHashes_eq_ok_iff {recent : List RecentBlock} {hashes : List Hash32} :
    recentHashes recent = .ok hashes ↔ (recent = [] ∧ hashes = []) ∨
      ∃ last hash, recent.getLast? = some last ∧ last.header.hash = .ok hash ∧
        hashes = (recent.drop (recent.length - 255)).map (·.header.parentHash) ++ [hash] := by
  unfold recentHashes
  cases hr : recent.getLast? with
  | none =>
    obtain rfl := List.getLast?_eq_none_iff.mp hr
    simp [pure, Except.pure, eq_comm]
  | some last =>
    have hne : recent ≠ [] := by rintro rfl; simp at hr
    have hpos : 0 < recent.length := List.length_pos_iff.mpr hne
    -- The last 255 blocks end with the last block.
    have hd : (recent.drop (recent.length - 255)).getLast? = some last := by
      rw [List.getLast?_drop, hr]
      split
      · omega
      · rfl
    simp only [hd, Except.mapError]
    cases hHash : last.header.hash with
    | error e => simp [hne, hHash, bind, Except.bind]
    | ok hash => simp [hne, hHash, bind, Except.bind, pure, Except.pure, eq_comm]

/-- The recent blocks of a chain give at most 256 hashes. -/
theorem length_of_recentHashes {recent : List RecentBlock} {hashes : List Hash32}
    (h : recentHashes recent = .ok hashes) : hashes.length ≤ 256 := by
  rcases recentHashes_eq_ok_iff.mp h with ⟨_, hh⟩ | ⟨_, _, _, _, hh⟩
  · simp [hh]
  · have := (recent.drop (recent.length - 255)).length_map (f := (·.header.parentHash))
    rw [hh, List.length_append, this, List.length_drop, List.length_singleton]
    omega

/-- The hashes of at least 256 linked recent blocks are the hashes of the last 256 of them.

Linked means that the hash of each recent block is the parent hash of the next one.

The statement assumes that the transition computes the hashes. -/
theorem recentHashes_eq_mapM_hash {recent : List RecentBlock} {hashes : List Hash32}
    (h : recentHashes recent = .ok hashes)
    (hlink : ∀ (i : Nat) (hi : i + 1 < recent.length),
      recent[i].header.hash = .ok recent[i + 1].header.parentHash)
    (hlen : 256 ≤ recent.length) :
    (recent.drop (recent.length - 256)).mapM (·.header.hash) = .ok hashes := by
  rcases recentHashes_eq_ok_iff.mp h with ⟨hnil, -⟩ | ⟨last, hash, hr, hh, hhs⟩
  · simp [hnil] at hlen
  have h255 : 255 ≤ recent.length := by omega
  rw [hhs, mapM_eq_ok_iff]
  refine ⟨by simp [Nat.sub_sub_self hlen, Nat.sub_sub_self h255], fun i hi => ?_⟩
  -- The kept blocks are the last 256, and their parent hashes skip the first of them.
  simp only [List.length_drop, Nat.sub_sub_self hlen] at hi
  rw [List.getElem_drop]
  by_cases hi' : i < 255
  · -- A kept block hashes to the parent hash of the block after it.
    have hk : i < ((recent.drop (recent.length - 255)).map (·.header.parentHash)).length := by
      simp only [List.length_map, List.length_drop, Nat.sub_sub_self h255]
      omega
    rw [List.getElem_append_left hk, List.getElem_map, List.getElem_drop]
    have := hlink (recent.length - 256 + i) (by omega)
    rwa [getElem_congr_idx (show recent.length - 256 + i + 1 = recent.length - 255 + i by omega)]
      at this
  · -- The last kept block is the last block, whose hash comes last.
    have hk : ((recent.drop (recent.length - 255)).map (·.header.parentHash)).length ≤ i := by
      simp only [List.length_map, List.length_drop, Nat.sub_sub_self h255]
      omega
    rw [List.getElem_append_right hk]
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega), Option.some.injEq] at hr
    rw [getElem_congr_idx (show recent.length - 256 + i = recent.length - 1 by omega), hr, hh]
    simp only [List.length_map, List.length_drop, Nat.sub_sub_self h255, List.getElem_singleton]

/-! ## The checks of the block -/

/-- Before Paris, a block that passes its checks has ommers that pass theirs. -/
theorem checkBlock_validateOmmers {config : ChainConfig} {checkSeal : Bool}
    {recent : List RecentBlock} {block : Block fork Transaction} (hParis : fork < .paris)
    (h : checkBlock config checkSeal recent block = .ok ()) :
    validateOmmers config checkSeal recent block.header block.ommers = .ok () := by
  cases hv : validateOmmers config checkSeal recent block.header block.ommers with
  | ok u => rfl
  | error e =>
    exfalso
    unfold checkBlock at h
    simp only [hParis, ↓reduceIte, hv, Except.mapError, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw] at h
    repeat' (first | contradiction | (split at h))

/-! ## The checks against the output -/

/-- The roots that the output gives hold the state root of the state after the block. -/
theorem outputRoots_state {transactions : List Transaction}
    {withdrawals : Since .shapella fork (List Withdrawal)} {output : BlockOutput fork}
    {post : State} {roots : OutputRoots}
    (h : outputRoots transactions withdrawals output post = .ok roots) :
    stateRoot keccak256 post = .ok roots.state := by
  unfold outputRoots at h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  obtain ⟨postRoot, hPost, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  cases h
  exact mapError_ok_iff.mp hPost

/-- A block that passes the checks against its output used the gas that its header states.

Its state root and its Bloom filter are also those that its body gave. -/
theorem of_outputChecks {header : Header fork} {output : BlockOutput fork} {roots : OutputRoots}
    (h : firstFailure (outputChecks header output roots) = .ok ()) :
    output.gas.gasUsed = header.gasUsed ∧ roots.state = header.stateRoot ∧
      logsBloom output.logs = header.bloom := by
  have all := (firstFailure_eq_ok_iff _).mp h
  have get : ∀ c ∈ outputChecks header output roots, c.1 = true := all
  -- The first five checks come first in the list, before the checks of later forks.
  have first : ∀ c ∈ [(decide (output.gas.gasUsed = header.gasUsed),
      BlockError.wrongGasUsed header.gasUsed output.gas.gasUsed),
      (decide (roots.transactions = header.transactionsRoot), .wrongTransactionsRoot),
      (decide (roots.state = header.stateRoot), .wrongStateRoot),
      (decide (roots.receipts = header.receiptRoot), .wrongReceiptRoot),
      (decide (logsBloom output.logs = header.bloom), .wrongBloom)], c.1 = true :=
    fun c hc => get c (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ hc))))
  refine ⟨?_, ?_, ?_⟩
  · exact of_decide_eq_true (first _ (.head _))
  · exact of_decide_eq_true (first _ (.tail _ (.tail _ (.head _))))
  · have := first _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
    simpa using this

/-- From Glamsterdam, a block that passes the checks commits to the list of its body.

The hash of its header is the hash of the block access list that the body built. -/
theorem accessListHash_of_outputChecks {header : Header fork} {output : BlockOutput fork}
    {roots : OutputRoots} (hFork : .glamsterdam ≤ fork)
    (h : firstFailure (outputChecks header output roots) = .ok ()) :
    output.accessListHash = some (header.blockAccessListHash hFork) := by
  have all := (firstFailure_eq_ok_iff _).mp h
  have last : (decide (output.accessListHash = some (header.blockAccessListHash hFork)),
      BlockError.wrongBlockAccessListHash) ∈ outputChecks header output roots := by
    unfold outputChecks
    simp only [hFork, ↓reduceDIte]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  exact of_decide_eq_true (all _ last)

/-- From Dencun, a block that passes the checks used the blob gas that its header states. -/
theorem blobGasUsed_of_outputChecks {header : Header fork} {output : BlockOutput fork}
    {roots : OutputRoots} (hFork : .dencun ≤ fork)
    (h : firstFailure (outputChecks header output roots) = .ok ()) :
    output.gas.blob = (header.blobGasUsed hFork).toNat := by
  have all := (firstFailure_eq_ok_iff _).mp h
  have blob : (decide (output.gas.blob = (header.blobGasUsed hFork).toNat),
      BlockError.wrongBlobGasUsed (header.blobGasUsed hFork).toNat output.gas.blob) ∈
        outputChecks header output roots := by
    unfold outputChecks
    simp only [hFork, ↓reduceDIte]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_singleton_self _)))
  exact of_decide_eq_true (all _ blob)

/-! ## The block access list -/

/-- Before Glamsterdam, a body gives no block access list. -/
theorem accessListHashOf_of_lt_glamsterdam {body : BodyState} {gasLimit : Nat}
    (h : fork < .glamsterdam) : accessListHashOf fork body gasLimit = .ok none := by
  have hpre : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt h
  simp [accessListHashOf, hpre, pure, Except.pure]

/-- From Glamsterdam, the hash that a body gives is the hash of the list it built.

That list passes every check of a list alone: its order, its uniqueness and its size. -/
theorem accessListHashOf_eq_ok {body : BodyState} {gasLimit : Nat} {hash : Option Hash32}
    (h : accessListHashOf fork body gasLimit = .ok hash) (hFork : .glamsterdam ≤ fork) :
    BlockAccessList.check body.builder.build gasLimit = .ok () ∧
      ∃ value, hash = some value ∧ BlockAccessList.hash body.builder.build = .ok value := by
  unfold accessListHashOf at h
  simp only [hFork, ↓reduceIte] at h
  obtain ⟨_, hCheck, h⟩ := bind_ok_iff.mp h
  obtain ⟨value, hHash, h⟩ := bind_ok_iff.mp (show _ >>= _ = _ from h)
  refine ⟨mapError_ok_iff.mp hCheck, value, ?_, mapError_ok_iff.mp hHash⟩
  cases h
  rfl

/-! ## The DAO transfer -/

/-- From Paris the DAO transfer leaves the block state as it was, whatever the configuration. -/
theorem daoTransfer_of_paris_le {config : ChainConfig} {number : Nat} {start : BlockState}
    (h : .paris ≤ fork) : daoTransfer config fork number start = .ok start := by
  have hNot : ¬fork < .paris := Nat.not_lt.mpr h
  simp only [daoTransfer, hNot, false_and, ↓reduceIte]
  rfl

/-- At a block that the configuration does not name for the DAO Fork, the state stays. -/
theorem daoTransfer_of_daoForkBlock_ne {config : ChainConfig} {number : Nat} {start : BlockState}
    (h : daoForkBlock config ≠ some number) :
    daoTransfer config fork number start = .ok start := by
  simp only [daoTransfer, h, and_false, ↓reduceIte]
  rfl

/-- Before Paris, at the DAO Fork block of the configuration, the DAO ether moves. -/
theorem daoTransfer_of_lt_paris {config : ChainConfig} {number : Nat} {start : BlockState}
    (h : fork < .paris) (hBlock : daoForkBlock config = some number) :
    daoTransfer config fork number start = onBlock start (applyDaoFork fork) := by
  simp only [daoTransfer, h, hBlock, and_self, ↓reduceIte]

/-! ## The transactions -/

/-- A transaction that enters the body passes the inclusion check, and its run succeeds.

The gas counts of the block then grow by those of that run.

The gas used that the receipts add up grows by the gas used of the run.

The body before it begins position `index + 1`, and the run then joins it. -/
theorem applyTransaction_eq_ok {env : BlockEnvironment fork} {index : Nat}
    {before after : BodyOutput fork} {tx : Transaction}
    (h : applyTransaction env index before tx = .ok after) :
    ∃ included out,
      checkInclusion env.chainId env before.gas (.ofBlock before.block) tx = .ok included ∧
      processTransaction env before.block included tx = .ok out ∧
      after.gas = before.gas.add out.blockGas ∧
      after.cumulativeGasUsed = before.cumulativeGasUsed + out.gasUsed ∧
      (before.body.beginIndex (index + 1)).join out.state = .ok after.body := by
  unfold applyTransaction at h
  obtain ⟨included, hIncluded, h⟩ := bind_ok_iff.mp h
  obtain ⟨out, hOut, h⟩ := bind_ok_iff.mp h
  obtain ⟨body, hBody, h⟩ := bind_ok_iff.mp h
  refine ⟨included, out, mapError_ok_iff.mp hIncluded, mapError_ok_iff.mp hOut, ?_⟩
  dsimp only at h
  split at h <;>
    (obtain ⟨_, -, h⟩ := bind_ok_iff.mp h; cases h; exact ⟨rfl, rfl, mapError_ok_iff.mp hBody⟩)

/-- A transaction that cannot enter its block makes the block invalid, with its error. -/
theorem applyTransaction_of_checkInclusion {env : BlockEnvironment fork} {index : Nat}
    {before : BodyOutput fork} {tx : Transaction} {e : InclusionError}
    (h : checkInclusion env.chainId env before.gas (.ofBlock before.block) tx =
      .error e) :
    applyTransaction env index before tx = .error (.invalidTransaction index e) := by
  simp [applyTransaction, h, Except.mapError, bind, Except.bind]

/-! ## The body -/

/-- A body that runs takes each step, in order, and gives the gas counts of its transactions.

The DAO transfer runs first, then the system calls that start the block, then the transactions.

From Shapella the withdrawals join the body after them, at the position after the transactions.

The requests then run, and the rewards last, which give the block state of the output.

The builder after the requests is the builder of the output, and gives its block access list hash.

The gas counts and the gas used that the receipts add up are those of the transactions. -/
theorem applyBody_eq_ok {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    (h : applyBody config env block start = .ok output) :
    ∃ state body txs withdrawn requested,
      daoTransfer config fork block.header.number start = .ok state ∧
      startSystemCalls env block.header.parentHash (.init state) = .ok body ∧
      applyTransactions env body block.transactions = .ok txs ∧
      (∀ hShapella : .shapella ≤ fork, ∃ tx,
        withdrawalState fork txs.body.block (block.withdrawals hShapella) = .ok tx ∧
        (txs.body.beginIndex (block.transactions.length + 1)).join tx = .ok withdrawn) ∧
      (¬.shapella ≤ fork → withdrawn = txs.body.beginIndex (block.transactions.length + 1)) ∧
      blockRequests config.depositContractAddress env withdrawn txs.logs =
        .ok (requested, output.requests) ∧
      onBlock requested.block (fun tx => payRewards fork tx block.header.coinbase
        block.header.number (block.ommers.map fun ommer => (ommer.2.coinbase, ommer.2.number))) =
        .ok output.block ∧
      output.body.builder = requested.builder ∧
      accessListHashOf fork requested block.header.gasLimit = .ok output.accessListHash ∧
      output.gas = txs.gas ∧ output.cumulativeGasUsed = txs.cumulativeGasUsed := by
  unfold applyBody at h
  dsimp only at h
  obtain ⟨state, hState, h⟩ := bind_ok_iff.mp h
  obtain ⟨body, hBody, h⟩ := bind_ok_iff.mp h
  obtain ⟨txs, hTxs, h⟩ := bind_ok_iff.mp h
  split at h
  · rename_i hShapella
    obtain ⟨tx, hTx, h⟩ := bind_ok_iff.mp h
    obtain ⟨withdrawn, hJoin, h⟩ := bind_ok_iff.mp h
    obtain ⟨⟨requested, requests⟩, hRequests, h⟩ := bind_ok_iff.mp h
    dsimp only at h
    obtain ⟨rewarded, hRewarded, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, hHash, h⟩ := bind_ok_iff.mp h
    cases h
    exact ⟨state, body, txs, withdrawn, requested, hState, mapError_ok_iff.mp hBody, hTxs,
      fun _ => ⟨tx, mapError_ok_iff.mp hTx, mapError_ok_iff.mp hJoin⟩,
      fun hNot => absurd hShapella hNot, hRequests, hRewarded, rfl, hHash, rfl, rfl⟩
  · rename_i hShapella
    obtain ⟨withdrawn, hWithdrawn, h⟩ := bind_ok_iff.mp h
    cases hWithdrawn
    obtain ⟨⟨requested, requests⟩, hRequests, h⟩ := bind_ok_iff.mp h
    dsimp only at h
    obtain ⟨rewarded, hRewarded, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, hHash, h⟩ := bind_ok_iff.mp h
    cases h
    exact ⟨state, body, txs, _, requested, hState, mapError_ok_iff.mp hBody, hTxs,
      fun hYes => absurd hYes hShapella, fun _ => rfl, hRequests, hRewarded, rfl, hHash, rfl,
      rfl⟩

/-! ## The transition -/

/-- From Hegotá, the transition fails, since the rules of that fork are not here yet. -/
theorem stateTransition_of_hegota_le {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} (h : .hegota ≤ fork) :
    stateTransition chain block checkSeal = .error (.aborted (.forkNotYetSpecified fork)) := by
  simp only [stateTransition, h, ↓reduceIte]
  rfl

/-- A block that passes the transition takes each step of it, in order.

Its fork is before Hegotá and is the active fork of its chain, and it passes its own checks.

Its body runs on the state after its parent, in the environment of the recent hashes.

The roots of the output pass the checks against the header.

The state after the block is the state that the body gives. -/
theorem stateTransition_eq_ok {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State} (h : stateTransition chain block checkSeal = .ok post) :
    ¬.hegota ≤ fork ∧
      chain.config.activeFork block.header.number block.header.timestamp.toNat = some fork ∧
      checkBlock chain.config checkSeal chain.recent block = .ok () ∧
      ∃ hashes output roots,
        recentHashes chain.recent = .ok hashes ∧
        applyBody chain.config (blockEnvironment chain.config hashes block.header) block
          ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output ∧
        outputRoots block.transactions block.withdrawals output output.block.applyChanges =
          .ok roots ∧
        firstFailure (outputChecks block.header output roots) = .ok () ∧
        post = output.block.applyChanges := by
  unfold stateTransition at h
  have hNotHegota : ¬.hegota ≤ fork := fun hH => by
    simp [hH, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  simp only [hNotHegota, ↓reduceIte] at h
  split at h
  · rename_i hActive
    obtain ⟨_, hCheck, h⟩ := bind_ok_iff.mp h
    obtain ⟨hashes, hHashes, h⟩ := bind_ok_iff.mp h
    obtain ⟨output, hOutput, h⟩ := bind_ok_iff.mp h
    obtain ⟨roots, hRoots, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, hChecks, h⟩ := bind_ok_iff.mp h
    cases h
    exact ⟨hNotHegota, hActive, hCheck, hashes, output, roots, hHashes, hOutput, hRoots, hChecks,
      rfl⟩
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

/-- A block that passes the transition is at the active fork of its chain.

Its header commits to the state after it. -/
theorem of_stateTransition {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State} (h : stateTransition chain block checkSeal = .ok post) :
    chain.config.activeFork block.header.number block.header.timestamp.toNat = some fork ∧
      stateRoot keccak256 post = .ok block.header.stateRoot := by
  obtain ⟨-, hActive, -, _, output, roots, -, -, hRoots, hChecks, rfl⟩ := stateTransition_eq_ok h
  refine ⟨hActive, ?_⟩
  rw [← (of_outputChecks hChecks).2.1]
  exact outputRoots_state hRoots

end EthLib.Execution.Blocks
