module

public import EthLib.Execution.Proofs.Blocks.AccessListFollow
public import EthLib.Execution.Proofs.Blocks.Rewards
public import EthLib.Execution.Proofs.Blocks.SystemCall
public import EthLib.Execution.Proofs.Blocks.Transition

/-!
# Proofs: the writes of a block access list rebuild the state after the block

From Glamsterdam, a header commits to the block access list of its body.

For each account in the list, take its last change of balance, nonce and code.

For each key of its storage, take its last change of word.

Applied to the state before the block, these give the state after the block.

A field with no change in the list keeps its value from before the block.

So a client that holds a list with the hash in the header can apply it to the state before.

That needs no run of the transactions, as long as the hash has no known collision.

This holds when the calls of the body keep a property of block states that makes each one fit.

Source: [EIP-7928, Recording Semantics by Change Type][eip7928].

[eip7928]: https://eips.ethereum.org/EIPS/eip-7928#recording-semantics-by-change-type
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState EMPTY_ACCOUNT State TransactionState)
open EthLib.Execution.Transactions

variable {fork : Fork}

/-! ## One step of the body -/

/-- A call that the builder follows keeps the builder of a body following the block. -/
theorem BodyState.tracks_join {body body' : BodyState} {tx : TransactionState} {base : BlockState}
    (h : body.builder.Tracks base body.block) (hfollow : Followable body.block tx)
    (hjoin : body.join tx = .ok body') : body'.builder.Tracks base body'.block := by
  obtain ⟨builder, hrecord, rfl⟩ := BodyState.join_eq_ok hjoin
  exact h.recordTransaction hfollow hrecord

/-- A later position keeps the builder of a body following the block. -/
private theorem BodyState.tracks_beginIndex {body : BodyState} {base : BlockState}
    {index : Nat}
    (h : body.builder.Tracks base body.block) (hindex : body.builder.index < UInt32.ofNat index) :
    (body.beginIndex index).builder.Tracks base (body.beginIndex index).block :=
  h.beginIndex hindex

/-! ## The body and the block -/

/-- The calls of a body at `fork` keep a property `P` of block states, and the builder follows each.

Take a block state with `P`.

A system call on it is one that the builder follows, and the block state after it has `P`.

So is a transaction that enters the block, and so are the withdrawals.

These are assumptions on the calls, which this file does not prove. -/
structure KeepsFollowable (env : BlockEnvironment fork) (P : BlockState → Prop) : Prop where
  /-- Each system call. -/
  systemCall : ∀ block target data out, P block →
    systemCall env block target data = .ok out → Followable block out.state ∧ P out.block
  /-- Each transaction that enters the block. -/
  transaction : ∀ gas block tx included out, P block →
    checkInclusion env.chainId env gas (.ofBlock block) tx = .ok included →
    processTransaction env block included tx = .ok out →
    Followable block out.state ∧ P out.state.incorporateTxIntoBlock.parent
  /-- The withdrawals. -/
  withdrawals : ∀ block withdrawals tx, P block →
    withdrawalState fork block withdrawals = .ok tx →
    Followable block tx ∧ P tx.incorporateTxIntoBlock.parent

/-- A followed call that keeps the property joins the body and keeps it, at the same position. -/
private theorem BodyState.join_keeps {P : BlockState → Prop} {body body' : BodyState}
    {tx : TransactionState} {base : BlockState} (h : body.builder.Tracks base body.block)
    (hfollow : Followable body.block tx) (hP : P tx.incorporateTxIntoBlock.parent)
    (hjoin : body.join tx = .ok body') :
    P body'.block ∧ body'.builder.Tracks base body'.block ∧
      body'.builder.index = body.builder.index := by
  refine ⟨?_, BodyState.tracks_join h hfollow hjoin, ?_⟩ <;>
    obtain ⟨builder, hrecord, rfl⟩ := BodyState.join_eq_ok hjoin
  · exact hP
  · exact (AccessListBuilder.recordTransaction_index hrecord).1

/-- The system calls at the start keep the property and the builder, at the same position. -/
private theorem startSystemCalls_tracks {env : BlockEnvironment fork} {P : BlockState → Prop}
    {parentHash : Hash32} {body body' : BodyState} {base : BlockState}
    (hkeep : KeepsFollowable env P) (hP : P body.block) (h : body.builder.Tracks base body.block)
    (hcalls : startSystemCalls env parentHash body = .ok body') :
    P body'.block ∧ body'.builder.Tracks base body'.block ∧
      body'.builder.index = body.builder.index := by
  obtain ⟨mid, hFirst, hNoFirst, hSecond, hNoSecond⟩ := startSystemCalls_eq_ok hcalls
  have hmid : P mid.block ∧ mid.builder.Tracks base mid.block ∧
      mid.builder.index = body.builder.index := by
    by_cases hDencun : .dencun ≤ fork
    · obtain ⟨out, hOut, hJoin⟩ := hFirst hDencun
      obtain ⟨hfollow, hP'⟩ := hkeep.systemCall _ _ _ _ hP hOut
      exact BodyState.join_keeps h hfollow hP' hJoin
    · obtain rfl := hNoFirst hDencun
      exact ⟨hP, h, rfl⟩
  by_cases hPectra : .pectra ≤ fork
  · obtain ⟨out, hOut, hJoin⟩ := hSecond hPectra
    obtain ⟨hfollow, hP'⟩ := hkeep.systemCall _ _ _ _ hmid.1 hOut
    obtain ⟨h₁, h₂, h₃⟩ := BodyState.join_keeps hmid.2.1 hfollow hP' hJoin
    exact ⟨h₁, h₂, h₃.trans hmid.2.2⟩
  · rw [hNoSecond hPectra]
    exact hmid

/-- The transactions keep the property and the builder, whose position is at most the last one. -/
private theorem applyTransactions_tracks {env : BlockEnvironment fork} {P : BlockState → Prop}
    {base : BlockState} (hkeep : KeepsFollowable env P) :
    ∀ (l : List Transaction) (m : Nat) (before out : BodyOutput fork),
      P before.body.block → before.body.builder.Tracks base before.body.block →
      before.body.builder.index.toNat ≤ m → m + l.length < 2 ^ 32 →
      (l.zipIdx m).foldlM (fun before (tx, index) => applyTransaction env index before tx)
        before = .ok out →
      P out.body.block ∧ out.body.builder.Tracks base out.body.block ∧
        out.body.builder.index.toNat ≤ m + l.length
  | [], m, before, out, hP, h, hindex, _, hfold => by
    simp only [List.zipIdx_nil, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
    subst hfold
    exact ⟨hP, h, by simpa using hindex⟩
  | tx :: l, m, before, out, hP, h, hindex, hlength, hfold => by
    rw [List.zipIdx_cons, List.foldlM_cons, bind_ok_iff] at hfold
    obtain ⟨next, hnext, hrest⟩ := hfold
    obtain ⟨included, run, hIncluded, hRun, -, -, hJoin⟩ := applyTransaction_eq_ok hnext
    obtain ⟨hfollow, hP'⟩ := hkeep.transaction _ _ _ _ _ hP hIncluded hRun
    have hm : m + 1 < 2 ^ 32 := by simp only [List.length_cons] at hlength; omega
    have hlt : before.body.builder.index < UInt32.ofNat (m + 1) := by
      rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' hm]
      omega
    obtain ⟨h₁, h₂, h₃⟩ :=
      BodyState.join_keeps (BodyState.tracks_beginIndex h hlt) hfollow hP' hJoin
    have hnext : next.body.builder.index.toNat ≤ m + 1 := by
      rw [h₃]
      show (UInt32.ofNat (m + 1)).toNat ≤ m + 1
      rw [UInt32.toNat_ofNat_of_lt' hm]
      exact Nat.le_refl _
    have := applyTransactions_tracks hkeep l (m + 1) next out h₁ h₂ hnext
      (by simp only [List.length_cons] at hlength; omega) hrest
    simp only [List.length_cons]
    exact ⟨this.1, this.2.1, by omega⟩

/-- The calls to the request contracts keep the property and the builder. -/
private theorem readRequests_tracks {env : BlockEnvironment fork} {P : BlockState → Prop}
    {base : BlockState} {body body' : BodyState} {requests : List ByteArray}
    (hkeep : KeepsFollowable env P) (hP : P body.block) (h : body.builder.Tracks base body.block)
    (hread : readRequests env body = .ok (body', requests)) :
    P body'.block ∧ body'.builder.Tracks base body'.block := by
  by_cases hPectra : .pectra ≤ fork
  · rw [readRequests_of_pectra hPectra] at hread
    refine foldlM_ok_invariant
      (fun s : BodyState × List ByteArray => P s.1.block ∧ s.1.builder.Tracks base s.1.block)
      (fun s c s' hs hs' => ?_) ⟨hP, h⟩ hread
    obtain ⟨out, hOut, hJoin, -⟩ := readRequest_eq_ok hs'
    obtain ⟨hfollow, hP'⟩ := hkeep.systemCall _ _ _ _ hs.1 (checkedSystemCall_ok hOut).2.1
    obtain ⟨h₁, h₂, -⟩ := BodyState.join_keeps hs.2 hfollow hP' hJoin
    exact ⟨h₁, h₂⟩
  · rw [readRequests_of_lt_pectra (Nat.lt_of_not_le hPectra)] at hread
    cases hread
    exact ⟨hP, h⟩

/-- A block state reads each account and word as it did after a step that wrote nothing. -/
private theorem onBlock_pure {block block' : BlockState}
    (h : onBlock block (fun tx => .ok tx) = .ok block') :
    (∀ address, (TransactionState.ofBlock block').getAccount address =
      (TransactionState.ofBlock block).getAccount address) ∧
    ∀ address key, (TransactionState.ofBlock block').getStorage address key =
      (TransactionState.ofBlock block).getStorage address key := by
  obtain ⟨tx, htx, rfl⟩ := onBlock_eq_ok h
  cases htx
  exact ⟨State.TransactionState.getAccount_ofBlock_incorporateTxIntoBlock _,
    State.TransactionState.getStorage_incorporateTxIntoBlock _⟩

/-- From Dencun, the builder at the end of a body follows the block from its start.

Before Dencun, a SELFDESTRUCT can wipe storage that the list does not name.

So the property is not expected to hold there, and the theorem starts at Dencun.

The calls of the body keep a property of block states that the start has.

The block has fewer than 2^32 - 1 transactions, so each position fits in 32 bits. -/
theorem applyBody_tracks {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    {P : BlockState → Prop} (hDencun : .dencun ≤ fork) (hkeep : KeepsFollowable env P)
    (hstart : P start) (hlength : block.transactions.length < 2 ^ 32 - 1)
    (h : applyBody config env block start = .ok output) :
    output.body.builder.Tracks start output.block := by
  have hParis : Fork.paris ≤ fork := Nat.le_trans (by decide) hDencun
  obtain ⟨state, body, txs, withdrawn, requested, hState, hBody, hTxs, hW, hNotW, hRequests,
    hRewards, hBuilder, -⟩ := applyBody_eq_ok h
  rw [daoTransfer_of_paris_le hParis] at hState
  cases hState
  -- The system calls run at position 0.
  obtain ⟨hP₁, hT₁, hI₁⟩ :=
    startSystemCalls_tracks hkeep hstart (AccessListBuilder.Tracks.init start) hBody
  -- The transactions run at the positions 1 to n.
  obtain ⟨hP₂, hT₂, hI₂⟩ := applyTransactions_tracks hkeep block.transactions 0
    ⟨body, .zero, 0, [], []⟩ txs hP₁ hT₁ (by rw [hI₁]; exact Nat.le_refl _) (by omega) hTxs
  -- The withdrawals and the requests run at position n + 1.
  have hn : block.transactions.length + 1 < 2 ^ 32 := by omega
  have hlt : txs.body.builder.index < UInt32.ofNat (block.transactions.length + 1) := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' hn]
    omega
  have hT₃ := BodyState.tracks_beginIndex hT₂ hlt
  have hW' : P withdrawn.block ∧ withdrawn.builder.Tracks start withdrawn.block := by
    by_cases hShapella : .shapella ≤ fork
    · obtain ⟨tx, hTx, hJoin⟩ := hW hShapella
      obtain ⟨hfollow, hP'⟩ := hkeep.withdrawals _ _ _ hP₂ hTx
      obtain ⟨h₁, h₂, -⟩ := BodyState.join_keeps hT₃ hfollow hP' hJoin
      exact ⟨h₁, h₂⟩
    · rw [hNotW hShapella]
      exact ⟨hP₂, hT₃⟩
  have hR : requested.builder.Tracks start requested.block := by
    obtain ⟨hNoPectra, hPectra⟩ := blockRequests_eq_ok hRequests
    by_cases hp : .pectra ≤ fork
    · obtain ⟨_, read, -, hRead, hResult⟩ := hPectra hp
      obtain ⟨rfl, -⟩ := Prod.mk.inj hResult
      exact (readRequests_tracks hkeep hW'.1 hW'.2
        ((readRequests_of_pectra hp).trans hRead)).2
    · obtain ⟨rfl, -⟩ := Prod.mk.inj (hNoPectra hp)
      exact hW'.2
  -- From Paris the rewards write nothing.
  simp only [payRewards_of_paris_le hParis] at hRewards
  obtain ⟨hacc, hsto⟩ := onBlock_pure hRewards
  rw [hBuilder]
  exact hR.congr hacc hsto

/-- From Glamsterdam, the list that a block commits to rebuilds the state after the block.

The hash in the header is the hash of the list that the builder built after the body.

The last change of each field in that list, or its value before the block, is its value after.

An account missing from a state reads as the empty account, so an empty account counts as none.

The nonce is in 64 bits, as the list holds it, which loses nothing below 2^64.

The calls of the body keep a property of block states that the state before the block has.

That excludes storage at an account that is empty or missing, since deleting it wipes its storage.

Storage at an account with a balance alone needs no exclusion: a creation there fails, by EIP-7610.

The block has fewer than 2^32 - 1 transactions.

From Hegota the transition is not yet specified, so this holds from Glamsterdam up to Hegota. -/
theorem stateTransition_rebuild {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State} {P : BlockState → Prop} (hFork : .glamsterdam ≤ fork)
    (hkeep : ∀ hashes, recentHashes chain.recent = .ok hashes →
      KeepsFollowable (blockEnvironment chain.config hashes block.header) P)
    (hstart : P ⟨chain.state, ∅, ∅, ∅, ∅⟩) (hlength : block.transactions.length < 2 ^ 32 - 1)
    (h : stateTransition chain block checkSeal = .ok post) :
    ∃ hashes output,
      recentHashes chain.recent = .ok hashes ∧
      applyBody chain.config (blockEnvironment chain.config hashes block.header) block
        ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output ∧
      BlockAccessList.hash output.body.builder.build =
        .ok (block.header.blockAccessListHash hFork) ∧
      ∀ address,
        ((post.getAccountOptional address).getD EMPTY_ACCOUNT).balance =
          output.body.builder.build.balanceAfter address
            ((chain.state.getAccountOptional address).getD EMPTY_ACCOUNT).balance ∧
        UInt64.ofNat ((post.getAccountOptional address).getD EMPTY_ACCOUNT).nonce =
          output.body.builder.build.nonceAfter address
            (UInt64.ofNat ((chain.state.getAccountOptional address).getD EMPTY_ACCOUNT).nonce) ∧
        ((post.getAccountOptional address).getD EMPTY_ACCOUNT).codeHash =
          output.body.builder.build.codeHashAfter address
            ((chain.state.getAccountOptional address).getD EMPTY_ACCOUNT).codeHash ∧
        ∀ key, post.getStorage address key =
          output.body.builder.build.storageAfter address key
            (chain.state.getStorage address key) := by
  obtain ⟨-, -, -, hashes, output, _, hHashes, hOutput, -, hChecks, rfl⟩ :=
    stateTransition_eq_ok h
  obtain ⟨value, hValue, hHash⟩ := applyBody_accessListHash hOutput hFork
  rw [accessListHash_of_outputChecks hFork hChecks] at hValue
  cases hValue
  have hT := applyBody_tracks (Nat.le_trans (by decide) hFork) (hkeep hashes hHashes) hstart
    hlength hOutput
  refine ⟨hashes, output, hHashes, hOutput, hHash, fun address => ?_⟩
  have hacc : (output.block.applyChanges.getAccountOptional address).getD EMPTY_ACCOUNT =
      (TransactionState.ofBlock output.block).getAccount address := by
    rw [BlockState.getAccountOptional_applyChanges]
    rfl
  refine ⟨?_, ?_, ?_, fun key => ?_⟩
  · rw [hacc]
    exact hT.balance_build address
  · rw [hacc]
    exact hT.nonce_build address
  · rw [hacc]
    exact hT.codeHash_build address
  · rw [BlockState.getStorage_applyChanges]
    exact hT.storage_build address key

end EthLib.Execution.Blocks
