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

This holds when the calls of the body keep a property of block states.

Each call fits when a predicate allows each address whose storage it wiped.

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

/-- A call that ran on `block` keeps `P`, and the builder follows it if `W` allows its wipes.

A wipe hides the words of storage before it, and the list records none of them. -/
structure KeepsIf (P : BlockState → Prop) (W : Address → Prop) (block : BlockState)
    (tx : TransactionState) : Prop where
  /-- The call ran on the block state. -/
  parent : tx.parent = block
  /-- The block state after the call has `P`. -/
  keeps : P tx.incorporateTxIntoBlock.parent
  /-- The builder follows the call if `W` holds at each address whose storage it wiped. -/
  follows : (∀ address ∈ tx.storageClears, W address) → Followable block tx

/-- The calls of a body at `fork` keep a property `P` of block states.

The builder follows each call whose wipes `W` allows.

These are assumptions on the calls, which this file does not prove. -/
structure KeepsFollowable (env : BlockEnvironment fork) (P : BlockState → Prop)
    (W : Address → Prop) : Prop where
  /-- Each system call. -/
  systemCall : ∀ block target data out, P block →
    systemCall env block target data = .ok out → KeepsIf P W block out.state
  /-- Each transaction that enters the block. -/
  transaction : ∀ gas block tx included out, P block →
    checkInclusion env.chainId env gas (.ofBlock block) tx = .ok included →
    processTransaction env block included tx = .ok out → KeepsIf P W block out.state
  /-- The withdrawals. -/
  withdrawals : ∀ block withdrawals tx, P block →
    withdrawalState fork block withdrawals = .ok tx → KeepsIf P W block tx

/-- `W` holds at each address whose storage the block state wiped. -/
private def WipesIn (W : Address → Prop) (block : BlockState) : Prop :=
  ∀ address ∈ block.storageClears, W address

/-- The second block state keeps each wipe of the first. -/
private def ClearsLe (block block' : BlockState) : Prop :=
  ∀ address ∈ block.storageClears, address ∈ block'.storageClears

private theorem ClearsLe.trans {a b c : BlockState} (hab : ClearsLe a b) (hbc : ClearsLe b c) :
    ClearsLe a c :=
  fun address h => hbc address (hab address h)

/-- What `W` allows in a later block state, it allows in an earlier one. -/
private theorem WipesIn.of_clearsLe {W : Address → Prop} {block block' : BlockState}
    (h : WipesIn W block') (hle : ClearsLe block block') : WipesIn W block :=
  fun address hmem => h address (hle address hmem)

/-- The wipes of the block state after a call are those of the call and those of its block. -/
private theorem mem_storageClears_incorporateTxIntoBlock {tx : TransactionState}
    {address : Address} :
    address ∈ tx.incorporateTxIntoBlock.parent.storageClears ↔
      address ∈ tx.storageClears ∨ address ∈ tx.parent.storageClears :=
  State.mem_foldl_insert _ _ _

/-- A call that keeps the property joins the body and keeps it, at the same position.

The body keeps each earlier wipe, and follows the block if `W` allows each wipe after the call. -/
private theorem BodyState.join_keeps {P : BlockState → Prop} {W : Address → Prop}
    {body body' : BodyState} {tx : TransactionState} {base : BlockState}
    (hstep : KeepsIf P W body.block tx) (hjoin : body.join tx = .ok body') :
    P body'.block ∧ ClearsLe body.block body'.block ∧
      (WipesIn W body'.block → body.builder.Tracks base body.block →
        body'.builder.Tracks base body'.block) ∧
      body'.builder.index = body.builder.index := by
  obtain ⟨builder, hrecord, rfl⟩ := BodyState.join_eq_ok hjoin
  refine ⟨hstep.keeps, fun address hmem => ?_, fun hwipes h => ?_,
    (AccessListBuilder.recordTransaction_index hrecord).1⟩
  · rw [← hstep.parent] at hmem
    exact mem_storageClears_incorporateTxIntoBlock.mpr (.inr hmem)
  · exact h.recordTransaction (hstep.follows fun address hmem =>
      hwipes address (mem_storageClears_incorporateTxIntoBlock.mpr (.inl hmem))) hrecord

/-- The system calls at the start keep the property and the builder, at the same position. -/
private theorem startSystemCalls_tracks {env : BlockEnvironment fork} {P : BlockState → Prop}
    {W : Address → Prop} {parentHash : Hash32} {body body' : BodyState} {base : BlockState}
    (hkeep : KeepsFollowable env P W) (hP : P body.block)
    (hcalls : startSystemCalls env parentHash body = .ok body') :
    P body'.block ∧ ClearsLe body.block body'.block ∧
      (WipesIn W body'.block → body.builder.Tracks base body.block →
        body'.builder.Tracks base body'.block) ∧
      body'.builder.index = body.builder.index := by
  obtain ⟨mid, hFirst, hNoFirst, hSecond, hNoSecond⟩ := startSystemCalls_eq_ok hcalls
  have hmid : P mid.block ∧ ClearsLe body.block mid.block ∧
      (WipesIn W mid.block → body.builder.Tracks base body.block →
        mid.builder.Tracks base mid.block) ∧
      mid.builder.index = body.builder.index := by
    by_cases hDencun : .dencun ≤ fork
    · obtain ⟨out, hOut, hJoin⟩ := hFirst hDencun
      exact BodyState.join_keeps (hkeep.systemCall _ _ _ _ hP hOut) hJoin
    · obtain rfl := hNoFirst hDencun
      exact ⟨hP, fun _ h => h, fun _ h => h, rfl⟩
  by_cases hPectra : .pectra ≤ fork
  · obtain ⟨out, hOut, hJoin⟩ := hSecond hPectra
    obtain ⟨h₁, h₂, h₃, h₄⟩ :=
      BodyState.join_keeps (hkeep.systemCall _ _ _ _ hmid.1 hOut) hJoin
    exact ⟨h₁, hmid.2.1.trans h₂,
      fun hwipes h => h₃ hwipes (hmid.2.2.1 (hwipes.of_clearsLe h₂) h), h₄.trans hmid.2.2.2⟩
  · rw [hNoSecond hPectra]
    exact hmid

/-- The transactions keep the property and the builder, whose position is at most the last one. -/
private theorem applyTransactions_tracks {env : BlockEnvironment fork} {P : BlockState → Prop}
    {W : Address → Prop} {base : BlockState} (hkeep : KeepsFollowable env P W) :
    ∀ (l : List Transaction) (m : Nat) (before out : BodyOutput fork),
      P before.body.block → before.body.builder.index.toNat ≤ m → m + l.length < 2 ^ 32 →
      (l.zipIdx m).foldlM (fun before (tx, index) => applyTransaction env index before tx)
        before = .ok out →
      P out.body.block ∧ ClearsLe before.body.block out.body.block ∧
        (WipesIn W out.body.block → before.body.builder.Tracks base before.body.block →
          out.body.builder.Tracks base out.body.block) ∧
        out.body.builder.index.toNat ≤ m + l.length
  | [], m, before, out, hP, hindex, _, hfold => by
    simp only [List.zipIdx_nil, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
    subst hfold
    exact ⟨hP, fun _ h => h, fun _ h => h, by simpa using hindex⟩
  | tx :: l, m, before, out, hP, hindex, hlength, hfold => by
    rw [List.zipIdx_cons, List.foldlM_cons, bind_ok_iff] at hfold
    obtain ⟨next, hnext, hrest⟩ := hfold
    obtain ⟨included, run, hIncluded, hRun, -, -, hJoin⟩ := applyTransaction_eq_ok hnext
    have hm : m + 1 < 2 ^ 32 := by simp only [List.length_cons] at hlength; omega
    have hlt : before.body.builder.index < UInt32.ofNat (m + 1) := by
      rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' hm]
      omega
    obtain ⟨h₁, h₂, h₃, h₄⟩ :=
      BodyState.join_keeps (body := before.body.beginIndex (m + 1))
        (hkeep.transaction _ _ _ _ _ hP hIncluded hRun) hJoin
    have hnext : next.body.builder.index.toNat ≤ m + 1 := by
      rw [h₄]
      show (UInt32.ofNat (m + 1)).toNat ≤ m + 1
      rw [UInt32.toNat_ofNat_of_lt' hm]
      exact Nat.le_refl _
    obtain ⟨r₁, r₂, r₃, r₄⟩ := applyTransactions_tracks hkeep l (m + 1) next out h₁ hnext
      (by simp only [List.length_cons] at hlength; omega) hrest
    simp only [List.length_cons]
    exact ⟨r₁, h₂.trans r₂, fun hwipes h =>
      r₃ hwipes (h₃ (hwipes.of_clearsLe r₂) (BodyState.tracks_beginIndex h hlt)), by omega⟩

/-- The calls to the request contracts keep the property and the builder. -/
private theorem readRequests_tracks {env : BlockEnvironment fork} {P : BlockState → Prop}
    {W : Address → Prop} {base : BlockState} {body body' : BodyState}
    {requests : List ByteArray} (hkeep : KeepsFollowable env P W) (hP : P body.block)
    (hread : readRequests env body = .ok (body', requests)) :
    P body'.block ∧ ClearsLe body.block body'.block ∧
      (WipesIn W body'.block → body.builder.Tracks base body.block →
        body'.builder.Tracks base body'.block) := by
  by_cases hPectra : .pectra ≤ fork
  · rw [readRequests_of_pectra hPectra] at hread
    refine foldlM_ok_invariant
      (fun s : BodyState × List ByteArray => P s.1.block ∧ ClearsLe body.block s.1.block ∧
        (WipesIn W s.1.block → body.builder.Tracks base body.block →
          s.1.builder.Tracks base s.1.block))
      (fun s c s' hs hs' => ?_) ⟨hP, fun _ h => h, fun _ h => h⟩ hread
    obtain ⟨out, hOut, hJoin, -⟩ := readRequest_eq_ok hs'
    obtain ⟨h₁, h₂, h₃, -⟩ :=
      BodyState.join_keeps (hkeep.systemCall _ _ _ _ hs.1 (checkedSystemCall_ok hOut).2.1) hJoin
    exact ⟨h₁, hs.2.1.trans h₂, fun hwipes h => h₃ hwipes (hs.2.2 (hwipes.of_clearsLe h₂) h)⟩
  · rw [readRequests_of_lt_pectra (Nat.lt_of_not_le hPectra)] at hread
    cases hread
    exact ⟨hP, fun _ h => h, fun _ h => h⟩

/-- A block state reads each account and word as it did after a step that wrote nothing.

It keeps each wipe too. -/
private theorem onBlock_pure {block block' : BlockState}
    (h : onBlock block (fun tx => .ok tx) = .ok block') :
    (∀ address, (TransactionState.ofBlock block').getAccount address =
      (TransactionState.ofBlock block).getAccount address) ∧
    (∀ address key, (TransactionState.ofBlock block').getStorage address key =
      (TransactionState.ofBlock block).getStorage address key) ∧
    ClearsLe block block' := by
  obtain ⟨tx, htx, rfl⟩ := onBlock_eq_ok h
  cases htx
  exact ⟨State.TransactionState.getAccount_ofBlock_incorporateTxIntoBlock _,
    State.TransactionState.getStorage_incorporateTxIntoBlock _,
    fun _ hmem => mem_storageClears_incorporateTxIntoBlock.mpr (.inr hmem)⟩

/-- From Dencun, the builder at the end of a body follows the block from its start.

Before Dencun, a SELFDESTRUCT can wipe storage that the list does not name.

So the property is not expected to hold there, and the theorem starts at Dencun. -/
theorem applyBody_tracks {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    -- The calls of the body keep a property of block states.
    --
    -- The builder follows each call whose wipes `W` allows.
    {P : BlockState → Prop} {W : Address → Prop} (hDencun : .dencun ≤ fork)
    (hkeep : KeepsFollowable env P W)
    -- The start has that property.
    --
    -- The block has fewer than 2^32 - 1 transactions, so each position fits in 32 bits.
    (hstart : P start) (hlength : block.transactions.length < 2 ^ 32 - 1)
    (h : applyBody config env block start = .ok output)
    -- `W` holds at each address whose storage the body wiped.
    (hwipes : ∀ address ∈ output.block.storageClears, W address) :
    output.body.builder.Tracks start output.block := by
  have hParis : Fork.paris ≤ fork := Nat.le_trans (by decide) hDencun
  obtain ⟨state, body, txs, withdrawn, requested, hState, hBody, hTxs, hW, hNotW, hRequests,
    hRewards, hBuilder, -⟩ := applyBody_eq_ok h
  rw [daoTransfer_of_paris_le hParis] at hState
  cases hState
  -- The system calls run at position 0.
  obtain ⟨hP₁, -, hT₁, hI₁⟩ := startSystemCalls_tracks (base := start) hkeep hstart hBody
  -- The transactions run at the positions 1 to n.
  obtain ⟨hP₂, hC₂, hT₂, hI₂⟩ := applyTransactions_tracks (base := start) hkeep
    block.transactions 0 ⟨body, .zero, 0, [], [], []⟩ txs hP₁ (by rw [hI₁]; exact Nat.le_refl _)
    (by omega) hTxs
  -- The withdrawals and the requests run at position n + 1.
  have hn : block.transactions.length + 1 < 2 ^ 32 := by omega
  have hlt : txs.body.builder.index < UInt32.ofNat (block.transactions.length + 1) := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' hn]
    omega
  have hW' : P withdrawn.block ∧ ClearsLe txs.body.block withdrawn.block ∧
      (WipesIn W withdrawn.block →
        (txs.body.beginIndex (block.transactions.length + 1)).builder.Tracks start
          (txs.body.beginIndex (block.transactions.length + 1)).block →
        withdrawn.builder.Tracks start withdrawn.block) := by
    by_cases hShapella : .shapella ≤ fork
    · obtain ⟨tx, hTx, hJoin⟩ := hW hShapella
      obtain ⟨h₁, h₂, h₃, -⟩ :=
        BodyState.join_keeps (body := txs.body.beginIndex (block.transactions.length + 1))
          (hkeep.withdrawals _ _ _ hP₂ hTx) hJoin
      exact ⟨h₁, h₂, h₃⟩
    · rw [hNotW hShapella]
      exact ⟨hP₂, fun _ h => h, fun _ h => h⟩
  have hR : ClearsLe withdrawn.block requested.block ∧
      (WipesIn W requested.block → withdrawn.builder.Tracks start withdrawn.block →
        requested.builder.Tracks start requested.block) := by
    obtain ⟨hNoPectra, hPectra⟩ := blockRequests_eq_ok hRequests
    by_cases hp : .pectra ≤ fork
    · obtain ⟨_, read, -, hRead, hResult⟩ := hPectra hp
      obtain ⟨rfl, -⟩ := Prod.mk.inj hResult
      exact (readRequests_tracks hkeep hW'.1 ((readRequests_of_pectra hp).trans hRead)).2
    · obtain ⟨rfl, -⟩ := Prod.mk.inj (hNoPectra hp)
      exact ⟨fun _ h => h, fun _ h => h⟩
  -- From Paris the rewards write nothing.
  simp only [payRewards_of_paris_le hParis] at hRewards
  obtain ⟨hacc, hsto, hclears⟩ := onBlock_pure hRewards
  -- Each block state of the body has its wipes among those at the end, which `W` allows.
  have w₄ : WipesIn W requested.block := WipesIn.of_clearsLe hwipes hclears
  have w₃ : WipesIn W withdrawn.block := w₄.of_clearsLe hR.1
  have w₂ : WipesIn W txs.body.block := w₃.of_clearsLe hW'.2.1
  have w₁ : WipesIn W body.block := w₂.of_clearsLe hC₂
  have t₂ := hT₂ w₂ (hT₁ w₁ (AccessListBuilder.Tracks.init start))
  rw [hBuilder]
  exact (hR.2 w₄ (hW'.2.2 w₃ (BodyState.tracks_beginIndex t₂ hlt))).congr hacc hsto

/-- From Glamsterdam, the list that a block commits to rebuilds the state after the block.

From Hegota the transition is not yet specified, so this holds from Glamsterdam up to Hegota. -/
theorem stateTransition_rebuild {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State} {P : BlockState → Prop} {W : Address → Prop}
    (hFork : .glamsterdam ≤ fork)
    -- The calls of the body keep a property of block states.
    --
    -- The builder follows each call whose wipes `W` allows.
    --
    -- A creation wipes the storage at its address.
    --
    -- So does SELFDESTRUCT, which deletes the account before Glamsterdam and clears it from then.
    (hkeep : ∀ hashes, recentHashes chain.recent = .ok hashes →
      KeepsFollowable (blockEnvironment chain.config hashes block.header) P W)
    -- The state before the block has that property.
    --
    -- The block has fewer than 2^32 - 1 transactions.
    (hstart : P ⟨chain.state, ∅, ∅, ∅, ∅⟩) (hlength : block.transactions.length < 2 ^ 32 - 1)
    -- `W` holds at each address whose storage the body wipes.
    (hwipes : ∀ hashes output, recentHashes chain.recent = .ok hashes →
      applyBody chain.config (blockEnvironment chain.config hashes block.header) block
        ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output →
      ∀ address ∈ output.block.storageClears, W address)
    (h : stateTransition chain block checkSeal = .ok post) :
    ∃ hashes output,
      recentHashes chain.recent = .ok hashes ∧
      applyBody chain.config (blockEnvironment chain.config hashes block.header) block
        ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output ∧
      -- The hash in the header is the hash of the list that the builder built after the body.
      BlockAccessList.hash output.body.builder.build =
        .ok (block.header.blockAccessListHash hFork) ∧
      -- Each field ends at its last change in that list, or else at its value before the block.
      --
      -- An account missing from a state reads as the empty account.
      --
      -- So an empty account counts as none.
      ∀ address,
        ((post.getAccountOptional address).getD EMPTY_ACCOUNT).balance =
          output.body.builder.build.balanceAfter address
            ((chain.state.getAccountOptional address).getD EMPTY_ACCOUNT).balance ∧
        -- The nonce is in 64 bits, as the list holds it, which loses nothing below 2^64.
        --
        -- A state whose nonces are at most 2^64 - 1 keeps that bound through the block.
        --
        -- A corollary shows that there, the 64-bit nonces equal the nonces after the block.
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
    hlength hOutput (hwipes hashes output hHashes hOutput)
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
