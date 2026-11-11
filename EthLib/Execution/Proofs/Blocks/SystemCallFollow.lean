module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Blocks.SystemCall
public import EthLib.Execution.Proofs.Blocks.AccessListFollow
public import EthLib.Execution.Proofs.Blocks.SystemCall
public import EthLib.Execution.Proofs.Blocks.SystemCall.Contract
public import EthLib.Execution.Proofs.Evm.Call.Rebuild

/-!
# Proofs: the access-list builder follows the system calls

From Spurious Dragon, a system call runs one message with zero value and no authorization.

Its target has code whenever the frame runs nonempty bytecode or follows a delegation indicator.

By EIP-7610, any creation inside the call fails at an address that already holds storage.

So unwritten storage words keep their block values, and each read code hashes to its key.

Thus the access-list builder follows the call, and the block state afterward can still be rebuilt.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State
open EthLib.Execution.Transactions

/-- With no write on a block state that can be rebuilt, the transaction state has `RebuildState`. -/
theorem Rebuildable.rebuildState {block : BlockState} (valid : Rebuildable block) :
    RebuildState block (.ofBlock block) :=
  RebuildState.ofBlock valid.code valid.storage

/-- Every `RebuildState` satisfies `RebuildInvariant`. -/
theorem _root_.EthLib.Execution.Evm.RebuildState.rebuildInvariant {block : BlockState}
    {tx : TransactionState} (valid : RebuildState block tx) : RebuildInvariant tx :=
  ⟨valid.code, valid.emptyStorage⟩

/-- Every `RebuildState` is `Followable` on its block. -/
theorem _root_.EthLib.Execution.Evm.RebuildState.followable {block : BlockState}
    {tx : TransactionState} (valid : RebuildState block tx) : Followable block tx :=
  ⟨valid.parent, fun _ _ hslot => valid.getStorage_of_slot_eq_none hslot,
    fun _ _ code _ hread => valid.code _ code hread⟩

/-- Preparing the first frame of a system message keeps `RebuildState` and prepares a valid call. -/
private theorem prepareFirstFrame_systemMessage {fork : Fork} {Meter : Type} [GasMeter Meter]
    {env : BlockEnvironment fork} {block : BlockState} {target : Address} {data : ByteArray}
    {first : FirstFrame fork Meter} (valid : RebuildState block (.ofBlock block))
    (h : prepareFirstFrame (Meter := Meter) env.chainId.toNat (systemMessage env target data)
      (.ofBlock block) Substate.empty [] ∅ = .ok first) :
    RebuildState block first.state ∧
      first.message.shouldTransferValue = false ∧
      (first.message.code.size ≠ 0 → HasNonceOrCode first.state first.message.currentTarget) := by
  unfold prepareFirstFrame at h
  simp only [systemMessage, applyAuthorizations, List.foldlM_nil] at h
  dsimp only [bind, Except.bind, pure, Except.pure] at h
  have hval : ¬((0 : U256) ≠ 0) := fun h0 => h0 rfl
  simp only [hval, false_and, and_false, ↓reduceIte] at h
  let s1 := (TransactionState.ofBlock block).recordAccountRead target
  have hs1_sw : SameWrites s1 (.ofBlock block) := SameWrites.recordAccountRead _ _
  have hs1_p : s1.parent = (TransactionState.ofBlock block).parent := rfl
  have vs1 : RebuildState block s1 := valid.of_sameWrites hs1_sw hs1_p
  obtain ⟨code, hcode_map, h⟩ := bind_ok_iff.mp h
  have hcode : s1.getCode (s1.getAccount target).codeHash = .ok code :=
    mapError_ok_iff.mp hcode_map
  have hhash_of_nonempty : code ≠ .empty → (s1.getAccount target).codeHash ≠ EMPTY_CODE_HASH := by
    intro hne hh
    rw [hh] at hcode
    simp only [TransactionState.getCode, ↓reduceIte, Except.ok.injEq] at hcode
    exact hne hcode.symm
  generalize hdel : (if fork ≥ .pectra then delegatedAddress code else none) = delegate at h
  rcases delegate with _ | delegate
  · cases h
    refine ⟨vs1, rfl, fun hsize => .inr (hhash_of_nonempty ?_)⟩
    intro hempty
    rw [hempty] at hsize
    exact hsize rfl
  · have hcode_ne : code ≠ .empty := by
      intro hempty
      rw [hempty, delegatedAddress_empty, ite_self] at hdel
      cases hdel
    have hs1_nc : HasNonceOrCode s1 target := .inr (hhash_of_nonempty hcode_ne)
    let s2 := s1.recordAccountRead delegate
    have hs2_sw : SameWrites s2 s1 := SameWrites.recordAccountRead _ _
    have hs2_p : s2.parent = s1.parent := rfl
    have vs2 : RebuildState block s2 := vs1.of_sameWrites hs2_sw hs2_p
    have hs2_nc : HasNonceOrCode s2 target :=
      (SameWrites.keepsNonceOrCode hs2_sw hs2_p).2 target hs1_nc
    dsimp only at h
    split at h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
          exact ⟨vs2, rfl, fun _ => hs2_nc⟩
    · split at h
      · cases h
      · cases h
        exact ⟨vs2, rfl, fun _ => hs2_nc⟩

/-- Running a system message from Spurious Dragon keeps `RebuildState`. -/
private theorem processMessageCall_systemMessage {fork : Fork} {Meter : Type} [GasMeter Meter]
    [LawfulGasMeter Meter] (hfork : .spuriousDragon ≤ fork) {env : BlockEnvironment fork}
    {block : BlockState} {target : Address} {data : ByteArray} {out : CallOutput}
    (valid : Rebuildable block)
    (h : processMessageCall (Meter := Meter) env.chainId.toNat (systemMessage env target data)
      (.ofBlock block) Substate.empty = .ok out) :
    RebuildState block out.state := by
  have v0 := valid.rebuildState
  unfold processMessageCall at h
  rcases hprep : prepareFirstFrame (Meter := Meter) env.chainId.toNat
      (systemMessage env target data) (.ofBlock block) Substate.empty [] ∅ with ⟨e, read⟩ | first
  · rw [hprep] at h
    dsimp only at h
    split at h
    · cases h
    · cases h
      exact v0.of_sameWrites (SameWrites.withReadsOf _ _) rfl
  · rw [hprep] at h
    obtain ⟨vfirst, hval, hcode⟩ := prepareFirstFrame_systemMessage v0 hprep
    have htarget : (systemMessage env target data).target = some target := rfl
    rw [htarget] at h
    dsimp only at h
    obtain ⟨ended, hended, hpure⟩ := bind_ok_iff.mp h
    cases hpure
    obtain ⟨vended, -⟩ := processMessage_rebuildState hfork vfirst hcode
      (.inl fun hc => Bool.noConfusion (hval.symm.trans hc.1)) hended
    have hframe_state : ∀ {r t}, (CallOutput.ofFrame ended.val r t).state = ended.val.state := by
      intro r t
      unfold CallOutput.ofFrame
      dsimp only
      split <;> rfl
    rw [hframe_state]
    exact vended

/-- From Spurious Dragon, a system call on a rebuildable block state keeps `RebuildState`. -/
theorem systemCall_rebuildState {fork : Fork} (hfork : .spuriousDragon ≤ fork)
    {env : BlockEnvironment fork} {block : BlockState} {target : Address} {data : ByteArray}
    {out : SystemCallOutput} (valid : Rebuildable block)
    (h : systemCall env block target data = .ok out) :
    RebuildState block out.state := by
  unfold systemCall at h
  split at h <;>
  · obtain ⟨call, hcall, hpure⟩ := bind_ok_iff.mp h
    cases hpure
    exact processMessageCall_systemMessage hfork valid hcall

/-- From Spurious Dragon, the access-list builder follows each system call. -/
theorem systemCall_followable {fork : Fork} (hfork : .spuriousDragon ≤ fork)
    {env : BlockEnvironment fork} {block : BlockState} {target : Address} {data : ByteArray}
    {out : SystemCallOutput} (valid : Rebuildable block)
    (h : systemCall env block target data = .ok out) :
    Followable block out.state :=
  (systemCall_rebuildState hfork valid h).followable

/-- From Spurious Dragon, after a system call, the block state can still be rebuilt. -/
theorem systemCall_rebuildable {fork : Fork} (hfork : .spuriousDragon ≤ fork)
    {env : BlockEnvironment fork} {block : BlockState} {target : Address} {data : ByteArray}
    {out : SystemCallOutput} (valid : Rebuildable block)
    (h : systemCall env block target data = .ok out) :
    Rebuildable out.block :=
  (systemCall_rebuildState hfork valid h).rebuildInvariant.ofBlock_incorporateTxIntoBlock

/-- Joining a followed state that can be rebuilt keeps `Rebuildable` and `Tracks`, at its index. -/
private theorem join_tracks_rebuildable {body body' : BodyState} {tx : TransactionState}
    {base : BlockState} (h : body.builder.Tracks base body.block)
    (hfollow : Followable body.block tx) (hreb : Rebuildable tx.incorporateTxIntoBlock.parent)
    (hjoin : body.join tx = .ok body') :
    Rebuildable body'.block ∧ body'.builder.Tracks base body'.block ∧
      body'.builder.index = body.builder.index := by
  obtain ⟨builder, hrecord, rfl⟩ := BodyState.join_eq_ok hjoin
  exact ⟨hreb, h.recordTransaction hfollow hrecord,
    (AccessListBuilder.recordTransaction_index hrecord).1⟩

/-- The system calls at the start of a block keep `Rebuildable` and `Tracks`, at the same index. -/
theorem startSystemCalls_rebuildable {fork : Fork} {env : BlockEnvironment fork}
    {parentHash : Hash32} {body body' : BodyState} {base : BlockState}
    (valid : Rebuildable body.block) (tracks : body.builder.Tracks base body.block)
    (h : startSystemCalls env parentHash body = .ok body') :
    Rebuildable body'.block ∧ body'.builder.Tracks base body'.block ∧
      body'.builder.index = body.builder.index := by
  obtain ⟨mid, hFirst, hNoFirst, hSecond, hNoSecond⟩ := startSystemCalls_eq_ok h
  have hmid : Rebuildable mid.block ∧ mid.builder.Tracks base mid.block ∧
      mid.builder.index = body.builder.index := by
    by_cases hDencun : .dencun ≤ fork
    · obtain ⟨out, hOut, hJoin⟩ := hFirst hDencun
      have hsd : .spuriousDragon ≤ fork := Nat.le_trans (by decide) hDencun
      exact join_tracks_rebuildable tracks (systemCall_followable hsd valid hOut)
        (systemCall_rebuildable hsd valid hOut) hJoin
    · obtain rfl := hNoFirst hDencun
      exact ⟨valid, tracks, rfl⟩
  by_cases hPectra : .pectra ≤ fork
  · obtain ⟨out, hOut, hJoin⟩ := hSecond hPectra
    have hsd : .spuriousDragon ≤ fork := Nat.le_trans (by decide) hPectra
    obtain ⟨h1, h2, h3⟩ := join_tracks_rebuildable hmid.2.1 (systemCall_followable hsd hmid.1 hOut)
      (systemCall_rebuildable hsd hmid.1 hOut) hJoin
    exact ⟨h1, h2, h3.trans hmid.2.2⟩
  · rw [hNoSecond hPectra]
    exact hmid

/-- Reading the request contracts keeps `Rebuildable` and `Tracks`. -/
theorem readRequests_rebuildable {fork : Fork} {env : BlockEnvironment fork}
    {base : BlockState} {body body' : BodyState} {requests : List ByteArray}
    (valid : Rebuildable body.block) (tracks : body.builder.Tracks base body.block)
    (h : readRequests env body = .ok (body', requests)) :
    Rebuildable body'.block ∧ body'.builder.Tracks base body'.block := by
  by_cases hPectra : .pectra ≤ fork
  · have hsd : .spuriousDragon ≤ fork := Nat.le_trans (by decide) hPectra
    rw [readRequests_of_pectra hPectra] at h
    refine foldlM_ok_invariant
      (fun s : BodyState × List ByteArray =>
        Rebuildable s.1.block ∧ s.1.builder.Tracks base s.1.block)
      (fun s _ s' hs hs' => ?_) ⟨valid, tracks⟩ h
    obtain ⟨out, hOut, hJoin, -⟩ := readRequest_eq_ok hs'
    have hCall := (checkedSystemCall_ok hOut).2.1
    obtain ⟨h1, h2, -⟩ := join_tracks_rebuildable hs.2 (systemCall_followable hsd hs.1 hCall)
      (systemCall_rebuildable hsd hs.1 hCall) hJoin
    exact ⟨h1, h2⟩
  · rw [readRequests_of_lt_pectra (Nat.lt_of_not_le hPectra)] at h
    cases h
    exact ⟨valid, tracks⟩

/-- The empty block state can be rebuilt, and a system call on it to the beacon roots succeeds. -/
theorem exists_rebuildable_systemCall {fork : Fork} (hfork : .paris ≤ fork)
    (env : BlockEnvironment fork) (data : ByteArray) :
    ∃ (block : BlockState) (out : SystemCallOutput),
      Rebuildable block ∧
      systemCall env block BEACON_ROOTS_ADDRESS data = .ok out ∧
      out.error = none ∧
      Followable block out.state ∧
      Rebuildable out.block := by
  let block : BlockState := ⟨⟨∅, ∅, ∅⟩, ∅, ∅, ∅, ∅⟩
  have hvalid : Rebuildable block := by
    refine ⟨fun hash code hread => ?_, fun _ _ _ => rfl⟩
    unfold TransactionState.getCode TransactionState.ofBlock State.getCode at hread
    dsimp only [block] at hread
    have hnone : (∅ : Std.ExtTreeMap Hash32 ByteArray)[hash]? = none :=
      Std.ExtTreeMap.getElem?_empty
    by_cases hempty : hash = EMPTY_CODE_HASH
    · subst hempty
      simp only [↓reduceIte, Except.ok.injEq] at hread
      subst hread
      rfl
    · simp only [hempty, ↓reduceIte, hnone] at hread
      cases hread
  have hpre : Precompiles.addedAt BEACON_ROOTS_ADDRESS.toU256.toNat = none := by
    rw [BEACON_ROOTS_ADDRESS, EthLib.Base.toNat_toU256_toAddressMasked]
    rfl
  have hcode : codeAt block BEACON_ROOTS_ADDRESS = .ok .empty := by
    unfold codeAt TransactionState.getAccount TransactionState.getAccountOptional
      TransactionState.getCode TransactionState.ofBlock State.getAccountOptional
    dsimp only [block]
    have hnone : (∅ : Std.ExtTreeMap Address (Option Account))[BEACON_ROOTS_ADDRESS]? = none :=
      Std.ExtTreeMap.getElem?_empty
    have hnone' : (∅ : Std.ExtTreeMap Address Account)[BEACON_ROOTS_ADDRESS]? = none :=
      Std.ExtTreeMap.getElem?_empty
    simp only [hnone, hnone', Option.getD_none, EMPTY_ACCOUNT, ↓reduceIte, Except.mapError]
  have hcall := SystemContract.systemCall_of_empty (env := env) (block := block)
    (target := BEACON_ROOTS_ADDRESS) (data := data) hfork hcode hpre
  have hsd : .spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  exact ⟨block, _, hvalid, hcall, rfl,
    systemCall_followable hsd hvalid hcall,
    systemCall_rebuildable hsd hvalid hcall⟩

end EthLib.Execution.Blocks
