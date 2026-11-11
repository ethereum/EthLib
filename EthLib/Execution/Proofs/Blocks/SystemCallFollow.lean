module

public import EthLib.Execution.Proofs.Blocks.AccessListFollow
public import EthLib.Execution.Proofs.Blocks.SystemCall.Contract
public import EthLib.Execution.Proofs.Evm.Call.Rebuild

/-!
# Proofs: the access-list builder follows the system calls

A system call runs one message with zero value and no authorization.

Its target has code whenever the frame runs nonempty bytecode or follows a delegation indicator.

By [EIP-7610][eip7610], any creation inside the call fails at an address that already holds storage.

From Spurious Dragon, a created account starts at nonce 1, so it may hold storage.

So unwritten storage words keep their block values, and each read code hashes to its key.

Thus the access-list builder follows the call, and the block state afterward can still be rebuilt.

This needs the block state before the call to be rebuildable.

Its code matches its hash, and no empty account holds storage.

[eip7610]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7610.md#specification
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State
open EthLib.Execution.Transactions

/-- The access-list builder follows every state with the rebuild property on its block. -/
theorem _root_.EthLib.Execution.Evm.RebuildState.followable {block : BlockState}
    {tx : TransactionState} (valid : RebuildState block tx) : Followable block tx :=
  ⟨valid.parent, fun _ _ hslot => valid.getStorage_of_slot_eq_none hslot,
    fun _ _ code _ hread => valid.code _ code hread⟩

/-- Preparing the first frame of a system message keeps the rebuild property and moves no value.

If the frame runs code, its target has a nonce or code. -/
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

/-- From Spurious Dragon, running a system message keeps the rebuild property. -/
private theorem processMessageCall_systemMessage {fork : Fork} {Meter : Type} [GasMeter Meter]
    [LawfulGasMeter Meter] (hfork : .spuriousDragon ≤ fork) {env : BlockEnvironment fork}
    {block : BlockState} {target : Address} {data : ByteArray} {out : CallOutput}
    (valid : Rebuildable block)
    (h : processMessageCall (Meter := Meter) env.chainId.toNat (systemMessage env target data)
      (.ofBlock block) Substate.empty = .ok out) :
    RebuildState block out.state := by
  have v0 := RebuildState.ofBlock valid
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

/-- From Spurious Dragon, a system call keeps the rebuild property of its block state. -/
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
  (systemCall_rebuildState hfork valid h).toRebuildInvariant.ofBlock_incorporateTxIntoBlock

/-- From Paris, the empty block state can be rebuilt, and a system call on it succeeds.

The call goes to the beacon roots address, which holds no code there.

The builder follows the call, and the state after it can still be rebuilt. -/
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
