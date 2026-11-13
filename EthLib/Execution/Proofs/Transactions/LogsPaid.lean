module

public import EthLib.Execution.Proofs.Evm.Call.LogsPaid
public import EthLib.Execution.Proofs.Blocks.Receipt
public import EthLib.Execution.Proofs.Transactions.Replay

/-!
# Proofs: the logs of a transaction are paid for, so its receipt encodes

The logs of a transaction weigh at most a quarter of its gas, plus one transfer log of EIP-7708.

When its gas limit is below `2^64`, its logs weigh far less than `2^64`.

Its receipt then has an RLP encoding, when the gas it records is below `2^64` too.

That removes one cause of failure of a receipt: a payload too long to encode.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.Blocks (Log Outcome Receipt encodeReceipt makeReceipt)
open EthLib.Serialization.Rlp (Codec)

variable {fork : Fork} {tx : Transaction}

/-- The first frame of a message starts from the logs of the substate it is given. -/
private theorem logs_prepareFirstFrame {Meter : Type} [GasMeter Meter] {chainId : Nat}
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame chainId message state substate auths paid = .ok first) :
    first.substate.logs = substate.logs := by
  unfold prepareFirstFrame at h
  dsimp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  all_goals
    simp only [Except.ok.injEq] at h
    subst h
    rfl

/-- The first frame of a message holds at most its gas, when a commit raises no gas held. -/
private theorem gasHeld_prepareFirstFrame {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    (hcommit : ∀ meter : Meter, GasMeter.gasHeld (GasMeter.commit meter) ≤ GasMeter.gasHeld meter)
    {chainId : Nat} {message : Message fork} {state : State.TransactionState}
    {substate : Substate} {auths : List Authorization} {paid : Std.ExtTreeSet Address}
    {first : FirstFrame fork Meter}
    (h : prepareFirstFrame chainId message state substate auths paid = .ok first) :
    GasMeter.gasHeld first.meter ≤ message.gas := by
  have := meter_prepareFirstFrame (Q := fun a b => GasMeter.gasHeld b ≤ GasMeter.gasHeld a)
    (fun _ => Nat.le_refl _) (fun h₁ h₂ => Nat.le_trans h₂ h₁)
    (fun h => by have := LawfulGasMeter.gasHeld_charge h; omega)
    (fun h => LawfulGasMeter.gasHeld_chargeState h) hcommit h
  rwa [LawfulGasMeter.gasHeld_start] at this

/-- The logs of a frame that ends keep the bound of the frame, and an error keeps no log. -/
private theorem logsWeight_ofFrame {Meter : Type} [GasMeter Meter] {evm : Evm fork Meter}
    {refund : Nat} {touched : Std.ExtTreeSet Address} :
    logsWeight (CallOutput.ofFrame evm refund touched).logs.toList ≤
      logsWeight evm.substate.logs.toList := by
  unfold CallOutput.ofFrame
  split
  · simp [logsWeight]
  · exact Nat.le_refl _

/-- The message of a transaction writes logs of at most a quarter of its gas, plus one transfer log.

It must start with no logs, and its meter must hold no more gas after a commit.

Both meters of the forks meet that, and a message that fails keeps no log. -/
theorem processMessageCall_logsWeight {Meter : Type} [GasMeter Meter]
    [LawfulGasMeter Meter]
    (hcommit : ∀ meter : Meter, GasMeter.gasHeld (GasMeter.commit meter) ≤ GasMeter.gasHeld meter)
    {chainId : Nat} {message : Message fork} {state : State.TransactionState}
    {substate : Substate} {auths : List Authorization} {paid : Std.ExtTreeSet Address}
    {output : CallOutput} (hempty : substate.logs = #[])
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output) :
    4 * logsWeight output.logs.toList ≤ message.gas + transferAllowance fork := by
  unfold processMessageCall at h
  split at h
  · split at h
    · cases h
    · cases h
      simp [CallOutput.ofHalt, logsWeight]
  rename_i first hfirst
  have hlogs : logsWeight first.substate.logs.toList = 0 := by
    rw [logs_prepareFirstFrame hfirst, hempty]
    rfl
  have hheld := gasHeld_prepareFirstFrame hcommit hfirst
  split at h
  · obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    have hbound := processCreateMessage_logsWeight hrun
    dsimp only at hbound
    have := logsWeight_ofFrame (evm := evm) (refund := 0) (touched := evm.substate.touchedAccounts)
    omega
  · obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    have hbound := processMessage_logsWeight hrun
    dsimp only at hbound
    have := logsWeight_ofFrame (evm := evm) (refund := first.refund)
      (touched := if fork ≥ .spuriousDragon ∧ fork < .paris ∧
        evm.state.accountExistsAndIsEmpty ‹_› then evm.substate.touchedAccounts.insert ‹_›
        else evm.substate.touchedAccounts)
    omega

/-- A transaction that runs writes logs of at most a quarter of its gas limit, and one transfer log.

This holds when a commit of the meter raises no gas held. -/
private theorem runTransaction_logsWeight {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    (hcommit : ∀ meter : Meter, GasMeter.gasHeld (GasMeter.commit meter) ≤ GasMeter.gasHeld meter)
    {env : BlockEnvironment fork} {block : State.BlockState} {included : Included}
    {out : TransactionOutput} (h : runTransaction Meter env block included tx = .ok out) :
    4 * logsWeight out.logs.toList ≤ tx.gas.toNat + transferAllowance fork := by
  unfold runTransaction at h
  obtain ⟨target, htarget, h⟩ := bind_ok_iff.mp h
  obtain ⟨bought, hbought, h⟩ := bind_ok_iff.mp h
  obtain ⟨message, hmessage, h⟩ := bind_ok_iff.mp h
  obtain ⟨output, houtput, h⟩ := bind_ok_iff.mp h
  obtain ⟨⟨settled, gasUsed⟩, hsettle, h⟩ := bind_ok_iff.mp h
  obtain ⟨deleted, hdeleted, h⟩ := bind_ok_iff.mp h
  cases h
  have hbound := processMessageCall_logsWeight hcommit rfl houtput
  have hgas := gas_transactionMessage hmessage
  have hadd := allocateGas_add fork tx included.intrinsicGas
  dsimp only at hbound ⊢
  omega

/-- A transaction that runs writes logs of at most a quarter of its gas limit, and one transfer log.

That holds whether or not its message ends with an error. -/
theorem processTransaction_logsWeight {env : BlockEnvironment fork} {block : State.BlockState}
    {included : Included} {out : TransactionOutput}
    (h : processTransaction env block included tx = .ok out) :
    4 * logsWeight out.logs.toList ≤ tx.gas.toNat + transferAllowance fork := by
  by_cases hhegota : .hegota ≤ fork
  · rw [processTransaction_of_hegota_le hhegota] at h
    cases h
  unfold processTransaction at h
  simp only [hhegota, ↓reduceIte] at h
  split at h
  · refine runTransaction_logsWeight (fun meter => ?_) h
    show meter.gasLeft + 0 ≤ meter.gasLeft + meter.spill
    omega
  · exact runTransaction_logsWeight (fun _ => Nat.le_refl _) h

open EthLib.Serialization in
/-- Logs whose weight is below `2^64` join their encodings into at most their weight in bytes. -/
private theorem joinEncodings_logs (logs : List Log) (h : logsWeight logs < 2 ^ 64) :
    ∃ p, Rlp.joinEncodings (logs.map Codec.toItem) = .ok p ∧ p.size ≤ logsWeight logs := by
  induction logs with
  | nil => exact ⟨.empty, rfl, by simp [ByteArray.size]⟩
  | cons l ls ih =>
    have hw : logsWeight (l :: ls) = logWeight l + logsWeight ls := by simp [logsWeight]
    obtain ⟨e, he, hes⟩ := encode_log_size_le l (by omega)
    obtain ⟨p, hp, hps⟩ := ih (by omega)
    refine ⟨e ++ p, ?_, ?_⟩
    · rw [List.map_cons, Rlp.joinEncodings_cons]
      simp only [Codec.encode] at he
      simp [he, hp, bind, Except.bind, pure, Except.pure]
    · simp only [ByteArray.size_append]
      omega

open EthLib.Serialization in
/-- A byte string of at most `n` bytes, with `n` below 56, encodes to at most `n + 1` bytes. -/
private theorem encode_bytes_short (d : ByteArray) (n : Nat) (hd : d.size ≤ n) (hn : n < 56) :
    ∃ e, Rlp.encode (.bytes d) = .ok e ∧ e.size ≤ n + 1 := by
  obtain ⟨e, he⟩ := (Rlp.encode_bytes_succeeds_iff d).mpr (by omega)
  have := (Rlp.encode_bytes_size_le d e he).2 (by omega)
  exact ⟨e, he, by omega⟩

open EthLib.Serialization EthLib.Execution.Blocks in
/-- A receipt encodes when its cumulative gas is below `2^64` and its logs weigh at most `2^63`. -/
theorem encode_makeReceipt (outcome : Outcome fork) (cumulativeGasUsed : Nat) (logs : List Log)
    (hgas : cumulativeGasUsed < 2 ^ 64) (hlogs : logsWeight logs ≤ 2 ^ 63) (type : UInt8) :
    ∃ e, encodeReceipt type (makeReceipt outcome cumulativeGasUsed logs) = .ok e := by
  -- The logs.
  obtain ⟨pl, hpl, hpls⟩ := joinEncodings_logs logs (by omega)
  obtain ⟨el, hel⟩ := (Rlp.encode_list_succeeds_iff _ pl hpl).mpr (by omega)
  have hels := Rlp.encode_list_size_le _ pl el hpl hel
  -- The outcome: a hash of 32 bytes, or a status of at most 1 byte.
  obtain ⟨eo, heo, heos⟩ : ∃ e, Rlp.encode (Codec.toItem outcome) = .ok e ∧ e.size ≤ 33 := by
    cases outcome with
    | postState _ root =>
      exact encode_bytes_short ⟨root.toArray⟩ 32 (by simp [ByteArray.size]) (by omega)
    | status _ b =>
      have := Rlp.bigEndian_size_le b.toNat 1 (by cases b <;> decide)
      obtain ⟨e, he, hs⟩ := encode_bytes_short (Rlp.bigEndian b.toNat) 1 this (by omega)
      exact ⟨e, he, by omega⟩
  -- The gas, of at most 8 bytes.
  obtain ⟨eg, heg, hegs⟩ := encode_bytes_short (Rlp.bigEndian cumulativeGasUsed) 8
    (Rlp.bigEndian_size_le _ 8 (by simpa using hgas)) (by omega)
  -- The bloom, of 256 bytes.
  obtain ⟨eb, heb⟩ := (Rlp.encode_bytes_succeeds_iff ⟨(logsBloom logs).toArray⟩).mpr
    (by simp [ByteArray.size])
  have hebs := (Rlp.encode_bytes_size_le _ eb heb).1
  have hbs : (ByteArray.mk (logsBloom logs).toArray).size = 256 := by
    simp [ByteArray.size]
  -- The payload of the receipt, then the receipt.
  have hJoin : Rlp.joinEncodings [Codec.toItem outcome, Codec.toItem cumulativeGasUsed,
      Codec.toItem (logsBloom logs), Codec.toItem logs] =
      .ok (eo ++ (eg ++ (eb ++ (el ++ .empty)))) := by
    have hg : Codec.toItem cumulativeGasUsed = Rlp.Item.bytes (Rlp.bigEndian cumulativeGasUsed) :=
      rfl
    have hb : Codec.toItem (logsBloom logs) =
        Rlp.Item.bytes ⟨(logsBloom logs).toArray⟩ := rfl
    have hl : Codec.toItem logs = Rlp.Item.list (logs.map Codec.toItem) := rfl
    rw [hg, hb, hl]
    simp only [Rlp.joinEncodings_cons, heo, heg, heb, hel, bind, Except.bind, pure, Except.pure]
    rfl
  obtain ⟨e, he⟩ := (Rlp.encode_list_succeeds_iff _ _ hJoin).mpr (by
    simp only [ByteArray.size_append]
    have : (ByteArray.empty).size = 0 := rfl
    omega)
  have hr : Codec.encode (makeReceipt outcome cumulativeGasUsed logs) = .ok e := he
  unfold encodeReceipt
  split
  · exact ⟨e, hr⟩
  · exact ⟨_, by rw [hr]; rfl⟩

/-- The receipt of a transaction that runs encodes.

Its gas limit and the cumulative gas that the receipt records must be below `2^64`.

So this receipt never fails to encode for a payload too long.

From Hegotá no transaction runs yet, so the claim is empty there. -/
theorem encode_makeReceipt_processTransaction {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} {out : TransactionOutput}
    (h : processTransaction env block included tx = .ok out) (hgas : tx.gas.toNat < 2 ^ 64)
    (outcome : Outcome fork) (cumulativeGasUsed : Nat) (hcum : cumulativeGasUsed < 2 ^ 64)
    (type : UInt8) :
    ∃ e, encodeReceipt type (makeReceipt outcome cumulativeGasUsed out.logs.toList) = .ok e :=
  encode_makeReceipt outcome cumulativeGasUsed out.logs.toList hcum
    (by
      have := processTransaction_logsWeight h
      have : transferAllowance fork ≤ 716 := by unfold transferAllowance; split <;> omega
      omega)
    type

end EthLib.Execution.Transactions
