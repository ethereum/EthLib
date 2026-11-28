module

public import EthLib.Execution.Proofs.Evm.OpTables.Parts
public import EthLib.Execution.Proofs.Evm.Gas.Prices
public import EthLib.Execution.Proofs.Evm.Call.Reads

/-!
# Proofs: the instructions that read accounts, use storage, log and self-destruct follow the tables

Each one takes and leaves the words of its tables, and pays its constant price.

SSTORE and SELFDESTRUCT may instead halt once they have read the state, with their words taken.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]

/-! ## Other accounts -/

/-- BALANCE takes a word, leaves one and pays at least its price. -/
theorem balanceStep_moves {evm after : Evm fork Meter} (h : balanceStep evm = .ok after) :
    Moves 1 1 (balanceCost fork false) evm after := by
  obtain ⟨⟨word, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ((((((popWord_moves h1).trans (accessAddress_moves _ _)).trans (chargeGas_moves h2)).trans
    (recordAccountRead_moves _ _)).trans (pushWord_moves h3)).trans (advance_moves _ _)).weaken
    (hp := by simp only [Nat.add_zero, Nat.zero_add]; exact balanceCost_le _ _)

/-- EXTCODESIZE takes a word, leaves one and pays at least its price. -/
theorem extcodesizeStep_moves {evm after : Evm fork Meter} (h : extcodesizeStep evm = .ok after) :
    Moves 1 1 (externalBaseCost fork false) evm after := by
  obtain ⟨⟨word, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ((((((popWord_moves h1).trans (accessAddress_moves _ _)).trans (chargeGas_moves h2)).trans
    (recordAccountRead_moves _ _)).trans (pushWord_moves h3)).trans (advance_moves _ _)).weaken
    (hp := by simp only [Nat.add_zero, Nat.zero_add]; exact externalBaseCost_le _ _)

/-- EXTCODECOPY takes four words and pays at least its price. -/
theorem extcodecopyStep_moves {evm after : Evm fork Meter} (h : extcodecopyStep evm = .ok after) :
    Moves 4 0 (externalBaseCost fork false) evm after := by
  obtain ⟨⟨word, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h5, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ((((((((popWord_moves h1).trans (popWord_moves h2)).trans (popWord_moves h3)).trans
    (popWord_moves h4)).trans (accessAddress_moves _ _)).trans
    (chargeGasAndMemory_moves h5)).trans
    (recordAccountRead_moves _ (Base.toAddressMasked word))).weaken (t' := 4)
    (l' := 0) (p' := externalBaseCost fork false) (hp := by
      simp only [Nat.add_zero, Nat.zero_add]
      exact Nat.le_trans (externalBaseCost_le _ _) (Nat.le_add_right _ _))).keep rfl rfl rfl rfl

/-- EXTCODEHASH takes a word, leaves one and pays at least its price. -/
theorem extcodehashStep_moves {evm after : Evm fork Meter} (h : extcodehashStep evm = .ok after) :
    Moves 1 1 (extcodehashCost fork false) evm after := by
  obtain ⟨⟨word, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ((((((popWord_moves h1).trans (accessAddress_moves _ _)).trans (chargeGas_moves h2)).trans
    (recordAccountRead_moves _ _)).trans (pushWord_moves h3)).trans (advance_moves _ _)).weaken
    (hp := by simp only [Nat.add_zero, Nat.zero_add]; exact extcodehashCost_le _ _)

/-- Each instruction that reads another account follows the tables. -/
theorem accountStep_moves {op : Op} {f : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {evm after : Evm fork Meter} {takes leaves : Nat} {immediate : UInt8}
    (hf : accountStep fork op = some f) (hw : op.stackWords immediate = some (takes, leaves))
    (h : f evm = .ok after) : Moves takes leaves (op.constantGas fork) evm after := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hf <;>
    simp only [Op.stackWords, Option.some.injEq, Prod.mk.injEq] at hw <;> obtain ⟨rfl, rfl⟩ := hw
  all_goals (repeat' split at hf) <;> (try simp only [Option.some.injEq] at hf) <;> (try subst hf)
  all_goals first
    | cases hf
    | exact balanceStep_moves h
    | exact extcodesizeStep_moves h
    | exact extcodecopyStep_moves h
    | exact extcodehashStep_moves h
    | exact ((recordAccountRead_moves _ _).trans (readFrame_moves h)).weaken (hp := Nat.le_refl _)

/-! ## Storage -/

/-- SSTORE costs at least its constant price, at every fork. -/
theorem constantGas_sstore_le (fork : Fork) (original current new : U256) (cold : Bool) :
    Op.constantGas fork .sstore ≤ sstoreCost fork original current new cold := by
  unfold Op.constantGas sstoreCost sstoreReadCost sstoreResetCost
  dsimp only [gasSchedule, sloadCost]
  cases fork <;> simp (config := { decide := true }) only [ite_true, ite_false]
  all_goals repeat' split
  all_goals decide

/-- SLOAD takes a word, leaves one and pays at least its price. -/
theorem sloadStep_moves {evm after : Evm fork Meter} (h : sloadStep evm = .ok after) :
    Moves 1 1 (sloadCost fork false) evm after := by
  obtain ⟨⟨word, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ((((((popWord_moves h1).trans (accessStorageKey_moves _ _ _)).trans
    (chargeGas_moves h2)).trans (recordStorageRead_moves _ _ _)).trans (pushWord_moves h3)).trans
    (advance_moves _ _)).weaken
    (hp := by simp only [Nat.add_zero, Nat.zero_add]; exact sloadCost_le _ _)

/-- SSTORE takes two words and pays at least its price, or halts once it has read the slot. -/
theorem sstoreStep_follows {evm after : Evm fork Meter} (h : sstoreStep evm = .ok after) :
    FollowsTables 2 0 (Op.constantGas fork .sstore) evm after := by
  unfold sstoreStep at h
  split at h
  · cases h
  obtain ⟨⟨word, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨new, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · cases h
  have m := (((popWord_moves h1).trans (popWord_moves h2)).trans
    (accessStorageKey_moves e2 e2.message.currentTarget (U256.toBeBytes word))).trans
    (recordStorageRead_moves _ e2.message.currentTarget (U256.toBeBytes word))
  rcases keepReads_eq_ok_halt h with h | ⟨e, -, he, rfl⟩
  · obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · cases h
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    refine (((((m.trans (refillStateGas_moves _ _)).trans (chargeGas_moves h3)).trans
      (chargeStateGas_moves h4)).weaken (t' := 2) (l' := 0) (p' := Op.constantGas fork .sstore)
      (hp := ?_)).follows rfl rfl rfl rfl)
    simp only [Nat.add_zero, Nat.zero_add]
    exact constantGas_sstore_le _ _ _ _ _
  · exact .halt m (Nat.le_refl _) he

/-! ## Transient storage -/

/-- TLOAD takes a word, leaves one and pays at least its price. -/
theorem tloadStep_moves {evm after : Evm fork Meter} (h : tloadStep evm = .ok after) :
    Moves 1 1 OPCODE_TLOAD evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ((((popWord_moves h1).trans (chargeGas_moves h2)).trans (pushWord_moves h3)).trans
    (advance_moves _ _)).weaken

/-- TSTORE takes two words and pays at least its price. -/
theorem tstoreStep_moves {evm after : Evm fork Meter} (h : tstoreStep evm = .ok after) :
    Moves 2 0 OPCODE_TSTORE evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · cases h
  · cases h
    exact ((((popWord_moves h1).trans (popWord_moves h2)).trans (chargeGas_moves h3)).weaken
      (t' := 2) (l' := 0) (p' := OPCODE_TSTORE)).keep rfl rfl rfl rfl

/-! ## Logs -/

omit [LawfulGasMeter Meter] in
/-- The pops of the topics of a log take one word for each topic. -/
theorem popTopics_moves {evm after : Evm fork Meter} {n : Nat} {topics : List EthLib.Base.Hash32}
    (h : popTopics evm n = .ok (topics, after)) : Moves n 0 0 evm after := by
  induction n generalizing evm topics with
  | zero =>
    cases h
    exact .refl _
  | succ k ih =>
    obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact ((popWord_moves h1).trans (ih h2)).weaken

/-- LOGn takes its words and pays at least its price. -/
theorem logStep_moves {n : Nat} {evm after : Evm fork Meter} (h : logStep n evm = .ok after) :
    Moves (n + 2) 0 (OPCODE_LOG_BASE + OPCODE_LOG_TOPIC * n) evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, _⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h4, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · cases h
  · cases h
    exact ((((((popWord_moves h1).trans (popWord_moves h2)).trans (popTopics_moves h3)).trans
      (chargeGasAndMemory_moves h4)).weaken (t' := n + 2) (l' := 0)
      (p' := OPCODE_LOG_BASE + OPCODE_LOG_TOPIC * n) (hp := by simp only [logCost]; omega))).keep
      rfl rfl rfl rfl

/-! ## SELFDESTRUCT -/

/-- SELFDESTRUCT takes a word and pays at least its price, or halts once it has read the state. -/
theorem selfdestructStep_follows {evm after : Evm fork Meter}
    (h : selfdestructStep fork evm = .ok after) :
    FollowsTables 1 0 (gasSchedule fork).OPCODE_SELFDESTRUCT_BASE evm after := by
  unfold selfdestructStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨word, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  have m := ((popWord_moves h1).trans (accessAddress_moves e1 (Base.toAddressMasked word))).trans
    (recordAccountRead_moves _ (Base.toAddressMasked word))
  rcases keepReads_eq_ok_halt h with h | ⟨e, -, he, rfl⟩
  · obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    unfold finishSelfdestruct at h
    split at h
    · cases h
    · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact ((((m.trans (chargeGas_moves h2)).trans (chargeStateGas_moves h3)).weaken (t' := 1)
        (l' := 0) (p' := (gasSchedule fork).OPCODE_SELFDESTRUCT_BASE)
        (hp := by simp only [selfdestructCost]; omega)).follows rfl rfl rfl rfl)
  · exact .halt m (Nat.le_refl _) he

end EthLib.Execution.Evm
