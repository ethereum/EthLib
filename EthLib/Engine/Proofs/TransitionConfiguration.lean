module

public import EthLib.Engine.TransitionConfiguration
public import EthLib.Engine.Proofs.Json
public import EthLib.Consensus.ForkChoice.Handlers

/-!
# Proofs: `engine_exchangeTransitionConfigurationV1`

A configuration reads back from its JSON.

The method succeeds exactly when the request holds one parameter that decodes as a configuration.

It then answers the configuration of the execution node, whatever configuration the request holds.

So the request that a consensus node writes always gets that answer.

The undecided terminal total difficulty is `2^256 - 2^10`, the value of the minimal configuration.

The terminal block check of the execution layer is that of the consensus layer.

Both must hold the same terminal total difficulty.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Serialization.JsonRpc

/-- A configuration reads back from its JSON. -/
theorem transitionConfigurationOfJson_json (c : TransitionConfiguration) :
    transitionConfigurationOfJson (transitionConfigurationJson c) = .ok c := by
  have hd : [("terminalTotalDifficulty", quantityJson c.terminalTotalDifficulty.toNat),
      ("terminalBlockHash", dataJson c.terminalBlockHash.toList),
      ("terminalBlockNumber", quantityJson c.terminalBlockNumber.toNat)].Pairwise
      fun a b => a.1 ≠ b.1 := by simp
  obtain ⟨fs, hfs, hp⟩ := fields_mkObj "transitionConfiguration" hd
    (by simp [quantityJson, dataJson, isNull_str])
  have hex : hasExactly fs transitionConfigurationFields = true := hasExactly_of_perm hp
  have r1 := field_of_perm (what := "transitionConfiguration") hp hd (List.mem_cons_self ..)
  have r2 := field_of_perm (what := "transitionConfiguration") hp hd
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have r3 := field_of_perm (what := "transitionConfiguration") hp hd
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  unfold transitionConfigurationOfJson transitionConfigurationJson
  simp only [hfs, hex, r1, r2, r3, quantity_toDigits _ c.terminalTotalDifficulty.isLt,
    fixed_dataJson, uint64_toDigits, Json.liftM_ok, bind, Except.bind, ite_true, pure,
    Except.pure, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The method succeeds exactly on one parameter that decodes, and then answers its own values.
-/
theorem exchangeTransitionConfiguration_eq_ok_iff {own r : TransitionConfiguration}
    {params : Lean.Json} :
    exchangeTransitionConfiguration own params = .ok r ↔
      r = own ∧ ∃ j c, params = .arr #[j] ∧ transitionConfigurationOfJson j = .ok c := by
  unfold exchangeTransitionConfiguration
  constructor
  · intro h
    cases params with
    | arr items =>
      simp only [paramsArray, bind, Except.bind, pure, Except.pure] at h
      match hi : items.toList, h with
      | [j], h =>
        simp only [Json.liftM_ok] at h
        rcases hj : transitionConfigurationOfJson j with e | c
        · simp [hj] at h
        · simp only [hj, Except.ok.injEq] at h
          refine ⟨h.symm, j, c, ?_, hj⟩
          congr 1
          exact Array.toList_inj.mp hi
      | [], h => simp [Json.liftM_ok, Json.invalid_eq] at h
      | _ :: _ :: _, h => simp [Json.liftM_ok, Json.invalid_eq] at h
    | _ => simp [paramsArray, bind, Except.bind] at h
  · rintro ⟨rfl, j, c, rfl, hj⟩
    simp [paramsArray, hj, bind, Except.bind, pure, Except.pure]

/-- The request that a consensus node writes gets the configuration of the execution node. -/
theorem exchangeTransitionConfiguration_paramsJson (own c : TransitionConfiguration) :
    exchangeTransitionConfiguration own (exchangeTransitionConfigurationParamsJson c) = .ok own :=
  exchangeTransitionConfiguration_eq_ok_iff.mpr
    ⟨rfl, _, c, rfl, transitionConfigurationOfJson_json c⟩

/-- The undecided terminal total difficulty is `2^256 - 2^10`. -/
theorem toNat_UNDECIDED_TERMINAL_TOTAL_DIFFICULTY :
    UNDECIDED_TERMINAL_TOTAL_DIFFICULTY.toNat = 2 ^ 256 - 2 ^ 10 := by
  decide

/-- The minimal configuration of the consensus layer sets the undecided total difficulty. -/
theorem minimal_terminalTotalDifficulty :
    Consensus.Config.minimal.TERMINAL_TOTAL_DIFFICULTY = UNDECIDED_TERMINAL_TOTAL_DIFFICULTY := by
  decide

/-- The terminal block check of the execution layer agrees with that of the consensus layer.

Both layers must hold the same terminal total difficulty. -/
theorem isTerminalPowBlock_eq_isValidTerminalPowBlock {config : Consensus.Config}
    {t : TransitionConfiguration} {block parent : Consensus.PowBlock}
    (h : t.terminalTotalDifficulty = config.TERMINAL_TOTAL_DIFFICULTY) :
    isTerminalPowBlock t block.totalDifficulty.toNat parent.totalDifficulty.toNat =
      Consensus.isValidTerminalPowBlock config block parent := by
  simp [isTerminalPowBlock, Consensus.isValidTerminalPowBlock, h, BitVec.le_def, BitVec.lt_def]

end EthLib.Engine
