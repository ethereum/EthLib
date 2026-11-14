module

public import EthLib.Engine.TransitionConfiguration
public import EthLib.Engine.Proofs.Json
public import EthLib.Consensus.ForkChoice.Handlers

/-!
# Proofs: `engine_exchangeTransitionConfigurationV1`

A configuration reads back from its JSON.

A JSON value reads as a configuration exactly when it holds the three members in canonical form.

The block hash is then in lowercase hex, and the two numbers have no leading zeros.

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

/-- A JSON value reads as a configuration exactly when it is an object of the form below.

A member whose value is `null` counts as absent.

Its other members are `terminalTotalDifficulty`, `terminalBlockHash` and `terminalBlockNumber`.

Each of the three occurs once, and no other member occurs.

The total difficulty is `0x` and its lowercase hex digits without leading zeros.

So is the block number.

The block hash is `0x` and 64 lowercase hex digits, two for each of its 32 bytes. -/
theorem transitionConfigurationOfJson_eq_ok_iff {j : Lean.Json} {c : TransitionConfiguration} :
    transitionConfigurationOfJson j = .ok c ↔
      ∃ fs, fields "transitionConfiguration" j = .ok fs ∧
        hasExactly fs ["terminalTotalDifficulty", "terminalBlockHash", "terminalBlockNumber"] =
          true ∧
        fs.lookup "terminalTotalDifficulty" = some (quantityJson c.terminalTotalDifficulty.toNat) ∧
        fs.lookup "terminalBlockHash" = some (.str (hexString c.terminalBlockHash.toList)) ∧
        fs.lookup "terminalBlockNumber" = some (quantityJson c.terminalBlockNumber.toNat) := by
  unfold transitionConfigurationOfJson transitionConfigurationFields
  simp only [bind_ok_iff, Json.liftM_eq_ok_iff]
  refine exists_congr fun fs => and_congr_right fun _ => ?_
  by_cases hex : hasExactly fs
      ["terminalTotalDifficulty", "terminalBlockHash", "terminalBlockNumber"] = true
  · rw [and_iff_right hex]
    simp only [hex, ↓reduceIte, bind_ok_iff, Json.liftM_eq_ok_iff, field_eq_ok_iff,
      quantity_eq_ok_iff, fixed_false_eq_ok_iff, uint64_eq_ok_iff_quantityJson, pure, Except.pure,
      Except.ok.injEq]
    obtain ⟨t, h, n⟩ := c
    constructor
    · rintro ⟨_, ht, v, ⟨hv, rfl⟩, _, hh, h, rfl, _, hn, n, rfl, he⟩
      simp only [TransitionConfiguration.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
      exact ⟨ht, hh, hn⟩
    · rintro ⟨ht, hh, hn⟩
      exact ⟨_, ht, t.toNat, ⟨t.isLt, rfl⟩, _, hh, h, rfl, _, hn, n, rfl,
        by simp⟩
  -- Any other set of members fails with an invalid parameter, never with a configuration.
  · simp only [hex, Bool.false_eq_true, ↓reduceIte]
    simp [bind, Except.bind]

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
