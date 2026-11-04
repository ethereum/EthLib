module

public import EthLib.Execution.Evm.Precompiles.Table

/-!
# Proofs: `Evm.Precompiles.Table`

- The table lists 18 distinct addresses, and each one has the fork that adds it.
- At a fork, a call runs a precompile exactly when the fork has a precompile at its address.
- Before the fork that adds it, an address runs no precompile.
- A call that succeeds had at least its price in gas.
- A call with less gas than its price fails.
- Gas above the price changes nothing, so a call that succeeds uses exactly its price.
- Each precompile has its own error code, and no code is 0.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles

open EthLib.Base (Fork)

/-- There are 18 precompiles, at distinct addresses. -/
theorem addresses_length : ADDRESSES.length = 18 ∧ ADDRESSES.Nodup := by
  decide

/-- An address has a precompile at some fork exactly when it is one of the 18. -/
theorem addedAt_isSome_iff (address : Nat) : (addedAt address).isSome ↔ address ∈ ADDRESSES := by
  unfold addedAt
  split <;> simp_all [ADDRESSES]

/-- From Fusaka, every one of the 18 addresses has a precompile. -/
theorem isPrecompile_of_fusaka_le {fork : Fork} (hfork : fork ≥ .fusaka) {address : Nat}
    (h : address ∈ ADDRESSES) : isPrecompile fork address = true := by
  simp only [ADDRESSES, List.mem_cons, List.not_mem_nil, or_false] at h
  have hle : ∀ f : Fork, f ≤ .fusaka → f ≤ fork := fun f hf => Nat.le_trans hf hfork
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;>
    (simp only [isPrecompile, addedAt, decide_eq_true_eq]; exact hle _ (by decide))

/-- Before the fork that adds it, an address runs no precompile. -/
theorem run_eq_none_of_lt {fork added : Fork} {address : Nat} (h : addedAt address = some added)
    (before : fork < added) (data : ByteArray) (gas : Nat) : run fork address data gas = none := by
  have : isPrecompile fork address = false := by
    simp only [isPrecompile, h, decide_eq_false_iff_not]
    exact fun le => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le before le)
  simp [run, this]

/-- A precompile of a fork has one of the 18 addresses. -/
theorem mem_addresses_of_isPrecompile {fork : Fork} {address : Nat}
    (h : isPrecompile fork address = true) : address ∈ ADDRESSES := by
  rw [← addedAt_isSome_iff]
  unfold isPrecompile at h
  split at h <;> simp_all

/-- A call runs a precompile exactly when the fork has a precompile at its address. -/
theorem run_isSome_iff (fork : Fork) (address : Nat) (data : ByteArray) (gas : Nat) :
    (run fork address data gas).isSome ↔ isPrecompile fork address = true := by
  unfold run
  by_cases h : isPrecompile fork address
  · simp only [h, Bool.not_true, Bool.false_eq_true, ite_false, iff_true]
    -- Every address with a fork is an address of the table, which runs a precompile.
    have hmem := mem_addresses_of_isPrecompile h
    simp only [ADDRESSES, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp [h]

/-- The precompiles with a price are exactly the precompiles of the fork. -/
theorem price_isSome_iff (fork : Fork) (address : Nat) (data : ByteArray) :
    (price fork address data).isSome ↔ isPrecompile fork address = true := by
  unfold price
  by_cases h : isPrecompile fork address
  · simp only [h, Bool.not_true, Bool.false_eq_true, ite_false, iff_true]
    have hmem := mem_addresses_of_isPrecompile h
    simp only [ADDRESSES, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp [h]

/-- Unfold the call of every precompile of the table. -/
local macro "unfold_calls" : tactic => `(tactic| simp only [run, Option.some.injEq,
  Ecrecover.ecrecover, Sha256.sha256, Ripemd160.ripemd160, Identity.identity, Modexp.modexp,
  AltBn128.ecadd, AltBn128.ecmul, AltBn128.ecpairing, Blake2f.blake2f,
  PointEvaluation.pointEvaluation, Bls12381.bls12G1Add, Bls12381.bls12G1Msm,
  Bls12381.bls12G2Add, Bls12381.bls12G2Msm, Bls12381.bls12Pairing, Bls12381.bls12MapFpToG1,
  Bls12381.bls12MapFp2ToG2, P256Verify.p256Verify] at *)

/-- Gas above the price changes nothing: the call gives what it gives with exactly its price. -/
theorem run_of_price_le {fork : Fork} {address : Nat} {data : ByteArray} {cost gas : Nat}
    (hprice : price fork address data = some cost) (enough : cost ≤ gas) :
    run fork address data gas = run fork address data cost := by
  have hlt : ¬gas < cost := Nat.not_lt.mpr enough
  unfold price at hprice
  by_cases h : isPrecompile fork address
  · simp only [h, Bool.not_true, Bool.false_eq_true, ite_false] at hprice
    split at hprice <;> cases hprice <;> unfold_calls <;> simp [h, hlt]
  · simp [h] at hprice

/-- A call with less gas than its price fails.

The error can come from a check of the call data before the charge. -/
theorem run_outOfGas {fork : Fork} {address : Nat} {data : ByteArray} {cost gas : Nat}
    (hprice : price fork address data = some cost) (short : gas < cost) :
    ∃ e, run fork address data gas = some (.error e) := by
  unfold price at hprice
  by_cases h : isPrecompile fork address
  · simp only [h, Bool.not_true, Bool.false_eq_true, ite_false] at hprice
    split at hprice <;> cases hprice <;> unfold_calls <;>
      simp [h, short, Except.mapError, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] <;>
      split <;> simp <;> split at * <;> simp_all
  · simp [h] at hprice

/-- A call that succeeds had at least its price in gas. -/
theorem run_ok_price {fork : Fork} {address : Nat} {data : ByteArray} {gas : Nat}
    {out : ByteArray} (hrun : run fork address data gas = some (.ok out)) :
    ∃ cost, price fork address data = some cost ∧ cost ≤ gas := by
  -- The fork has a precompile at the address, so it has a price.
  have hmem := (run_isSome_iff fork address data gas).mp (by simp [hrun])
  obtain ⟨cost, hcost⟩ :=
    Option.isSome_iff_exists.mp ((price_isSome_iff fork address data).mpr hmem)
  refine ⟨cost, hcost, Nat.not_lt.mp fun short => ?_⟩
  -- Less gas than the price would make the call fail.
  obtain ⟨e, he⟩ := run_outOfGas hcost short
  simp [hrun] at he

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem PrecompileError.code_injective (e₁ e₂ : PrecompileError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [PrecompileError.code] at h; exact absurd h (by decide))

/-- No error has code 0, which a caller can keep for an address with no precompile. -/
theorem PrecompileError.code_ne_zero (e : PrecompileError) : e.code ≠ 0 := by
  cases e <;> simp only [PrecompileError.code] <;> decide

end EthLib.Execution.Evm.Precompiles
