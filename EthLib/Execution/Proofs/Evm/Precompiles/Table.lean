module

public import EthLib.Execution.Evm.Precompiles.Table

/-!
# Proofs: `Evm.Precompiles.Table`

- The table lists 18 distinct addresses.
- A call runs a precompile exactly when its address is in that list.
- A call that succeeds had at least its price in gas.
- A call with less gas than its price fails.
- Gas above the price changes nothing, so a call that succeeds uses exactly its price.
- Each precompile has its own error code, and no code is 0.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles

/-- There are 18 precompiles, at distinct addresses. -/
theorem addresses_length : ADDRESSES.length = 18 ∧ ADDRESSES.Nodup := by
  decide

/-- A call runs a precompile exactly when its address is one of the 18. -/
theorem run_isSome_iff (address : Nat) (data : ByteArray) (gas : Nat) :
    (run address data gas).isSome ↔ address ∈ ADDRESSES := by
  unfold run
  split <;> simp_all [ADDRESSES]

/-- The precompiles with a price are exactly the precompiles of the table. -/
theorem price_isSome_iff (address : Nat) (data : ByteArray) :
    (price address data).isSome ↔ address ∈ ADDRESSES := by
  unfold price
  split <;> simp_all [ADDRESSES]

/-- Unfold the call of every precompile of the table. -/
local macro "unfold_calls" : tactic => `(tactic| simp only [run, Option.some.injEq,
  Ecrecover.ecrecover, Sha256.sha256, Ripemd160.call, Identity.identity, Modexp.modexp,
  AltBn128.ecadd, AltBn128.ecmul, AltBn128.ecpairing, Blake2f.call,
  PointEvaluation.pointEvaluation, Bls12381.bls12G1Add, Bls12381.bls12G1Msm,
  Bls12381.bls12G2Add, Bls12381.bls12G2Msm, Bls12381.bls12Pairing, Bls12381.bls12MapFpToG1,
  Bls12381.bls12MapFp2ToG2, P256Verify.p256Verify] at *)

/-- Gas above the price changes nothing: the call gives what it gives with exactly its price. -/
theorem run_of_price_le {address : Nat} {data : ByteArray} {cost gas : Nat}
    (hprice : price address data = some cost) (enough : cost ≤ gas) :
    run address data gas = run address data cost := by
  have hlt : ¬gas < cost := Nat.not_lt.mpr enough
  unfold price at hprice
  split at hprice <;> cases hprice <;> unfold_calls <;> simp [hlt]

/-- A call with less gas than its price fails.

The error can come from a check of the call data before the charge. -/
theorem run_outOfGas {address : Nat} {data : ByteArray} {cost gas : Nat}
    (hprice : price address data = some cost) (short : gas < cost) :
    ∃ e, run address data gas = some (.error e) := by
  unfold price at hprice
  split at hprice <;> cases hprice <;> unfold_calls <;>
    simp [short, Except.mapError, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] <;>
    split <;> simp <;> split at * <;> simp_all

/-- A call that succeeds had at least its price in gas. -/
theorem run_ok_price {address : Nat} {data : ByteArray} {gas : Nat} {out : ByteArray}
    (hrun : run address data gas = some (.ok out)) :
    ∃ cost, price address data = some cost ∧ cost ≤ gas := by
  -- The address has a precompile, so it has a price.
  have hmem := (run_isSome_iff address data gas).mp (by simp [hrun])
  obtain ⟨cost, hcost⟩ := Option.isSome_iff_exists.mp ((price_isSome_iff address data).mpr hmem)
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
