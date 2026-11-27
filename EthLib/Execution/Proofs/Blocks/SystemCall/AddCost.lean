module

public import EthLib.Execution.Proofs.Blocks.SystemCall.FeePath
public import EthLib.Execution.Proofs.Blocks.SystemCall.AddPath
public import EthLib.Execution.Proofs.Evm.Logic.Cost

/-!
# Proofs: the gas that a call adding a request spends

A call that pays the fee of a request contract adds its request.

The fee path and the add path each bound the gas they spend, and the bounds add up.
-/

@[expose] public section

namespace EthLib.Execution.Blocks.RequestQueue

open EthLib.Base (Fork U256)
open EthLib.Execution.Evm EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Blocks.SystemContract

namespace RequestContract

variable (c : RequestContract) {fork : Fork} {message : Message fork} {gas : Nat}
  {state : TransactionState} {substate : Substate} {returnData : ByteArray}

/-- From Shapella, a call that pays the fee adds its request, within a bound on the gas.

The bound is the fee path, for a loop of `m` steps, then the reads and writes of the storage. -/
theorem costs_add {system revert n m : Nat}
    (hfee : FeePathCode c.code system c.feeFraction revert c.inputSize)
    (hadd : AddPathCode c.code n c.inputSize)
    -- The loop of the code fixes the fee at an excess of 0 to 1 wei.
    (hmin : c.minFee = 1) (hfork : .shapella ≤ fork)
    (hcaller : message.caller ≠ SYSTEM_ADDRESS) (hstatic : message.isStatic = false)
    -- The account of the contract exists, and the input has the size of a request.
    (hacc : (state.getAccountOptional message.currentTarget).isSome = true)
    (hsize : message.data.size = c.inputSize)
    -- The loop of the fee stops within `m` steps with no overflow, unless the inhibitor holds.
    (hfits : storageOf state message.currentTarget 0 ≠ EXCESS_INHIBITOR →
      FeeFits c.minFee c.feeFraction (storageOf state message.currentTarget 0).toNat m)
    -- The value pays the fee.
    (hpays : c.pays (storageOf state message.currentTarget) message.value = true)
    -- The frame starts with at least the gas of the bound.
    (hgas : 2266 + 87 * m + 25000 * storageGasScale fork * (n + 4) ≤ gas) :
    -- From Glamsterdam, this one-counter frame is a model for the proof, not the meter of EIP-8037.
    Costs (Step fork) (At c.code message 0 [] .empty gas state substate returnData)
      (fun evm => evm.running = false ∧
        Added (n + 1) message.currentTarget (requestWordsOf n message.caller message.data)
          (requestLog message.caller message.data) state substate evm)
      (2266 + 87 * m + 25000 * storageGasScale fork * (n + 4)) := by
  -- The storage part of the bound, as one term for `omega`.
  generalize hK : 25000 * storageGasScale fork * (n + 4) = K at hgas ⊢
  have hspec := c.spec_pay (m := m) (returnData := returnData) (P := fun evm =>
      Added (n + 1) message.currentTarget (requestWordsOf n message.caller message.data)
        (requestLog message.caller message.data) state substate evm ∧
      gas ≤ evm.gas + (2266 + 87 * m + K)) hfee hmin hfork hcaller hsize hfits (by omega)
    fun _ g ss (hg : gas - (2266 + 87 * m) ≤ g) hlogs => by
      refine Spec.consequence (hadd.spec_add
        (S := state.recordStorageRead message.currentTarget (U256.toBeBytes 0)) hfork
        hstatic hacc hsize (by rw [hK]; omega)) (fun _ h => h) ?_
      rintro evm ⟨⟨herr, hout, hw, hlog⟩, hg'⟩
      refine ⟨⟨herr, hout, hw, by rw [hlog, hlogs]⟩, ?_⟩
      rw [hK] at hg'
      omega
  refine Costs.consequence (Costs.of_triple hspec fun a b ha hb => ?_) (fun _ h => h)
    fun evm ⟨hs, hq⟩ => ?_
  · simp only [hpays, ↓reduceIte] at hb
    rw [ha.2.2.2.2.2.2.1]
    exact hb.2.2
  · simp only [hpays, ↓reduceIte] at hq
    exact ⟨hs, hq.1⟩

end RequestContract

end EthLib.Execution.Blocks.RequestQueue
