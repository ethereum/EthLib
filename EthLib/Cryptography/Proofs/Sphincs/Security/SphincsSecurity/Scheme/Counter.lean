module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Search

/-!
# The counter search

The counter search of the one-time signature hashes the layer message and a 32-bit counter.

The counter is part of the hashed bytes, so counters below `2^32` give distinct inputs.

The search tries at most `2^32` counters, so its inputs never repeat.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 10000

namespace SphincsSecurity.Completeness

variable [Params]

open Concrete Seeded

/-- The input that the counter search hashes at counter `c`. -/
def encodeInput (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : HashInput) (c : Nat) : HashInput :=
  tweakableHashInput parameter (.encoding lay tree leaf)
    (message ++ bytesLE 4 (BitVec.ofNat counterBits c))

/-- Two counters below `2^32` with the same input are equal. -/
theorem encodeInput_inj (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : HashInput) {c c' : Nat}
    (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32)
    (h : encodeInput parameter lay tree leaf message c
      = encodeInput parameter lay tree leaf message c') : c = c' := by
  simp only [encodeInput, tweakableHashInput, List.append_assoc] at h
  have hpayload := List.append_cancel_left h
  have hpayload' := List.append_cancel_left hpayload
  exact counter_bytes_inj hc hc' (List.append_cancel_left hpayload')

end SphincsSecurity.Completeness
