module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Bytes
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

/-- The input that the counter search hashes at counter `c`.

The message comes first, then `BE_32(c)`, the four big-endian bytes of `c`. -/
def encodeInput (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : HashInput) (c : Nat) : HashInput :=
  tweakableHashInput parameter (.encoding lay tree leaf)
    (message ++ bytesBE 4 (BitVec.ofNat counterBits c))

omit [Params] in
/-- Two counters below `2^32` with the same four big-endian bytes are equal. -/
theorem counter_bytesBE_inj {c c' : Nat} (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32)
    (h : (bytesBE 4 (BitVec.ofNat counterBits c) : HashInput)
        = bytesBE 4 (BitVec.ofNat counterBits c')) : c = c' :=
  ofNat_inj_of_lt hc hc' (bytesBE_injective h)

/-- Two counters below `2^32` with the same input are equal. -/
theorem encodeInput_inj (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : HashInput) {c c' : Nat}
    (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32)
    (h : encodeInput parameter lay tree leaf message c
      = encodeInput parameter lay tree leaf message c') : c = c' := by
  simp only [encodeInput, tweakableHashInput, List.append_assoc] at h
  have hpayload := List.append_cancel_left h
  have hpayload' := List.append_cancel_left hpayload
  exact counter_bytesBE_inj hc hc' (List.append_cancel_left hpayload')

end SphincsSecurity.Completeness
