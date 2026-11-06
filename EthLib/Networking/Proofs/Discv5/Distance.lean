module

public import EthLib.Networking.Proofs.Discv5.Identity

/-!
# `Networking.Proofs.Discv5.Distance`

The logarithmic distance of discv5 is an ultrametric.

- A distance is below `2^k` exactly when the logarithmic distance is at most `k`.
- The distances from `a` to `b` and from `b` to `c` XOR to the distance from `a` to `c`.
- The logarithmic distance from `a` to `c` is at most the larger of the two through `b`.
- When the one from `a` to `b` is smaller, the one from `a` to `c` is the one from `b` to `c`.

"Node Table" of `discv5-theory.md` groups the nodes of a table by their logarithmic distance:

<https://github.com/ethereum/devp2p/blob/88f1c80800d6/discv5/discv5-theory.md#node-table>
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Discv5.Distance

open EthLib.Networking.Discv5
open EthLib.Networking.Proofs.Discv5.Identity

/-- A distance is below `2^k` exactly when the logarithmic distance is at most `k`.

So the logarithmic distance is the number of bits of the distance. -/
theorem distance_lt_two_pow_iff {a b : NodeId} {k : Nat} :
    distance a b < 2 ^ k ↔ logDistance a b ≤ k := by
  simp only [logDistance]
  split
  · rename_i hzero
    simp only [hzero, Nat.zero_le, iff_true]
    exact Nat.two_pow_pos k
  · rw [← Nat.log2_lt ‹_›]
    omega

/-- The distances from `a` to `b` and from `b` to `c` XOR to the distance from `a` to `c`. -/
theorem distance_xor_distance (a b c : NodeId) :
    distance a b ^^^ distance b c = distance a c := by
  -- The value of `b` appears twice, and cancels.
  simp only [distance, Nat.xor_assoc, ← Nat.xor_assoc (Base.bytesToNat b.toList), Nat.xor_self,
    Nat.zero_xor]

/-- The logarithmic distance is an ultrametric.

The distance from `a` to `c` is at most the larger of the two through `b`. -/
theorem logDistance_le_max (a b c : NodeId) :
    logDistance a c ≤ max (logDistance a b) (logDistance b c) := by
  rw [← distance_lt_two_pow_iff, ← distance_xor_distance a b c]
  exact Nat.xor_lt_two_pow (distance_lt_two_pow_iff.mpr (Nat.le_max_left _ _))
    (distance_lt_two_pow_iff.mpr (Nat.le_max_right _ _))

/-- When `b` is nearer to `a` than to `c`, the distance from `a` to `c` is that from `b` to `c`. -/
theorem logDistance_eq_of_lt {a b c : NodeId} (h : logDistance a b < logDistance b c) :
    logDistance a c = logDistance b c := by
  have hac := logDistance_le_max a b c
  -- The distance from `b` to `c` goes through `a` too.
  have hbc := logDistance_le_max b a c
  rw [logDistance_comm b a] at hbc
  omega

end EthLib.Networking.Proofs.Discv5.Distance
