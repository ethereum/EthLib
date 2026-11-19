module

/-!
# `Multilinear.Hypercube`

The order of the points of the hypercube `{0, 1}^k`, as indices into an array of length `2^k`.

No external standard fixes this order, so this file states the rule itself.

A point `u = (u_0, ..., u_(k-1))` is the integer `u_0 * 2^0 + u_1 * 2^1 + ... + u_(k-1) * 2^(k-1)`.

So coordinate `i` is bit `i` of the index, and the first coordinate is the low bit.

A function on the hypercube is the array whose entry `i` is its value at the point of index `i`.

With `k = 3`, the point `(1, 0, 1)` is the index `1 + 0 * 2 + 1 * 4 = 5`.

The index `6 = 0 + 2 + 4` is the point `(0, 1, 1)`.
-/

@[expose] public section

namespace EthLib.Cryptography.Multilinear

/-- The index of a hypercube point: coordinate `i` is bit `i`, the first coordinate the low bit.

It is the first coordinate plus twice the index of the other coordinates.

With `k = 3`, the point `(1, 0, 1)` has the index `5`. -/
def pointIndex : {k : Nat} → Vector Bool k → Fin (2 ^ k)
  | 0, _ => ⟨0, Nat.one_pos⟩
  | k + 1, u =>
    ⟨u[0].toNat + 2 * (pointIndex (k := k) u.tail).val, by
      have hlow := Bool.toNat_le u[0]
      have hrest := (pointIndex (k := k) u.tail).isLt
      rw [Nat.pow_succ]
      omega⟩

/-- The hypercube point of an index: coordinate `i` is bit `i` of the index.

With `k = 3`, the index `6` is the point `(0, 1, 1)`. -/
def indexPoint {k : Nat} (i : Fin (2 ^ k)) : Vector Bool k := Vector.ofFn fun j => i.val.testBit j

end EthLib.Cryptography.Multilinear
