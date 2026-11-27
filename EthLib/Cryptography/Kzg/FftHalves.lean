module

/-!
# `FftHalves`

The even and the odd entries of a vector, which each stage of a transform splits.

It imports nothing, so the kernel checks of the trusted setup can run the same split.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

/-- Entries `start`, `start + 2`, `start + 4` and so on of `xs`: the even or the odd entries. -/
def everyOther {α : Type _} {k : Nat} (xs : Vector α (2 ^ (k + 1))) (start : Fin 2) :
    Vector α (2 ^ k) :=
  Vector.ofFn fun i => xs[start.val + 2 * i.val]'(by
    have hi := i.isLt
    have hs := start.isLt
    have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ ..
    omega)

end EthLib.Cryptography.Kzg
