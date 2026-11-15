module

-- The equation below restates the body of `Nat.digitChar`.
import all Init.Data.Repr

/-!
# `Base.Proofs.Toolchain.Repr`

The equation of the digit that Lean writes for a number, from `Init.Data.Repr` of Lean.

Lean does not expose the body of `Nat.digitChar`, so `decide` cannot evaluate it.

This module reads its body and states it as one public theorem, which `decide` can then evaluate.

Other proofs cite this theorem, so a Lean release that changes the body breaks this file only.
-/

@[expose] public section

namespace EthLib.Base.Toolchain

/-- The digit of a number below sixteen is `0` to `9` or `a` to `f`, and `*` for any other number.
-/
theorem digitChar_eq (n : Nat) :
    n.digitChar =
      if n = 0 then '0' else if n = 1 then '1' else if n = 2 then '2' else
      if n = 3 then '3' else if n = 4 then '4' else if n = 5 then '5' else
      if n = 6 then '6' else if n = 7 then '7' else if n = 8 then '8' else
      if n = 9 then '9' else if n = 0xa then 'a' else if n = 0xb then 'b' else
      if n = 0xc then 'c' else if n = 0xd then 'd' else if n = 0xe then 'e' else
      if n = 0xf then 'f' else '*' := by
  unfold Nat.digitChar; rfl

end EthLib.Base.Toolchain
