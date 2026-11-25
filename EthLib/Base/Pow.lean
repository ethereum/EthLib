module

/-!
# Square and multiply

The power `a^e` by square and multiply, for any product with a one.
-/

@[expose] public section

namespace EthLib.Base

/-- `a^e` in a monoid, for `e < 2^fuel`, by square and multiply on the bits of `e`, low bit first.

For any other product with a one, it is that sequence of products.

It recurses on `fuel`, so the kernel can run it. -/
@[specialize] def powBits {α : Type} [Mul α] [One α] : Nat → α → Nat → α
  | 0, _, _ => 1
  | fuel + 1, a, e =>
    -- `a^e = a^(e mod 2) * (a^2)^(e / 2)`.
    let half := powBits fuel (a * a) (e / 2)
    if e % 2 = 1 then a * half else half

end EthLib.Base
