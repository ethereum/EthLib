module

-- The equation below restates the body of `String.compare`.
import all Init.Data.Ord.String

/-!
# `Base.Proofs.Toolchain.OrdString`

The equation of the order on strings, from `Init.Data.Ord.String` of Lean.

Lean states no lemma that links `compare` on strings to `<` on strings.

This module reads the body of `String.compare` and states it as a public theorem.

Other proofs cite this theorem, so a Lean release that changes the body breaks this file only.
-/

@[expose] public section

namespace EthLib.Base.Toolchain.String

/-- Strings compare by their lexicographic order `<`. -/
theorem compare_eq (s t : String) : compare s t = compareOfLessAndEq s t := by
  show String.compare s t = _
  unfold String.compare; rfl

end EthLib.Base.Toolchain.String
