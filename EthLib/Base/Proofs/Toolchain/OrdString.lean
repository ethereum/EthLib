module

/-!
# `Base.Proofs.Toolchain.OrdString`

The equation of the order on strings.

Lean compares strings by their UTF-8 bytes, and states that this comparison is lawful for `<`.

This module derives from that law that `compare` on strings is the lexicographic order `<`.

A Lean release that changes the order on strings breaks this file only.
-/

@[expose] public section

namespace EthLib.Base.Toolchain.String

/-- Strings compare by their lexicographic order `<`. -/
theorem compare_eq (s t : String) : compare s t = compareOfLessAndEq s t :=
  Std.compare_eq_of_lt_iff compareOfLessAndEq_eq_lt.symm
    (compareOfLessAndEq_eq_gt Std.le_antisymm (fun _ _ => Std.le_total) Std.not_le s t).symm

end EthLib.Base.Toolchain.String
