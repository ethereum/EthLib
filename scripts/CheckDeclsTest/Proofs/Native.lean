module

/-!
# `CheckDeclsTest.Proofs.Native`

A proof module: its `native_decide` is a finding, which a baseline may allow.
-/

@[expose] public section

namespace CheckDeclsTest.Proofs.Native

/-- A known answer the compiled code decides. -/
-- Keep the private owner distinct from the public native theorem in `Bad`.
private theorem big : 2 ^ 20 = 1048576 := by native_decide

end CheckDeclsTest.Proofs.Native
