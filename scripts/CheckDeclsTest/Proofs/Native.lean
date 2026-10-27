/-!
# `CheckDeclsTest.Proofs.Native`

A proof module: its `native_decide` is a finding, which a baseline may allow.
-/

namespace CheckDeclsTest.Proofs.Native

/-- A known answer the compiled code decides. -/
theorem big : 2 ^ 20 = 1048576 := by native_decide

end CheckDeclsTest.Proofs.Native
