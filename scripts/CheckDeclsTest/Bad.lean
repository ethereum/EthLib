import CheckDeclsForeign

/-!
# `CheckDeclsTest.Bad`

One declaration for each finding the declaration check must report.
-/

namespace CheckDeclsTest.Bad

/-- The kernel sees a `partial` definition as an opaque constant. -/
partial def spin (n : Nat) : Nat := spin (n + 1)

/-- An opaque constant. -/
opaque hidden : Nat

/-- An axiom declaration. -/
axiom assumed : 1 = 2

/-- A theorem that depends on an axiom declared in scope. -/
theorem usesAssumed : 1 = 2 := assumed

/-- An unfinished proof. -/
theorem unfinished : 2 = 3 := sorry

/-- A known answer the compiled code decides, not the kernel. -/
theorem native : 10 + 10 = 20 := by native_decide

/-- A theorem that uses `native`: reported through `native`, not again here. -/
theorem usesNative : 10 + 10 = 20 := native

/-- The code the compiler runs in place of `slow`. -/
def fastImpl (n : Nat) : Nat := n

/-- Compiled as `fastImpl`. -/
@[implemented_by fastImpl] def slow (n : Nat) : Nat := n

/-- Compiled as a C function. -/
@[extern "ethlib_check_decls_test"] def external (n : Nat) : Nat := n

/-- A function the compiler replaces. -/
def double (n : Nat) : Nat := n + n

/-- Its replacement. -/
def doubleFast (n : Nat) : Nat := 2 * n

/-- Makes the compiler run `doubleFast` wherever `double` appears. -/
@[csimp] theorem double_eq_doubleFast : @double = @doubleFast := by
  funext n
  simp only [double, doubleFast]
  omega

/-- `while` compiles to `Loop.forIn`, which Lean core defines with `partial`. -/
def countdown (n : Nat) : Nat := Id.run do
  let mut i := n
  while i > 0 do
    i := i - 1
  return i

/-- An unsafe definition. -/
unsafe def reinterpret (n : Nat) : Nat := unsafeCast n

/-- An inductive type that carries a dependency's axiom.
The type and its constructor each inherit the axiom from the other, so it is reported at the type. -/
inductive Carrier where
  | mk : CheckDeclsForeign.T → Carrier

/-- A panic whose fallback is a dependency's opaque constant.
The kernel sees the fallback, `CheckDeclsForeign.hiddenNat`, so this cannot unfold. -/
def fallback : Nat := @panic Nat ⟨CheckDeclsForeign.hiddenNat⟩ "message"

/-- A panic whose fallback is built by a message function, from a dependency's opaque constant.
Only the outer message is a message; the fallback is a value, so it is followed. -/
def fallbackMessage : String :=
  @panic String ⟨mkPanicMessage "module" CheckDeclsForeign.hiddenNat 0 "text"⟩ "outer"

/-- An axiom named like a generated native axiom, with no declaration it belongs to. -/
axiom Phantom._native : False

/-- An unsafe definition named like a compiler auxiliary, with no `partial` parent. -/
unsafe def Ghost._unsafe_rec (n : Nat) : Nat := unsafeCast n

end CheckDeclsTest.Bad
