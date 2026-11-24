module

/-!
# Proofs: one tactic for the injectivity of error codes

Each error type has a stable code per constructor.

The tactic proves that two errors with one code come from one constructor.
-/

public section

namespace EthLib.Base

open Lean in
/-- Prove that two errors with equal codes have one constructor index.

The goal must be the equality of the constructor indices of two errors named `e₁` and `e₂`.

The equation of their codes must be named `h`.

The arguments are the code functions, which give each constructor a distinct literal. -/
macro "code_injective " codes:ident,+ : tactic => do
  -- Only these three names come from the theorem, so the rest of the macro stays hygienic.
  let e₁ := mkIdent `e₁
  let e₂ := mkIdent `e₂
  let h := mkIdent `h
  -- Split on both errors.
  --
  -- On one constructor both indices agree.
  --
  -- On two distinct constructors, the codes are two distinct literals, which `decide` separates.
  `(tactic| (cases $e₁:ident <;> cases $e₂:ident <;>
    first
      | rfl
      | (simp only [$[$codes:ident],*] at $h:ident; exact absurd $h (by decide))))

end EthLib.Base
