module

public import EthLib.Base.Exports.PyValue

/-!
# Bounded integers at the Python boundary

The `FinAsInt` scope represents `Fin n` as a Python integer below `n`.

Exporters opt in to this representation with `open scoped EthLib.Exports.FinAsInt`.

Importing this module alone selects no representation for `Fin`.
-/

public section

namespace EthLib.Exports.FinAsInt

scoped instance (n : Nat) : ToPy (Fin n) := ⟨fun value => .int value.val⟩

scoped instance (n : Nat) : FromPy (Fin n) := ⟨fun value => do
  let bounded ← fromPyBelow n value
  return ⟨bounded.val, bounded.property⟩⟩

scoped instance (n : Nat) : PlainPy (Fin n) := ⟨fun _ => rfl⟩

scoped instance (n : Nat) : LawfulPy (Fin n) where
  fromPy_toPy value := by
    show (do
      let bounded ← fromPyBelow n (.int value.val)
      pure (⟨bounded.val, bounded.property⟩ : Fin n)) = .ok value
    simp [fromPyBelow, fromPy, value.isLt, bind, Except.bind, pure, Except.pure]

end EthLib.Exports.FinAsInt
