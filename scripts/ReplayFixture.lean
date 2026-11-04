import Lean

/-!
A theorem that the kernel never checked, for `scripts/replay.sh`.

Its type is `False` and its proof is `True.intro`.

leanchecker must reject it when it replays this module.
-/

open Lean Elab Command

set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl <| .thmDecl {
  name := `ReplayFixture.unchecked
  levelParams := []
  type := mkConst ``False
  value := mkConst ``True.intro }
