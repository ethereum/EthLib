import LeanChecker

/-!
Replay the declarations of one module into Lean's kernel, for `scripts/replay.sh`.

The module is the value of the environment variable `REPLAY_MODULE`.

leanchecker replays every module whose name starts with its argument.

With more than one such module, leanchecker from Lean v4.36.0 crashes with a segmentation fault.

This script calls the replay function of leanchecker on the named module alone.

It fails with the error of the kernel when a declaration does not replay.
-/

#eval show IO Unit from do
  let some name ← IO.getEnv "REPLAY_MODULE" | throw <| IO.userError "REPLAY_MODULE is not set"
  unsafe replayFromImports name.toName
