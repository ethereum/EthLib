"""Tests of `check_lean_commands.py` on small repositories in a temporary directory."""

import importlib.util
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Load the script by path: `scripts` is not a package.
spec = importlib.util.spec_from_file_location(
    "check_lean_commands", HERE / "check_lean_commands.py"
)
assert spec and spec.loader
commands = importlib.util.module_from_spec(spec)
spec.loader.exec_module(commands)

PRINT = """\
theorem t : True := trivial

/--
info: 't' depends on axioms: []
-/
#guard_msgs (whitespace := lax) in
#print axioms t
"""

EVAL_AND_CHECK = """\
def x : Nat := 1
#eval x
  #check x
"""

TIGHT = """\
def x : Nat := 1
#eval! x
#check(x)
set_option maxRecDepth 1000 in #reduce x
"""

NO_COMMAND = """\
/-- A doc comment may show `#eval x` and a code line:

#print axioms t
-/
def v : Vector Nat 2 :=
  #v[1, 2]

-- #check v
def s : String := "
#eval s"
def a : Array Nat := #[1]
/- outer /- inner -/
#eval a
-/
def r : String := r#"
#eval r"#
def c : Char := '#'
"""

ALLOWLIST_HEADER = "# Commands that run at every build, each for a reason.\n\n"


class CheckLeanCommands(unittest.TestCase):
    def run_check(self, files: dict[str, str], allowlist: str = ALLOWLIST_HEADER) -> list[str]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name, text in files.items():
                path = root / "EthLib" / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding="utf-8")
            (root / "scripts").mkdir()
            (root / commands.ALLOWLIST).write_text(allowlist, encoding="utf-8")
            return commands.check(root)

    def test_guarded_print_fails(self):
        self.assertEqual(
            self.run_check({"X/A.lean": PRINT}),
            [
                "EthLib/X/A.lean:6: `#guard_msgs (whitespace := lax) in` runs at every build; "
                "check it in CI instead, or list it in the allowlist with a reason",
                "EthLib/X/A.lean:7: `#print axioms t` runs at every build; "
                "check it in CI instead, or list it in the allowlist with a reason",
            ],
        )

    def test_eval_and_indented_check_fail(self):
        self.assertEqual(
            self.run_check({"X/B.lean": EVAL_AND_CHECK}),
            [
                "EthLib/X/B.lean:2: `#eval x` runs at every build; "
                "check it in CI instead, or list it in the allowlist with a reason",
                "EthLib/X/B.lean:3: `#check x` runs at every build; "
                "check it in CI instead, or list it in the allowlist with a reason",
            ],
        )

    def test_commands_without_a_space_or_after_in_fail(self):
        self.assertEqual(
            self.run_check({"X/T.lean": TIGHT}),
            [
                "EthLib/X/T.lean:2: `#eval! x` runs at every build; "
                "check it in CI instead, or list it in the allowlist with a reason",
                "EthLib/X/T.lean:3: `#check(x)` runs at every build; "
                "check it in CI instead, or list it in the allowlist with a reason",
                "EthLib/X/T.lean:4: `set_option maxRecDepth 1000 in #reduce x` "
                "runs at every build; "
                "check it in CI instead, or list it in the allowlist with a reason",
            ],
        )

    def test_comments_strings_and_literals_pass(self):
        self.assertEqual(self.run_check({"X/C.lean": NO_COMMAND}), [])

    def test_allowlisted_command_passes(self):
        allowlist = ALLOWLIST_HEADER + (
            "EthLib/X/B.lean | the value is shown on purpose | #eval x\n"
            "EthLib/X/B.lean | the type is shown on purpose | #check x\n"
        )
        self.assertEqual(self.run_check({"X/B.lean": EVAL_AND_CHECK}, allowlist), [])

    def test_entry_fits_only_its_file(self):
        allowlist = ALLOWLIST_HEADER + (
            "EthLib/X/A.lean | the value is shown on purpose | #eval x\n"
            "EthLib/X/A.lean | the type is shown on purpose | #check x\n"
        )
        self.assertEqual(
            self.run_check({"X/A.lean": "", "X/B.lean": EVAL_AND_CHECK}, allowlist),
            [
                "EthLib/X/B.lean:2: `#eval x` runs at every build; "
                "check it in CI instead, or list it in the allowlist with a reason",
                "EthLib/X/B.lean:3: `#check x` runs at every build; "
                "check it in CI instead, or list it in the allowlist with a reason",
                "scripts/check_lean_commands_allowlist.txt: EthLib/X/A.lean has no command "
                "`#check x`; remove the entry",
                "scripts/check_lean_commands_allowlist.txt: EthLib/X/A.lean has no command "
                "`#eval x`; remove the entry",
            ],
        )

    def test_command_with_the_separator_can_be_listed(self):
        files = {"X/M.lean": "#eval match 0 with | _ => 1\n"}
        allowlist = ALLOWLIST_HEADER + (
            "EthLib/X/M.lean | the match is shown on purpose | #eval match 0 with | _ => 1\n"
        )
        self.assertEqual(self.run_check(files, allowlist), [])

    def test_duplicate_entry_fails(self):
        allowlist = ALLOWLIST_HEADER + (
            "EthLib/X/B.lean | the value is shown on purpose | #eval x\n"
            "EthLib/X/B.lean | the value is shown again | #eval x\n"
            "EthLib/X/B.lean | the type is shown on purpose | #check x\n"
        )
        self.assertEqual(
            self.run_check({"X/B.lean": EVAL_AND_CHECK}, allowlist),
            ["scripts/check_lean_commands_allowlist.txt:4: EthLib/X/B.lean lists `#eval x` twice"],
        )

    def test_entry_without_reason_fails(self):
        allowlist = ALLOWLIST_HEADER + "EthLib/X/B.lean | #eval x\n"
        self.assertEqual(
            self.run_check({"X/C.lean": NO_COMMAND}, allowlist),
            [
                "scripts/check_lean_commands_allowlist.txt:3: "
                "an entry is `path | reason | command`, on one line"
            ],
        )

    def test_stale_entry_fails(self):
        allowlist = ALLOWLIST_HEADER + "EthLib/X/C.lean | no longer needed | #eval x\n"
        self.assertEqual(
            self.run_check({"X/C.lean": NO_COMMAND}, allowlist),
            [
                "scripts/check_lean_commands_allowlist.txt: EthLib/X/C.lean has no command "
                "`#eval x`; remove the entry"
            ],
        )

    def test_repository_passes(self):
        self.assertEqual(commands.check(HERE.parent), [])


if __name__ == "__main__":
    unittest.main()
