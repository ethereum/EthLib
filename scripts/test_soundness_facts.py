"""
Check `soundness_facts.py` itself, on a small repository built in a temporary
directory.

    python3 -m unittest scripts/test_soundness_facts.py

Only the standard library is used, like the script.
"""
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Load the script by path: `scripts` is not a package.
spec = importlib.util.spec_from_file_location("soundness_facts", HERE / "soundness_facts.py")
facts = importlib.util.module_from_spec(spec)
spec.loader.exec_module(facts)

EXPORTS = """\
/- `@[export eth_foo_in_a_comment]` is not an export. -/
@[export eth_foo_op_one]
def one (_ : Unit) : UInt8 := 1

@[inline,
  export eth_foo_op_two]
def two (_ : Unit) : UInt8 := 2

def three (_ : Unit) : UInt8 := 3
attribute [export eth_foo_op_three] three

@[export eth_foo_const_size]
def size (_ : Unit) : UInt64 := 4
"""

C_SOURCE = """\
extern uint8_t
eth_foo_op_one(
  uint8_t unit
);
extern uint8_t eth_foo_op_two(uint8_t unit);
extern uint8_t eth_foo_op_three(uint8_t unit);
extern uint64_t eth_foo_const_size(uint8_t unit);

/* eth_foo_op_three(0) in a comment is not a call. */
void use(void) {
  eth_foo_op_one(0);
  eth_foo_op_two(0);
  eth_foo_const_size(0);
}
"""

DOC = """\
# Soundness

This document describes the development tree that declares package version `1.0.0` in `pyproject.toml`.
""" + "".join(f"\n<!-- generated: {name} -->\n<!-- end generated -->\n" for name in facts.GENERATORS)


class SoundnessFacts(unittest.TestCase):

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = self.root = Path(self.tmp.name)
        (root / "EthLib" / "Exports").mkdir(parents=True)
        (root / "EthLib" / "Exports" / "Foo.lean").write_text(EXPORTS)
        (root / "bindings" / "python").mkdir(parents=True)
        (root / "bindings" / "python" / "foo.c").write_text(C_SOURCE)
        (root / "scripts").mkdir()
        (root / "scripts" / "check_decls_baseline.txt").write_text(
            "# comment\nnative Foo.known_answer\npartial Foo.spin\n")
        self.write_manifest("5e932f97dd25535344f80f9dd8da3aab83df0fe6")
        (root / "lean-toolchain").write_text("leanprover/lean4:v4.29.1\n")
        (root / "pyproject.toml").write_text('[project]\nname = "foo"\nversion = "1.0.0"\n')
        (root / "SOUNDNESS.md").write_text(DOC)
        self.assertEqual(facts.run(root, check=False), [])

    def tearDown(self):
        self.tmp.cleanup()

    def write_manifest(self, mathlib_rev: str) -> None:
        (self.root / "lake-manifest.json").write_text(json.dumps({"packages": [
            {"name": "ssz", "rev": "a23a2392ffffdd72caefb12f57b7ebd0c9a49de5",
             "inputRev": "a23a2392ffffdd72caefb12f57b7ebd0c9a49de5"},
            {"name": "mathlib", "rev": mathlib_rev, "inputRev": "v4.29.1"},
        ]}))

    def check(self) -> list[str]:
        return facts.run(self.root, check=True)

    def test_intact_tree_passes(self):
        self.assertEqual(self.check(), [])

    def test_exports_are_counted_however_written(self):
        # One-line, multi-line and `attribute` forms count; a comment does not.
        self.assertEqual(facts.lean_exports(self.root),
                         {"eth_foo_op_one", "eth_foo_op_two", "eth_foo_op_three", "eth_foo_const_size"})

    def test_a_declared_but_uncalled_export_is_not_called(self):
        # eth_foo_op_three is declared `extern` and named in a comment, but never called.
        text = facts.exports(self.root)
        self.assertIn("Lean exports 3 operations and 1 size constants.", text)
        self.assertIn("calls 2 of the operations and 1 of the constants.", text)
        self.assertIn("`eth_foo_op_three`", text)

    def test_nested_comment_and_strings_are_not_exports(self):
        # Lean block comments nest, so the inner `-/` does not end the comment.
        lean = self.root / "EthLib" / "Exports" / "Bar.lean"
        lean.write_text(
            "/- outer /- inner -/ @[export eth_foo_not_an_export] -/\n"
            'def msg : String := "@[export eth_foo_in_a_string]"\n'
            'def raw : String := r#"@[export eth_foo_in_a_raw_string] "quoted" "#\n'
            "def quote : Char := '\"'\n"
            "@[export eth_foo_op_after] def after (_ : Unit) : UInt8 := 0\n")
        found = facts.lean_exports(self.root)
        self.assertNotIn("eth_foo_not_an_export", found)
        self.assertNotIn("eth_foo_in_a_string", found)
        self.assertNotIn("eth_foo_in_a_raw_string", found)
        self.assertIn("eth_foo_op_after", found)

    def test_a_call_inside_a_string_is_not_a_call(self):
        c = self.root / "bindings" / "python" / "foo.c"
        c.write_text(C_SOURCE.replace(
            "  eth_foo_const_size(0);\n",
            '  report("eth_foo_const_size(0) failed");\n  char q = \'\\\'\';\n'))
        self.assertNotIn("eth_foo_const_size", facts.c_calls(self.root, facts.lean_exports(self.root)))

    def test_partly_used_constants_are_named_one_by_one(self):
        lean = self.root / "EthLib" / "Exports" / "Foo.lean"
        lean.write_text(EXPORTS + "\n@[export eth_foo_const_other]\ndef other (_ : Unit) : UInt64 := 5\n")
        text = facts.exports(self.root)
        self.assertIn("calls 2 of the operations and 1 of the constants.", text)
        self.assertIn("Exported constants it does not call: `eth_foo_const_other`.", text)
        self.assertNotIn("eth_foo_const_size`", text.split("does not call:")[-1])

    def test_removed_call_fails(self):
        c = self.root / "bindings" / "python" / "foo.c"
        c.write_text(C_SOURCE.replace("  eth_foo_op_two(0);\n", ""))
        self.assertIn("generated blocks are out of date: run python3 scripts/soundness_facts.py", self.check())

    def test_reformatted_export_keeps_its_count(self):
        lean = self.root / "EthLib" / "Exports" / "Foo.lean"
        lean.write_text(EXPORTS.replace("@[export eth_foo_op_one]", "@[export\n    eth_foo_op_one]"))
        self.assertEqual(self.check(), [])

    def test_changed_mathlib_commit_fails(self):
        self.write_manifest("0000000000000000000000000000000000000000")
        self.assertIn("generated blocks are out of date: run python3 scripts/soundness_facts.py", self.check())

    def test_changed_baseline_fails(self):
        (self.root / "scripts" / "check_decls_baseline.txt").write_text("partial Foo.spin\n")
        self.assertIn("generated blocks are out of date: run python3 scripts/soundness_facts.py", self.check())

    def test_version_bump_fails(self):
        (self.root / "pyproject.toml").write_text('[project]\nname = "foo"\nversion = "1.1.0"\n')
        problems = self.check()
        self.assertEqual(len(problems), 1)
        self.assertIn("declares 1.1.0", problems[0])

    def test_regenerating_never_touches_the_version_line(self):
        (self.root / "pyproject.toml").write_text('[project]\nname = "foo"\nversion = "1.1.0"\n')
        facts.run(self.root, check=False)
        self.assertIn("package version `1.0.0`", (self.root / "SOUNDNESS.md").read_text())


if __name__ == "__main__":
    unittest.main()
