"""
Check `readme_facts.py` itself, on a small repository built in a temporary
directory.

    python3 -m unittest scripts/test_readme_facts.py

Only the standard library is used, like the script.
"""
import importlib.util
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Load the script by path: `scripts` is not a package.
spec = importlib.util.spec_from_file_location("readme_facts", HERE / "readme_facts.py")
facts = importlib.util.module_from_spec(spec)
spec.loader.exec_module(facts)

CODE = """\
namespace EthLib.Cryptography.Foo
/-- `def notDeclared` in a comment declares nothing. -/
def op (x : Nat) : Nat := x
private def helper (x : Nat) : Nat := x
end EthLib.Cryptography.Foo
"""

PROOFS = """\
namespace EthLib.Cryptography.Foo
theorem op_id (x : Nat) : op x = x := rfl
end EthLib.Cryptography.Foo
"""

EXPORTS = "@[export eth_foo_op] def opExport (x : UInt8) : UInt8 := x\n"

BAR_PAGE = """\
# Bar

<!-- reviewed: -->

[The Foo page](../Foo/README.md) cites this one.

<!-- generated: baseline -->
<!-- end generated -->
"""

SUMS = """\
0000  foo_op/case_0/data.yaml
1111  foo_op/case_1/data.yaml
2222  foo_op/case_1/extra.yaml
"""

PAGE = """\
# Foo

<!-- reviewed: -->

```text
Lean      file         C export
op        Foo.lean     eth_foo_op
helper    Foo.lean
```

## Test vectors

<!-- generated: vectors -->
<!-- end generated -->

## What is proved

- `op` is the identity (`op_id`, `Foo.lean`).
- The helper (`Shared/Helper.lean`).
- The C glue is `bindings/python/foo.c`, and [the notes](../../../NOTES.md) explain it.
- [The Bar page](../Bar/README.md) cites this one.

<!-- generated: baseline -->
<!-- end generated -->
"""


class ReadmeFacts(unittest.TestCase):

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = self.root = Path(self.tmp.name)
        crypto = root / "EthLib" / "Cryptography"
        for d in ("Foo", "Proofs/Foo", "Exports", "Shared", "Other", "Bar", "Proofs/Bar"):
            (crypto / d).mkdir(parents=True)
        (crypto / "Foo.lean").write_text("import EthLib.Cryptography.Foo.Foo\n")
        (crypto / "Foo" / "Foo.lean").write_text(CODE)
        (crypto / "Proofs" / "Bar" / "Bar.lean").write_text("theorem spin_ok : True := trivial\n")
        (crypto / "Bar" / "README.md").write_text(BAR_PAGE)
        (root / "bindings" / "python").mkdir(parents=True)
        (root / "bindings" / "python" / "foo.c").write_text("int foo;\n")
        (root / "NOTES.md").write_text("Notes.\n")
        (crypto / "Proofs" / "Foo" / "Foo.lean").write_text(PROOFS)
        (crypto / "Exports" / "Foo.lean").write_text(EXPORTS)
        (crypto / "Shared" / "Helper.lean").write_text("def shared := 0\n")
        (crypto / "Other" / "Unrelated.lean").write_text("def unrelated := 0\n")
        (root / "scripts").mkdir()
        (root / "scripts" / "check_decls_baseline.txt").write_text(
            "# comment\nnative EthLib.Cryptography.Foo.known_answer\npartial EthLib.Cryptography.Bar.spin\n")
        (root / "tests" / "cryptography" / "foo").mkdir(parents=True)
        (root / "tests" / "cryptography" / "foo" / "SHA256SUMS").write_text(SUMS)
        self.page = crypto / "Foo" / "README.md"
        self.page.write_text(PAGE)
        self.assertEqual(self.run_facts(check=False, reviewed=("Bar", "Foo")), [])

    def tearDown(self):
        self.tmp.cleanup()

    def run_facts(self, check: bool, reviewed: tuple[str, ...] = ()) -> list[str]:
        return facts.run(self.root, check=check, reviewed=reviewed, required=("Bar", "Foo"))

    def check(self) -> list[str]:
        return self.run_facts(check=True)

    def assertProblem(self, text: str):
        problems = self.check()
        self.assertTrue(any(text in p for p in problems), problems)

    def test_intact_tree_passes(self):
        self.assertEqual(self.check(), [])

    def test_generated_blocks(self):
        page = self.page.read_text()
        # Two files of one case count once; a module's baseline excludes other modules.
        self.assertIn("holds 2 cases:", page)
        self.assertIn("handler    cases\nfoo_op         2\n", page)
        self.assertIn("- `EthLib.Cryptography.Foo.known_answer`, `native`\n", page)
        self.assertNotIn("Bar.spin", page)

    def test_changed_baseline_fails(self):
        (self.root / "scripts" / "check_decls_baseline.txt").write_text("partial EthLib.Cryptography.Bar.spin\n")
        self.assertProblem("generated blocks are out of date")
        self.run_facts(check=False)
        self.assertIn("lists no finding in this module.", self.page.read_text())

    def test_new_vector_fails(self):
        sums = self.root / "tests" / "cryptography" / "foo" / "SHA256SUMS"
        sums.write_text(SUMS + "3333  foo_op/case_2/data.yaml\n")
        self.assertProblem("generated blocks are out of date")

    def test_vectors_without_a_block_fail(self):
        self.page.write_text(self.page.read_text().replace("<!-- generated: vectors -->", "<!-- removed -->"))
        self.assertProblem("missing generated block: vectors")

    def test_changed_proof_fails_until_reviewed(self):
        proofs = self.root / "EthLib" / "Cryptography" / "Proofs" / "Foo" / "Foo.lean"
        proofs.write_text(PROOFS + "theorem op_zero : op 0 = 0 := rfl\n")
        self.assertProblem("changed since it was last reviewed")
        # Regenerating alone does not record a review.
        self.run_facts(check=False)
        self.assertProblem("changed since it was last reviewed")
        self.assertEqual(self.run_facts(check=False, reviewed=("Foo",)), [])
        self.assertEqual(self.check(), [])

    def test_changed_root_file_fails(self):
        (self.root / "EthLib" / "Cryptography" / "Foo.lean").write_text("-- changed\n")
        self.assertProblem("Foo/README.md: the files it describes changed")

    def test_changed_cited_c_file_fails(self):
        (self.root / "bindings" / "python" / "foo.c").write_text("int foo = 1;\n")
        self.assertProblem("Foo/README.md: the files it describes changed")

    def test_changed_linked_file_fails(self):
        (self.root / "NOTES.md").write_text("Other notes.\n")
        self.assertProblem("Foo/README.md: the files it describes changed")

    def test_reviewing_one_page_leaves_a_page_citing_it_intact(self):
        # The pages link each other, so tracking each other's README would never settle.
        (self.root / "EthLib" / "Cryptography" / "Proofs" / "Bar" / "Bar.lean").write_text("-- changed\n")
        self.assertEqual(self.check(), [
            "EthLib/Cryptography/Bar/README.md: the files it describes changed since it was last reviewed: "
            "read it again, then run python3 scripts/readme_facts.py --reviewed Bar"])
        self.assertEqual(self.run_facts(check=False, reviewed=("Bar",)), [])
        self.assertEqual(self.check(), [])

    def test_deleted_required_page_fails(self):
        (self.root / "EthLib" / "Cryptography" / "Bar" / "README.md").unlink()
        self.assertProblem("Bar/README.md: missing")

    def test_changed_cited_file_outside_the_module_fails(self):
        (self.root / "EthLib" / "Cryptography" / "Shared" / "Helper.lean").write_text("def shared := 1\n")
        self.assertProblem("changed since it was last reviewed")

    def test_unrelated_file_and_page_edit_pass(self):
        (self.root / "EthLib" / "Cryptography" / "Other" / "Unrelated.lean").write_text("def unrelated := 1\n")
        self.page.write_text(self.page.read_text() + "\nOne more sentence.\n")
        self.assertEqual(self.check(), [])

    def test_renamed_theorem_fails(self):
        proofs = self.root / "EthLib" / "Cryptography" / "Proofs" / "Foo" / "Foo.lean"
        proofs.write_text(PROOFS.replace("op_id", "op_eq_self"))
        self.assertProblem("cites `op_id`, which no file it describes declares")

    def test_a_name_in_a_comment_is_not_declared(self):
        self.page.write_text(self.page.read_text().replace("(`op_id`", "(`notDeclared`"))
        self.assertProblem("cites `notDeclared`")

    def test_missing_file_fails(self):
        self.page.write_text(self.page.read_text().replace("`Shared/Helper.lean`", "`Shared/Gone.lean`"))
        self.assertProblem("cites `Shared/Gone.lean`, which names no file")

    def test_ambiguous_file_outside_the_module_fails(self):
        (self.root / "EthLib" / "Cryptography" / "Other" / "Helper.lean").write_text("def other := 0\n")
        self.page.write_text(self.page.read_text().replace("`Shared/Helper.lean`", "`Helper.lean`"))
        self.assertProblem("cites `Helper.lean`, which names several files")

    def test_table_name_not_in_its_file_fails(self):
        code = self.root / "EthLib" / "Cryptography" / "Foo" / "Foo.lean"
        code.write_text(CODE.replace("private def helper", "private def helper2"))
        self.assertProblem("lists `helper` in `Foo.lean`, which does not declare it")

    def test_unknown_c_export_fails(self):
        (self.root / "EthLib" / "Cryptography" / "Exports" / "Foo.lean").write_text(
            EXPORTS.replace("eth_foo_op", "eth_foo_renamed"))
        self.assertProblem("lists the C export `eth_foo_op`")

    def test_missing_review_line_fails(self):
        self.page.write_text(self.page.read_text().replace("<!-- reviewed:", "<!-- seen:"))
        self.assertProblem("no `<!-- reviewed: ... -->` line")

    def test_reviewing_an_unknown_module_fails(self):
        self.assertIn("--reviewed Baz: no module of that name has a README",
                      self.run_facts(check=False, reviewed=("Baz",)))

    def test_check_changes_nothing(self):
        (self.root / "scripts" / "check_decls_baseline.txt").write_text("")
        before = self.page.read_text()
        self.check()
        self.assertEqual(self.page.read_text(), before)


if __name__ == "__main__":
    unittest.main()
