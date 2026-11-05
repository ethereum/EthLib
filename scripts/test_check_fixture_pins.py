"""
Check `check_fixture_pins.py` itself, on small repositories built in a temporary directory.

    uv run --no-project --python 3.12 python -m unittest scripts/test_check_fixture_pins.py

Only the standard library is used, like the script.
"""

import importlib.util
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Load the script by path: `scripts` is not a package.
spec = importlib.util.spec_from_file_location("check_fixture_pins", HERE / "check_fixture_pins.py")
pins = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pins)

PIN = "1111111111111111111111111111111111111111"
OTHER = "2222222222222222222222222222222222222222"

SOURCES = f"""\
[repositories."org/vectors"]
commit = "{PIN}"
directories = ["tests/suite/a"]

[other]
"tests/suite/b" = "RFC 1"
"""

SUMS = "0000  case/data.yaml\n"


class Tree:
    """A temporary repository with two pinned vector directories that pass the check."""

    def __init__(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.write("tests/sources.toml", SOURCES)
        self.write("tests/suite/a/SHA256SUMS", f"# Source: org/vectors at {PIN}\n" + SUMS)
        self.write("tests/suite/b/SHA256SUMS", "# Source: RFC 1\n" + SUMS)
        self.write("tests/suite/README.md", f"The cases of `a/` come from org/vectors at {PIN}.\n")
        self.write("bindings/python/tests/test_a.py", f'"""At commit {PIN[:7]}."""\n')

    def write(self, name: str, text: str) -> None:
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def problems(self) -> list[str]:
        try:
            return pins.check(self.root)
        finally:
            self.tmp.cleanup()


class Pins(unittest.TestCase):
    def assertFails(self, tree: Tree, text: str) -> None:
        problems = tree.problems()
        self.assertEqual(len(problems), 1, problems)
        self.assertIn(text, problems[0])

    def test_intact_tree_passes(self):
        self.assertEqual(Tree().problems(), [])

    def test_repository(self):
        self.assertEqual(pins.check(HERE.parent), [])

    def test_unlisted_directory(self):
        tree = Tree()
        tree.write("bindings/python/tests/c/SHA256SUMS", SUMS)
        self.assertFails(tree, "bindings/python/tests/c: a pinned vector directory that")

    def test_listed_directory_without_manifest(self):
        tree = Tree()
        (tree.root / "tests/suite/b/SHA256SUMS").unlink()
        self.assertFails(tree, "tests/suite/b holds no SHA256SUMS")

    def test_missing_source_line(self):
        tree = Tree()
        tree.write("tests/suite/a/SHA256SUMS", SUMS)
        self.assertFails(tree, f"missing the line '# Source: org/vectors at {PIN}'")

    def test_source_line_of_another_commit(self):
        tree = Tree()
        tree.write(
            "tests/suite/b/SHA256SUMS",
            f"# Source: RFC 1\n# Source: org/vectors at {OTHER}\n" + SUMS,
        )
        problems = tree.problems()
        self.assertTrue(any("is not a source" in p for p in problems), problems)

    def test_readme_without_the_pin(self):
        tree = Tree()
        tree.write("tests/suite/README.md", "The cases of `a/` come from org/vectors.\n")
        self.assertFails(tree, f"tests/suite/README.md: does not name org/vectors at {PIN}")

    def test_own_readme_comes_first(self):
        tree = Tree()
        tree.write("tests/suite/a/README.md", "No commit here.\n")
        self.assertFails(tree, "tests/suite/a/README.md: does not name")

    def test_cited_commit_that_is_not_a_pin(self):
        for text in (
            f"at commit `{OTHER}`",
            f"at commit\n# {OTHER[:9]}",
            f"# Commit: {OTHER}",
            f"https://github.com/org/vectors/blob/{OTHER}/case.json",
        ):
            with self.subTest(text=text):
                tree = Tree()
                tree.write("tests/suite/a/format.md", text + "\n")
                self.assertFails(tree, f"cites commit {OTHER[:9]}")

    def test_hex_word_that_is_not_a_pin(self):
        for text in (
            "execution-specs at `abc1234`",
            "execution-specs at abc1234, in gas.py",
            "the commit `abc1234cafe`",
        ):
            with self.subTest(text=text):
                tree = Tree()
                tree.write("bindings/python/tests/test_c.py", f'"""{text}."""\n')
                self.assertFails(tree, "cites commit abc1234")

    def test_hex_word_that_reads_as_no_commit(self):
        # A digest is longer than a commit, even when it is cut short.
        # A word needs a letter and a digit.
        for text in (
            f"`{'ab12' * 16}`",
            "`deadbeef`",
            "`1234567`",
            "look at abc1234x",
            "sha256 `e2fa7ea2…`",
        ):
            with self.subTest(text=text):
                tree = Tree()
                tree.write("bindings/python/tests/test_c.py", f'"""{text}."""\n')
                self.assertEqual(tree.problems(), [])

    def test_link_to_a_change_is_not_a_citation(self):
        tree = Tree()
        tree.write("tests/suite/a/format.md", f"https://github.com/org/lib/commit/{OTHER}\n")
        self.assertEqual(tree.problems(), [])

    def test_stale_pin(self):
        tree = Tree()
        tree.write(
            "tests/sources.toml", SOURCES + f'\n[repositories."org/unused"]\ncommit = "{OTHER}"\n'
        )
        self.assertFails(tree, "no test cites the pin of org/unused")

    def test_short_pin(self):
        tree = Tree()
        tree.write("tests/sources.toml", SOURCES.replace(PIN, PIN[:7]))
        problems = tree.problems()
        self.assertIn("tests/sources.toml: org/vectors needs a full 40-digit commit", problems)


ARCHIVE = f"""
[archives."vectors/v1/all"]
repository = "org/vectors"
url = "https://example.org/v1/all.tar.gz"
size = 10
sha256 = "{"3" * 64}"
"""


class Archives(unittest.TestCase):
    def tree(self, archive: str = ARCHIVE) -> Tree:
        """The intact tree, with one archive that a test names."""
        tree = Tree()
        tree.write("tests/sources.toml", SOURCES + archive)
        tree.write("bindings/python/tests/test_b.py", 'ARCHIVE = "vectors/v1/all"\n')
        return tree

    def test_named_archive_passes(self):
        self.assertEqual(self.tree().problems(), [])

    def test_archive_that_no_test_names(self):
        tree = self.tree()
        (tree.root / "bindings/python/tests/test_b.py").unlink()
        self.assertEqual(
            tree.problems(), ["tests/sources.toml: no test names the archive vectors/v1/all"]
        )

    def test_archive_from_no_repository(self):
        archive = ARCHIVE.replace('repository = "org/vectors"', 'source = "NIST CAVP"')
        self.assertEqual(self.tree(archive).problems(), [])
        archive = ARCHIVE.replace('repository = "org/vectors"', 'source = ""')
        problems = self.tree(archive).problems()
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("needs a recorded repository", problems[0])

    def test_malformed_archive(self):
        for old, new, text in (
            ('"org/vectors"', '"org/other"', "a recorded repository"),
            ("https://", "http://", "an https URL"),
            ("size = 10", "size = 0", "a positive size"),
            ("size = 10", 'size = "10"', "a positive size"),
            ("3" * 64, "3" * 63, "a 64-digit sha256"),
        ):
            with self.subTest(text=text, new=new):
                problems = self.tree(ARCHIVE.replace(old, new)).problems()
                self.assertEqual(len(problems), 1, problems)
                self.assertIn(f"the archive vectors/v1/all needs {text}", problems[0])


if __name__ == "__main__":
    unittest.main()
