"""Tests of `check_fixture_pins.py` on small repositories in a temporary directory."""

import importlib.util
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Load the script by path: `scripts` is not a package.
spec = importlib.util.spec_from_file_location("check_fixture_pins", HERE / "check_fixture_pins.py")
assert spec and spec.loader
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

GENERATORS = """\
[generators.tool]
computes = "the tool"
version = "1.0"
source = "its README"

[[directories."tests/suite/a"]]
cases = ["**"]
generator = "tool"

[[directories."tests/suite/b"]]
cases = ["case/*"]
generator = "ethlib"

[runtime]
tools = []
"""


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
        self.write("tests/generators.toml", GENERATORS)

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
    def assert_fails(self, tree: Tree, text: str) -> None:
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
        self.assert_fails(tree, "bindings/python/tests/c: a pinned vector directory that")

    def test_listed_directory_without_manifest(self):
        tree = Tree()
        (tree.root / "tests/suite/b/SHA256SUMS").unlink()
        self.assert_fails(tree, "tests/suite/b holds no SHA256SUMS")

    def test_missing_source_line(self):
        tree = Tree()
        tree.write("tests/suite/a/SHA256SUMS", SUMS)
        self.assert_fails(tree, f"missing the line '# Source: org/vectors at {PIN}'")

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
        self.assert_fails(tree, f"tests/suite/README.md: does not name org/vectors at {PIN}")

    def test_own_readme_comes_first(self):
        tree = Tree()
        tree.write("tests/suite/a/README.md", "No commit here.\n")
        self.assert_fails(tree, "tests/suite/a/README.md: does not name")

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
                self.assert_fails(tree, f"cites commit {OTHER[:9]}")

    def test_hex_word_that_is_not_a_pin(self):
        for text in (
            "execution-specs at `abc1234`",
            "execution-specs at abc1234, in gas.py",
            "the commit `abc1234cafe`",
        ):
            with self.subTest(text=text):
                tree = Tree()
                tree.write("bindings/python/tests/test_c.py", f'"""{text}."""\n')
                self.assert_fails(tree, "cites commit abc1234")

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
        self.assert_fails(tree, "no test cites the pin of org/unused")

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


ARCHIVE_GROUP = """
[[archives."vectors/v1/all"]]
cases = ["**"]
generator = "not established"
checked = "the release notes"
"""


class Archives(unittest.TestCase):
    def tree(self, archive: str = ARCHIVE) -> Tree:
        """The intact tree, with one archive that a test names."""
        tree = Tree()
        tree.write("tests/sources.toml", SOURCES + archive)
        tree.write("bindings/python/tests/test_b.py", 'ARCHIVE = "vectors/v1/all"\n')
        tree.write("tests/generators.toml", GENERATORS + ARCHIVE_GROUP)
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

    def test_archive_without_generator(self):
        tree = self.tree()
        tree.write("tests/generators.toml", GENERATORS)
        self.assertEqual(
            tree.problems(),
            ["tests/generators.toml: vectors/v1/all has no entry in the table archives"],
        )


class Generators(unittest.TestCase):
    def problems(self, generators: str, *files: tuple[str, str]) -> list[str]:
        """The problems of the intact tree with `generators` in place, and `files` written."""
        tree = Tree()
        tree.write("tests/generators.toml", generators)
        for name, text in files:
            tree.write(name, text)
        return tree.problems()

    def assert_fails(self, text: str, generators: str, *files: tuple[str, str]) -> None:
        problems = self.problems(generators, *files)
        self.assertEqual(len(problems), 1, problems)
        self.assertIn(text, problems[0])

    def test_missing_file(self):
        tree = Tree()
        (tree.root / "tests/generators.toml").unlink()
        self.assertEqual(tree.problems(), ["tests/generators.toml is missing"])

    def test_directory_without_entry(self):
        text = GENERATORS.replace(
            '[[directories."tests/suite/b"]]', '[[directories."tests/suite/c"]]'
        )
        problems = self.problems(text)
        self.assertIn(
            "tests/generators.toml: tests/suite/b has no entry in the table directories", problems
        )
        self.assertIn(
            "tests/generators.toml: tests/suite/c is in the table directories, "
            "but not in tests/sources.toml",
            problems,
        )

    def test_file_in_no_group(self):
        sums = "# Source: RFC 1\n" + SUMS + "1111  other/data.yaml\n"
        self.assert_fails(
            "tests/suite/b/other/data.yaml belongs to no group",
            GENERATORS,
            ("tests/suite/b/SHA256SUMS", sums),
        )

    def test_licence_and_script_need_no_group(self):
        sums = "# Source: RFC 1\n" + SUMS + "1111  LICENSE\n2222  generate.py\n"
        self.assertEqual(self.problems(GENERATORS, ("tests/suite/b/SHA256SUMS", sums)), [])

    def test_glob_that_matches_nothing(self):
        text = GENERATORS.replace('cases = ["case/*"]', 'cases = ["case/*", "missing/*"]')
        self.assert_fails("tests/suite/b, group 1: missing/* matches no pinned file", text)

    def test_shared_file_needs_a_subset(self):
        group = '\n[[directories."tests/suite/b"]]\ncases = ["**"]\ngenerator = "tool"\n'
        self.assert_fails("tests/suite/b/case/data.yaml is in several groups", GENERATORS + group)
        both = GENERATORS.replace('cases = ["case/*"]', 'cases = ["case/*"]\nsubset = "the inputs"')
        self.assertEqual(
            self.problems(both + group.replace("generator", 'subset = "the outputs"\ngenerator')),
            [],
        )

    def test_generator_names(self):
        for old, new, text in (
            ('generator = "tool"', 'generator = "other"', "the generator 'other' is not defined"),
            ("[generators.tool]", '[generators."ethlib"]', "the generator 'ethlib' is reserved"),
            ('version = "1.0"\n', "", "the generator 'tool' needs version"),
            ('cases = ["**"]', "cases = []", "group 1: needs a list of globs in cases"),
            ('generator = "ethlib"', 'generator = "ethlib"\nnote = "x"', "unknown field note"),
        ):
            with self.subTest(text=text):
                problems = self.problems(GENERATORS.replace(old, new))
                self.assertTrue(any(text in p for p in problems), problems)

    def test_unused_generator(self):
        text = GENERATORS.replace(
            "[runtime]",
            '[generators.spare]\ncomputes = "x"\nversion = "1"\nsource = "y"\n\n[runtime]',
        )
        self.assert_fails("the generator 'spare' is defined but no group names it", text)

    def test_not_established_needs_what_was_checked(self):
        text = GENERATORS.replace('generator = "ethlib"', 'generator = "not established"')
        self.assert_fails(
            "needs checked when, and only when, the generator is not established", text
        )
        self.assertEqual(
            self.problems(
                text.replace('"not established"', '"not established"\nchecked = "the README"')
            ),
            [],
        )


LOCK = """\
[[package]]
name = "py-ecc"
version = "8.0.0"
"""

ORACLE = """
[runtime.oracles.py_ecc]
package = "py-ecc"
version = "8.0.0"
computes = "BLS signatures"
"""


class Runtime(unittest.TestCase):
    def problems(self, generators: str, *files: tuple[str, str]) -> list[str]:
        tree = Tree()
        tree.write("tests/generators.toml", generators)
        tree.write("uv.lock", LOCK)
        for name, text in files:
            tree.write(name, text)
        return tree.problems()

    def test_listed_oracle_passes(self):
        test = ("bindings/python/tests/test_c.py", "from py_ecc.bls import G2ProofOfPossession\n")
        self.assertEqual(self.problems(GENERATORS + ORACLE, test), [])

    def test_unlisted_import(self):
        test = ("bindings/python/tests/test_c.py", "import py_ecc\n")
        self.assertEqual(
            self.problems(GENERATORS, test),
            [
                "tests/generators.toml: the tests import py_ecc, "
                "which the table runtime does not list"
            ],
        )

    def test_standard_library_and_local_modules_need_no_entry(self):
        files = (
            ("bindings/python/tests/helpers.py", "import json\n"),
            (
                "bindings/python/tests/test_c.py",
                "import hashlib\nimport helpers\nfrom ethlib import x\nfrom . import y\n",
            ),
        )
        self.assertEqual(self.problems(GENERATORS, *files), [])

    def test_entry_that_no_test_imports(self):
        self.assertEqual(
            self.problems(GENERATORS + ORACLE),
            ["tests/generators.toml: the table runtime lists py_ecc, which no test imports"],
        )

    def test_version_differs_from_the_lock_file(self):
        test = ("bindings/python/tests/test_c.py", "import py_ecc\n")
        self.assertEqual(
            self.problems(
                GENERATORS + ORACLE.replace('version = "8.0.0"', 'version = "7.0.0"'), test
            ),
            ["tests/generators.toml: the oracle py_ecc has version 7.0.0, but uv.lock has 8.0.0"],
        )

    def test_standard_library_and_local_oracles(self):
        oracles = (
            '\n[runtime.oracles.hashlib]\npackage = "python"\ncomputes = "SHA-256"\n'
            '\n[runtime.oracles.reference]\npath = "bindings/python/tests/reference.py"\n'
            'computes = "a trie"\n'
        )
        files = (
            ("bindings/python/tests/reference.py", "X = 1\n"),
            ("bindings/python/tests/test_c.py", "import hashlib\nimport reference\n"),
        )
        self.assertEqual(self.problems(GENERATORS + oracles, *files), [])
        not_standard = oracles.replace("hashlib", "py_ecc")
        test = ("bindings/python/tests/test_d.py", "import py_ecc\n")
        problems = self.problems(GENERATORS + not_standard, *files, test)
        self.assertIn(
            "tests/generators.toml: the oracle py_ecc is not in the standard library", problems
        )


if __name__ == "__main__":
    unittest.main()
