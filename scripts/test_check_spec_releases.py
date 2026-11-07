"""Tests of `check_spec_releases.py` on release lists and source files written here."""

import importlib.util
import re
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Load the script by path: `scripts` is not a package.
spec = importlib.util.spec_from_file_location(
    "check_spec_releases", HERE / "check_spec_releases.py"
)
assert spec and spec.loader
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)

Release = check.Release

EXECUTION = [
    Release("tests-bogota-devnet@v2.0.0", "2026-10-27T20:18:24Z", True),
    Release("tests@v21.0.2", "2026-10-26T16:29:51Z", False),
    Release("tests-heze-devnet@v3.0.0", "2026-10-21T18:52:16Z", True),
    Release("tests-bogota-devnet@v1.1.1", "2026-10-21T10:21:06Z", True),
    Release("tests@v21.0.1", "2026-10-08T14:23:12Z", False),
]

CONSENSUS = [
    Release("v1.7.0-beta.4", "2026-10-08T19:27:03Z", True),
    Release("v1.7.0-beta.3", "2026-10-05T19:28:33Z", True),
    Release("v1.6.1", "2025-11-15T13:27:52Z", False),
]


class Newer(unittest.TestCase):
    def test_the_latest_release_has_nothing_newer(self):
        self.assertEqual(check.newer("tests@v21.0.2", EXECUTION), [])
        self.assertEqual(check.newer("v1.7.0-beta.4", CONSENSUS), [])

    def test_a_stable_pin_ignores_other_lines_and_pre_releases(self):
        later = check.newer("tests@v21.0.1", EXECUTION)
        self.assertEqual([release.tag for release in later], ["tests@v21.0.2"])

    def test_a_devnet_pin_follows_its_own_line(self):
        later = check.newer("tests-bogota-devnet@v1.1.1", EXECUTION)
        self.assertEqual([release.tag for release in later], ["tests-bogota-devnet@v2.0.0"])

    def test_a_pre_release_pin_counts_pre_releases(self):
        later = check.newer("v1.7.0-beta.3", CONSENSUS)
        self.assertEqual([release.tag for release in later], ["v1.7.0-beta.4"])

    def test_a_pin_missing_from_the_list_is_an_error(self):
        message = "the pinned release tests@v20.0.0 is not among the published releases"
        with self.assertRaisesRegex(LookupError, rf"\A{re.escape(message)}\Z"):
            check.newer("tests@v20.0.0", EXECUTION)


class Pins(unittest.TestCase):
    def test_pins_read_repositories_and_archives(self):
        sources = """
[repositories."ethereum/execution-specs"]
commit = "e27f097ec7b3e6e8ee9c2c1873c183e8f7da7a6e"
release = "tests@v21.0.2"

[repositories."ethereum/ssz-specs"]
commit = "7bce07ff7d51b1a3c66ff4e2bd3233ac248ede70"
release = "v0.1.0"

[archives."execution-specs/tests-bogota-devnet@v2.0.0/fixtures"]
repository = "ethereum/execution-specs"
release = "tests-bogota-devnet@v2.0.0"

[archives."consensus-specs/v1.7.0-alpha.12/general"]
repository = "ethereum/consensus-specs"
"""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "tests").mkdir()
            (root / "tests" / "sources.toml").write_text(sources)
            self.assertEqual(
                check.pins(root),
                [
                    ("ethereum/execution-specs", "tests-bogota-devnet@v2.0.0"),
                    ("ethereum/execution-specs", "tests@v21.0.2"),
                ],
            )

    def test_the_report_names_each_newer_release(self):
        lines = check.report(
            {
                ("ethereum/execution-specs", "tests@v21.0.1"): [EXECUTION[1]],
                ("ethereum/consensus-specs", "v1.7.0-beta.4"): [],
            }
        )
        self.assertEqual(
            lines,
            [
                "ethereum/consensus-specs: v1.7.0-beta.4 is the latest release of its line",
                "ethereum/execution-specs: tests@v21.0.1 is pinned; "
                "newer: tests@v21.0.2 (2026-10-26)",
            ],
        )


class NextFork(unittest.TestCase):
    def setUp(self):
        self.saved = check._get, check.holds
        check._get = lambda path: {"default_branch": "forks/bogota"}
        self.asked = []

    def tearDown(self):
        check._get, check.holds = self.saved

    def run_with(self, holding: set[str], found: dict) -> list[str]:
        """The report when exactly the refs `holding` hold the tests of the next fork."""

        def holds(repository, ref, directory):
            self.asked.append(ref)
            return ref in holding

        check.holds = holds
        return check.next_fork(found)

    def test_nothing_is_due_while_no_ref_holds_the_tests(self):
        found = {
            ("ethereum/execution-specs", "tests@v21.0.2"): [],
            ("ethereum/execution-specs", "tests-bogota-devnet@v1.1.1"): [EXECUTION[0]],
        }
        self.assertEqual(self.run_with(set(), found), [])
        # A devnet line never counts, since its tests stay on a devnet branch.
        self.assertEqual(self.asked, ["forks/bogota", "tests@v21.0.2"])

    def test_a_merge_into_the_fork_branch_is_reported(self):
        found = {("ethereum/execution-specs", "tests@v21.0.2"): []}
        self.assertEqual(
            self.run_with({"forks/bogota"}, found),
            [
                "ethereum/execution-specs: forks/bogota holds tests/bogota, "
                "so the rules of that fork are due"
            ],
        )

    def test_a_newer_stable_release_with_the_fork_is_reported(self):
        later = Release("tests@v22.0.0", "2026-11-20T00:00:00Z", False)
        found = {("ethereum/execution-specs", "tests@v21.0.2"): [later]}
        self.assertEqual(
            self.run_with({"tests@v22.0.0"}, found),
            [
                "ethereum/execution-specs: tests@v22.0.0 holds tests/bogota, "
                "so the rules of that fork are due"
            ],
        )


if __name__ == "__main__":
    unittest.main()
