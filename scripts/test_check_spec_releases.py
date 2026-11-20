"""Tests of `check_spec_releases.py` on release lists and source files written here."""

import contextlib
import importlib.util
import io
import re
import tempfile
import unittest
from pathlib import Path
from unittest import mock

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


# The download URL of an asset of a consensus-specs release.
DOWNLOAD = "https://github.com/ethereum/consensus-specs/releases/download/v1.7.0-beta.4/{}"
# The end of the line that names an unplaced asset.
UNPLACED = "which tests/sources.toml neither pins in archives nor declares in unread_assets"


class Assets(unittest.TestCase):
    def test_assets_are_the_download_urls_of_the_release(self):
        asked = []

        def get(path):
            asked.append(path)
            return {
                "assets": [{"browser_download_url": "https://a"}, {"browser_download_url": "b"}]
            }

        with mock.patch.object(check, "_get", get):
            self.assertEqual(
                check.assets("ethereum/execution-specs", "tests@v21.0.2"), ["https://a", "b"]
            )
        # The tag is quoted, since `@` is not part of a path segment of the API.
        self.assertEqual(asked, ["repos/ethereum/execution-specs/releases/tags/tests%40v21.0.2"])

    def test_placed_assets_are_the_archives_and_the_declared_ones(self):
        sources = f"""
[archives."consensus-specs/v1.7.0-beta.4/mainnet"]
repository = "ethereum/consensus-specs"
url = "{DOWNLOAD.format("mainnet.tar.gz")}"

[unread_assets]
"{DOWNLOAD.format("comptests.tar.gz")}" = "Its runner is planned"
"""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "tests").mkdir()
            (root / "tests" / "sources.toml").write_text(sources)
            self.assertEqual(
                check.placed(root),
                {DOWNLOAD.format("mainnet.tar.gz"), DOWNLOAD.format("comptests.tar.gz")},
            )

    def test_every_unplaced_asset_is_named_once_in_order(self):
        names = ["mainnet.tar.gz", "minimal.tar.gz", "general.tar.gz", "comptests.tar.gz"]
        devnet = "https://github.com/ethereum/execution-specs/releases/download/x/extra.tar.gz"
        # The pins come in reverse order, and one unplaced asset is listed twice.
        found = {
            ("ethereum/execution-specs", "x"): [devnet],
            ("ethereum/consensus-specs", "v1.7.0-beta.4"): [
                *(DOWNLOAD.format(name) for name in names),
                DOWNLOAD.format("general.tar.gz"),
            ],
        }
        known = {DOWNLOAD.format("mainnet.tar.gz"), DOWNLOAD.format("minimal.tar.gz")}
        lines = [
            f"ethereum/consensus-specs: v1.7.0-beta.4 has the asset {DOWNLOAD.format(name)}, "
            f"{UNPLACED}"
            for name in ("comptests.tar.gz", "general.tar.gz")
        ]
        lines.append(f"ethereum/execution-specs: x has the asset {devnet}, {UNPLACED}")
        self.assertEqual(check.unplaced(found, known), lines)

    def test_placed_assets_give_no_line(self):
        urls = [DOWNLOAD.format("mainnet.tar.gz")]
        found = {("ethereum/consensus-specs", "v1.7.0-beta.4"): urls}
        self.assertEqual(check.unplaced(found, set(urls)), [])


class Main(unittest.TestCase):
    def run_main(self, placed: set[str], fork: tuple[str, ...] = ()) -> tuple[int, list[str]]:
        """The exit code and the printed lines of a run over one pin with two assets."""
        pin = ("ethereum/consensus-specs", "v1.7.0-beta.4")
        printed = io.StringIO()
        with (
            mock.patch.object(check, "pins", lambda: [pin]),
            mock.patch.object(check, "releases", lambda repository: CONSENSUS),
            mock.patch.object(
                check, "assets", lambda repository, tag: [DOWNLOAD.format(n) for n in "ab"]
            ),
            mock.patch.object(check, "placed", lambda: placed),
            mock.patch.object(check, "next_fork", lambda found: list(fork)),
            contextlib.redirect_stdout(printed),
        ):
            code = check.main()
        return code, printed.getvalue().splitlines()

    def test_an_unplaced_asset_fails_the_run_and_is_named(self):
        code, lines = self.run_main({DOWNLOAD.format("a")})
        self.assertEqual(code, 1)
        self.assertEqual(
            lines,
            [
                "ethereum/consensus-specs: v1.7.0-beta.4 is the latest release of its line",
                f"ethereum/consensus-specs: v1.7.0-beta.4 has the asset {DOWNLOAD.format('b')}, "
                f"{UNPLACED}",
            ],
        )

    def test_the_next_fork_fails_the_run_after_the_assets(self):
        fork = "ethereum/execution-specs: forks/bogota holds tests/bogota"
        code, lines = self.run_main({DOWNLOAD.format("a")}, (fork,))
        self.assertEqual(code, 1)
        self.assertEqual(
            lines,
            [
                "ethereum/consensus-specs: v1.7.0-beta.4 is the latest release of its line",
                f"ethereum/consensus-specs: v1.7.0-beta.4 has the asset {DOWNLOAD.format('b')}, "
                f"{UNPLACED}",
                fork,
            ],
        )
        code, lines = self.run_main({DOWNLOAD.format(n) for n in "ab"}, (fork,))
        self.assertEqual((code, lines[1:]), (1, [fork]))

    def test_placed_assets_pass(self):
        code, lines = self.run_main({DOWNLOAD.format(n) for n in "ab"})
        self.assertEqual(code, 0)
        self.assertEqual(
            lines, ["ethereum/consensus-specs: v1.7.0-beta.4 is the latest release of its line"]
        )


class NextFork(unittest.TestCase):
    def setUp(self):
        self.asked = []

    def run_with(self, holding: set[str], found: dict) -> list[str]:
        """The report when exactly the refs `holding` hold the tests of the next fork."""

        def holds(repository, ref, directory):
            self.asked.append(ref)
            return ref in holding

        with (
            mock.patch.object(check, "_get", lambda path: {"default_branch": "forks/bogota"}),
            mock.patch.object(check, "holds", holds),
        ):
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
