"""Test the theorem baseline guard against commits in isolated Git repositories."""

import contextlib
import importlib.util
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "check_theorems_baseline", HERE / "check_theorems_baseline.py"
)
assert SPEC and SPEC.loader
guard = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(guard)

ONE = "EthLib.Base.Sample EthLib.Base.first\n"
TWO = "EthLib.Base.Sample EthLib.Base.second\n"
THREE = "EthLib.Base.Sample EthLib.Base.third\n"
MALFORMED = "1: expected a module and a declaration name"


class ParserTests(unittest.TestCase):
    def test_shared_parser_cases(self) -> None:
        cases = json.loads((HERE / "check_theorems_baseline_cases.json").read_text())
        for case in cases:
            with self.subTest(case=case["name"]):
                if "error" in case:
                    message = f"fixture:{case['error']}"
                    with self.assertRaisesRegex(guard.BaselineError, f"^{re.escape(message)}$"):
                        guard.entries(case["text"], "fixture")
                else:
                    expected = {tuple(entry) for entry in case["entries"]}
                    self.assertEqual(guard.entries(case["text"], "fixture"), expected)


class BaselineTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.path = self.root / guard.BASELINE
        self.git("init", "--quiet")
        (self.root / "README").write_text("Isolated baseline test.\n", encoding="utf-8")
        self.before = self.commit()
        self.write(ONE + TWO)
        self.base = self.commit()

    def git(self, *args: str) -> str:
        return subprocess.run(
            [
                "git",
                "-c",
                "user.name=Baseline Test",
                "-c",
                "user.email=baseline-test@example.invalid",
                "-c",
                "commit.gpgsign=false",
                "-c",
                "tag.gpgsign=false",
                "-c",
                "core.hooksPath=/dev/null",
                "-c",
                "core.excludesFile=/dev/null",
                "-c",
                "init.defaultBranch=baseline-fixture",
                *args,
            ],
            cwd=self.root,
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()

    def write(self, text: str) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.path.write_text(text, encoding="utf-8")

    def commit(self) -> str:
        self.git("add", ".")
        self.git("commit", "--quiet", "-m", "baseline fixture")
        return self.git("rev-parse", "HEAD")

    def run_main(self, *args: str) -> tuple[int, str, str]:
        output, errors = io.StringIO(), io.StringIO()
        with (
            mock.patch.object(guard, "ROOT", self.root),
            contextlib.redirect_stdout(output),
            contextlib.redirect_stderr(errors),
        ):
            status = guard.main(list(args))
        return status, output.getvalue(), errors.getvalue()

    def assert_error(self, base: str, message: str) -> None:
        """Check that the guard rejects this base with exactly this message."""
        with self.assertRaisesRegex(guard.BaselineError, f"^{re.escape(message)}$"):
            guard.check(self.root, base)

    def added(self, base: str) -> str:
        """Return the report line for the third entry added since this base."""
        return f"{guard.BASELINE}: entry added since {base}: EthLib.Base.Sample EthLib.Base.third"

    def workflow_command(self) -> str:
        lines = (HERE.parent / ".github/workflows/ci.yml").read_text().splitlines()
        start = lines.index("      - name: theorem baseline")
        stop = next(
            (i for i in range(start + 1, len(lines)) if lines[i].startswith("      - ")),
            len(lines),
        )
        step = lines[start:stop]
        self.assertIn("        shell: bash", step)
        self.assertIn(
            "          PUSH_BEFORE: "
            "${{ github.event_name == 'push' && github.event.before || '' }}",
            step,
        )
        body = step[step.index("        run: |") + 1 :]
        self.assertTrue(all(not line.strip() or line.startswith("          ") for line in body))
        return "\n".join(line[10:] for line in body) + "\n"

    def run_workflow(
        self, before: str, root: Path | None = None
    ) -> subprocess.CompletedProcess[str]:
        project = self.root if root is None else root
        script = project / "scripts/check_theorems_baseline.py"
        script.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(HERE / script.name, script)
        env = os.environ.copy()
        env["PUSH_BEFORE"] = before
        env["UV_OFFLINE"] = "1"
        env["PATH"] = str(Path(sys.executable).parent) + os.pathsep + env.get("PATH", "")
        with tempfile.TemporaryDirectory() as cache:
            env["UV_CACHE_DIR"] = cache
            return subprocess.run(
                ["bash", "-e", "-o", "pipefail", "-c", self.workflow_command()],
                cwd=project,
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )

    def test_unchanged_baseline_passes(self) -> None:
        self.assertEqual(guard.check(self.root, self.base), [])

    def test_deleting_entries_passes(self) -> None:
        self.write(ONE)
        self.assertEqual(guard.check(self.root, self.base), [])
        self.write("")
        self.assertEqual(guard.check(self.root, self.base), [])

    def test_order_comments_and_whitespace_do_not_add_entries(self) -> None:
        self.write("# The same two entries.\n\n" + TWO + "\t" + ONE.replace(" ", "\t") + "# End.\n")
        self.assertEqual(guard.check(self.root, self.base), [])

    def test_an_added_entry_fails(self) -> None:
        self.write(ONE + TWO + THREE)
        self.assertEqual(guard.check(self.root, self.base), [self.added(self.base)])
        status, output, errors = self.run_main("--base", self.base)
        self.assertEqual(status, 1)
        self.assertEqual(
            output, self.added(self.base) + "\ncheck-theorems-baseline: added entries: 1\n"
        )
        self.assertEqual(errors, "")

    def test_renaming_an_entry_also_fails(self) -> None:
        self.write(ONE + THREE)
        self.assertEqual(guard.check(self.root, self.base), [self.added(self.base)])

    def test_adding_to_an_empty_existing_baseline_fails(self) -> None:
        self.write("# Empty baseline.\n")
        empty = self.commit()
        self.write(THREE)
        self.assertEqual(guard.check(self.root, empty), [self.added(empty)])

    def test_first_creation_is_allowed_and_reported(self) -> None:
        self.write(ONE + TWO + THREE)
        self.assertEqual(guard.check(self.root, self.before), [])
        status, output, errors = self.run_main("--base", self.before)
        self.assertEqual(status, 0)
        self.assertEqual(
            output,
            "check-theorems-baseline: initial baseline creation allowed "
            f"(no baseline at {self.before})\n",
        )
        self.assertEqual(errors, "")

    def test_deleting_an_existing_baseline_fails(self) -> None:
        self.path.unlink()
        message = f"{guard.BASELINE}: missing from the working tree but present at {self.base}"
        self.assert_error(self.base, message)
        status, output, errors = self.run_main("--base", self.base)
        self.assertEqual(status, 2)
        self.assertEqual(output, "")
        self.assertEqual(errors, f"check-theorems-baseline: {message}\n")

    def test_missing_baseline_at_both_revisions_passes(self) -> None:
        self.path.unlink()
        status, output, errors = self.run_main("--base", self.before)
        self.assertEqual(status, 0)
        self.assertEqual(output, f"check-theorems-baseline: no entries added since {self.before}\n")
        self.assertEqual(errors, "")

    def test_current_baseline_must_be_a_file(self) -> None:
        self.path.unlink()
        self.path.mkdir()
        self.assert_error(self.base, f"{self.path}: expected a regular file")

    def test_current_baseline_must_not_be_a_symlink(self) -> None:
        (self.root / "contents.txt").write_text(ONE + TWO, encoding="utf-8")
        self.path.unlink()
        self.path.symlink_to("../contents.txt")
        self.assert_error(self.base, f"{self.path}: expected a regular file")

    def test_base_baseline_must_be_a_regular_file(self) -> None:
        self.path.unlink()
        self.path.mkdir()
        child = self.path / "entry"
        child.write_text(ONE, encoding="utf-8")
        directory_base = self.commit()
        child.unlink()
        self.path.rmdir()
        self.write(ONE)
        self.assert_error(
            directory_base, f"{guard.BASELINE} at {directory_base}: expected a regular file"
        )

    def test_base_baseline_must_not_be_a_symlink(self) -> None:
        (self.root / "contents.txt").write_text(ONE, encoding="utf-8")
        self.path.unlink()
        self.path.symlink_to("../contents.txt")
        link_base = self.commit()
        self.path.unlink()
        self.write(ONE)
        self.assert_error(link_base, f"{guard.BASELINE} at {link_base}: expected a regular file")

    def test_executable_base_baseline_is_compared(self) -> None:
        self.path.chmod(0o755)
        executable_base = self.commit()
        self.assertEqual(
            self.git("ls-tree", executable_base, "--", guard.BASELINE.as_posix()).split()[0],
            "100755",
        )
        self.write(ONE + TWO + THREE)
        self.assertEqual(guard.check(self.root, executable_base), [self.added(executable_base)])

    def test_current_baseline_must_be_utf8(self) -> None:
        self.path.write_bytes(b"\xff")
        self.assert_error(
            self.base,
            f"{self.path}: 'utf-8' codec can't decode byte 0xff in position 0: invalid start byte",
        )

    def test_malformed_current_baseline_fails_even_on_first_creation(self) -> None:
        for text in ("one_column\n", ONE.rstrip() + " extra\n"):
            with self.subTest(text=text):
                self.write(text)
                self.assert_error(self.base, f"{guard.BASELINE}:{MALFORMED}")
                self.assert_error(self.before, f"{guard.BASELINE}:{MALFORMED}")

    def test_duplicate_current_entries_fail(self) -> None:
        self.write(ONE + ONE)
        self.assert_error(self.base, f"{guard.BASELINE}:2: duplicate baseline entry")

    def test_carriage_returns_do_not_split_lines_in_either_revision(self) -> None:
        self.write(ONE.replace("\n", "\r") + TWO)
        self.assert_error(self.base, f"{guard.BASELINE}:{MALFORMED}")
        bad_base = self.commit()
        self.write(ONE)
        self.assert_error(bad_base, f"{guard.BASELINE} at {bad_base}:{MALFORMED}")

    def test_malformed_base_baseline_fails(self) -> None:
        self.write("one_column\n")
        bad_base = self.commit()
        self.write(ONE)
        self.assert_error(bad_base, f"{guard.BASELINE} at {bad_base}:{MALFORMED}")

    def test_duplicate_base_entries_fail(self) -> None:
        self.write(ONE + ONE)
        bad_base = self.commit()
        self.write(ONE)
        self.assert_error(bad_base, f"{guard.BASELINE} at {bad_base}:2: duplicate baseline entry")

    def test_empty_base_reference_fails(self) -> None:
        self.assert_error("", "the base revision must name a commit")

    def test_invalid_base_references_fail(self) -> None:
        for base in ("does-not-exist", "--help"):
            with self.subTest(base=base):
                self.assert_error(
                    base, f"invalid base revision {base!r}: fatal: Needed a single revision"
                )
        blob = self.git("hash-object", str(self.path))
        self.assert_error(
            blob,
            f"invalid base revision {blob!r}: error: {blob}^{{commit}}: expected commit type, "
            "but the object dereferences to blob type\nfatal: Needed a single revision",
        )

    def test_named_commit_reference_passes(self) -> None:
        self.git("tag", "baseline-snapshot", self.base)
        self.assertEqual(guard.check(self.root, "baseline-snapshot"), [])

    def test_cli_reports_errors(self) -> None:
        self.write("broken\n")
        status, output, errors = self.run_main("--base", self.base)
        self.assertEqual(status, 2)
        self.assertEqual(output, "")
        self.assertEqual(errors, f"check-theorems-baseline: {guard.BASELINE}:{MALFORMED}\n")

    def test_cli_requires_a_base(self) -> None:
        errors = io.StringIO()
        with contextlib.redirect_stderr(errors), self.assertRaises(SystemExit) as error:
            guard.main([])
        self.assertEqual(error.exception.code, 2)
        self.assertEqual(
            errors.getvalue(),
            "usage: check-theorems-baseline [-h] --base BASE\n"
            "check-theorems-baseline: error: the following arguments are required: --base\n",
        )

    def test_ci_checks_the_whole_push(self) -> None:
        self.write(ONE + TWO + THREE)
        self.commit()
        (self.root / "README").write_text("An unrelated final commit.\n", encoding="utf-8")
        self.commit()
        self.assertEqual(guard.check(self.root, "HEAD^1"), [])
        result = self.run_workflow(self.base)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertEqual(
            result.stdout, self.added(self.base) + "\ncheck-theorems-baseline: added entries: 1\n"
        )

    def test_ci_pull_request_checks_the_merge_first_parent(self) -> None:
        self.git("checkout", "--quiet", "-b", "proposal")
        self.write(ONE + TWO + THREE)
        self.commit()
        self.git("checkout", "--quiet", "-b", "target", self.base)
        self.git("merge", "--quiet", "--no-ff", "-m", "Merge proposal", "proposal")
        result = self.run_workflow("")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertEqual(
            result.stdout, self.added("HEAD^1") + "\ncheck-theorems-baseline: added entries: 1\n"
        )

    def test_ci_new_branch_uses_the_first_parent(self) -> None:
        (self.root / "README").write_text("A newly created branch.\n", encoding="utf-8")
        self.commit()
        result = self.run_workflow("0" * 40)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "check-theorems-baseline: no entries added since HEAD^1\n")

    def test_ci_fetches_a_before_commit_outside_the_shallow_clone(self) -> None:
        self.write(ONE + TWO + THREE)
        self.commit()
        (self.root / "README").write_text("An unrelated final commit.\n", encoding="utf-8")
        self.commit()
        clone = self.root / "shallow"
        self.git(
            "-c",
            "protocol.file.allow=always",
            "clone",
            "--quiet",
            "--depth=2",
            self.root.as_uri(),
            str(clone),
        )
        subprocess.run(["git", "config", "protocol.file.allow", "always"], cwd=clone, check=True)
        missing = subprocess.run(
            ["git", "cat-file", "-e", f"{self.base}^{{commit}}"],
            cwd=clone,
            capture_output=True,
            check=False,
        )
        self.assertNotEqual(missing.returncode, 0)
        result = self.run_workflow(self.base, clone)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertEqual(
            result.stdout, self.added(self.base) + "\ncheck-theorems-baseline: added entries: 1\n"
        )
        subprocess.run(["git", "cat-file", "-e", f"{self.base}^{{commit}}"], cwd=clone, check=True)

    def test_ci_stops_when_the_before_commit_cannot_be_fetched(self) -> None:
        remote = self.root / "missing-remote.git"
        self.git("remote", "add", "origin", str(remote))
        result = self.run_workflow("f" * 40)
        self.assertEqual(result.returncode, 128, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "")
        self.assertEqual(
            result.stderr.splitlines()[0],
            f"fatal: '{remote}' does not appear to be a git repository",
        )


if __name__ == "__main__":
    unittest.main()
