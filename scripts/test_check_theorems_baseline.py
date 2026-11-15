"""Test the theorem baseline guard against commits in isolated Git repositories."""

import contextlib
import importlib.util
import io
import os
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


class BaselineTests(unittest.TestCase):
    def setUp(self):
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

    def test_unchanged_baseline_passes(self):
        self.assertEqual(guard.check(self.root, self.base), [])

    def test_deleting_entries_passes(self):
        self.write(ONE)
        self.assertEqual(guard.check(self.root, self.base), [])
        self.write("")
        self.assertEqual(guard.check(self.root, self.base), [])

    def test_order_comments_and_whitespace_do_not_add_entries(self):
        self.write("# The same two entries.\n\n" + TWO + "\t" + ONE.replace(" ", "\t") + "# End.\n")
        self.assertEqual(guard.check(self.root, self.base), [])

    def test_an_added_entry_fails(self):
        self.write(ONE + TWO + THREE)
        self.assertEqual(
            guard.check(self.root, self.base),
            [
                f"{guard.BASELINE}: entry added since {self.base}: "
                "EthLib.Base.Sample EthLib.Base.third"
            ],
        )
        status, output, errors = self.run_main("--base", self.base)
        self.assertEqual(status, 1)
        self.assertIn("added entries: 1", output)
        self.assertEqual(errors, "")

    def test_renaming_an_entry_also_fails(self):
        self.write(ONE + THREE)
        self.assertEqual(len(guard.check(self.root, self.base)), 1)

    def test_adding_to_an_empty_existing_baseline_fails(self):
        self.write("# Empty baseline.\n")
        empty = self.commit()
        self.write(THREE)
        self.assertEqual(len(guard.check(self.root, empty)), 1)

    def test_first_creation_is_allowed_and_reported(self):
        self.write(ONE + TWO + THREE)
        self.assertEqual(guard.check(self.root, self.before), [])
        status, output, errors = self.run_main("--base", self.before)
        self.assertEqual(status, 0)
        self.assertIn("initial baseline creation allowed", output)
        self.assertEqual(errors, "")

    def test_missing_current_baseline_is_empty(self):
        self.path.unlink()
        self.assertEqual(guard.check(self.root, self.base), [])

    def test_missing_baseline_at_both_revisions_passes(self):
        self.path.unlink()
        status, output, errors = self.run_main("--base", self.before)
        self.assertEqual(status, 0)
        self.assertIn("no entries added", output)
        self.assertNotIn("initial baseline creation", output)
        self.assertEqual(errors, "")

    def test_current_baseline_must_be_a_file(self):
        self.path.unlink()
        self.path.mkdir()
        with self.assertRaisesRegex(guard.BaselineError, "check_theorems_baseline.txt"):
            guard.check(self.root, self.base)

    def test_current_baseline_must_not_be_a_symlink(self):
        (self.root / "contents.txt").write_text(ONE + TWO, encoding="utf-8")
        self.path.unlink()
        self.path.symlink_to("../contents.txt")
        with self.assertRaisesRegex(guard.BaselineError, "expected a regular file"):
            guard.check(self.root, self.base)

    def test_base_baseline_must_be_a_regular_file(self):
        self.path.unlink()
        self.path.mkdir()
        child = self.path / "entry"
        child.write_text(ONE, encoding="utf-8")
        directory_base = self.commit()
        child.unlink()
        self.path.rmdir()
        self.write(ONE)
        with self.assertRaisesRegex(guard.BaselineError, "expected a regular file"):
            guard.check(self.root, directory_base)

    def test_current_baseline_must_be_utf8(self):
        self.path.write_bytes(b"\xff")
        with self.assertRaises(guard.BaselineError):
            guard.check(self.root, self.base)

    def test_malformed_current_baseline_fails_even_on_first_creation(self):
        for text in ("one_column\n", ONE.rstrip() + " extra\n"):
            with self.subTest(text=text):
                self.write(text)
                with self.assertRaisesRegex(guard.BaselineError, "expected a module"):
                    guard.check(self.root, self.base)
                with self.assertRaisesRegex(guard.BaselineError, "expected a module"):
                    guard.check(self.root, self.before)

    def test_duplicate_current_entries_fail(self):
        self.write(ONE + ONE)
        with self.assertRaisesRegex(guard.BaselineError, "duplicate baseline entry"):
            guard.check(self.root, self.base)

    def test_malformed_base_baseline_fails(self):
        self.write("one_column\n")
        bad_base = self.commit()
        self.write(ONE)
        with self.assertRaisesRegex(guard.BaselineError, "at .*:1: expected a module"):
            guard.check(self.root, bad_base)

    def test_duplicate_base_entries_fail(self):
        self.write(ONE + ONE)
        bad_base = self.commit()
        self.write(ONE)
        with self.assertRaisesRegex(guard.BaselineError, "duplicate baseline entry"):
            guard.check(self.root, bad_base)

    def test_invalid_base_references_fail(self):
        for base in ("", "does-not-exist", "--help"):
            with self.subTest(base=base), self.assertRaises(guard.BaselineError):
                guard.check(self.root, base)
        blob = self.git("hash-object", str(self.path))
        with self.assertRaisesRegex(guard.BaselineError, "invalid base revision"):
            guard.check(self.root, blob)

    def test_named_commit_reference_passes(self):
        self.git("tag", "baseline-snapshot", self.base)
        self.assertEqual(guard.check(self.root, "baseline-snapshot"), [])

    def test_cli_reports_errors(self):
        self.write("broken\n")
        status, output, errors = self.run_main("--base", self.base)
        self.assertEqual(status, 2)
        self.assertEqual(output, "")
        self.assertIn("check-theorems-baseline:", errors)

    def test_cli_requires_a_base(self):
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as error:
            guard.main([])
        self.assertEqual(error.exception.code, 2)

    def test_ci_checks_the_whole_push(self):
        self.write(ONE + TWO + THREE)
        self.commit()
        (self.root / "README").write_text("An unrelated final commit.\n", encoding="utf-8")
        self.commit()
        self.assertEqual(guard.check(self.root, "HEAD^1"), [])
        result = self.run_workflow(self.base)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn(f"entry added since {self.base}", result.stdout)

    def test_ci_pull_request_checks_the_merge_first_parent(self):
        self.git("checkout", "--quiet", "-b", "proposal")
        self.write(ONE + TWO + THREE)
        self.commit()
        self.git("checkout", "--quiet", "-b", "target", self.base)
        self.git("merge", "--quiet", "--no-ff", "-m", "Merge proposal", "proposal")
        result = self.run_workflow("")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("entry added since HEAD^1", result.stdout)

    def test_ci_new_branch_uses_the_first_parent(self):
        (self.root / "README").write_text("A newly created branch.\n", encoding="utf-8")
        self.commit()
        result = self.run_workflow("0" * 40)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("no entries added since HEAD^1", result.stdout)

    def test_ci_fetches_a_before_commit_outside_the_shallow_clone(self):
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
        self.assertIn(f"entry added since {self.base}", result.stdout)
        subprocess.run(["git", "cat-file", "-e", f"{self.base}^{{commit}}"], cwd=clone, check=True)

    def test_ci_stops_when_the_before_commit_cannot_be_fetched(self):
        self.git("remote", "add", "origin", str(self.root / "missing-remote.git"))
        result = self.run_workflow("f" * 40)
        self.assertNotEqual(result.returncode, 0)
        self.assertNotIn("check-theorems-baseline:", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
