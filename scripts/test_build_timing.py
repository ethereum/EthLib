"""Check timing attribution, incremental samples, and command failure reporting."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from module_times import empty_table, load_table, parse_logs, update_table


ROOT = Path(__file__).resolve().parent.parent
REPORT = ROOT / "scripts" / "build_timing_report.sh"


class BuildTimingTests(unittest.TestCase):
    def setUp(self):
        self.work = tempfile.TemporaryDirectory()
        self.addCleanup(self.work.cleanup)
        self.root = Path(self.work.name)
        self.log = self.root / "library_build.log"
        self.log.write_text(
            "✔ [1/8] Built EthLib.Fast (1.0s)\n"
            "⚠ [2/8] Built EthLib.Proofs.Slow (12s)\n"
            "✔ [3/8] Built EthLib.New (850ms)\n"
            "✔ [4/8] Built EthLib.Fast:c.o (3.0s)\n"
            "✔ [5/8] Built Mathlib.Other (22s)\n"
            "✔ [6/8] Replayed EthLib.Cached (4.0s)\n"
            "✔ [7/8] Built CheckDeclsTest.Bad (2.0s)\n"
            "✖ [8/8] Building EthLib.Failed (7.0s)\n"
            "✔ [9/9] Built EthLib.Fast (9.9s)\n",
            encoding="utf-8",
        )
        for module in ("Fast", "Proofs/Slow", "New", "Kept"):
            source = self.root / "EthLib" / f"{module}.lean"
            source.parent.mkdir(parents=True, exist_ok=True)
            source.touch()
        self.base = {
            "schema_version": 1,
            "commit": "a" * 40,
            "modules": {
                "EthLib.Fast": {"seconds": 2.0, "decimals": 1},
                "EthLib.Proofs.Slow": {"seconds": 18.0, "decimals": 0},
                "EthLib.Kept": {"seconds": 30.0, "decimals": 0},
                "EthLib.Gone": {"seconds": 5.0, "decimals": 0},
            },
        }

    def render(self, *rows):
        results = self.root / "results.jsonl"
        results.write_text("".join(json.dumps(row) + "\n" for row in rows))
        # The tests must work under the workflow's exported timing paths too.
        env = {key: value for key, value in os.environ.items()
               if not key.startswith("BUILD_TIMING_")}
        env.update(BUILD_TIMING_LOG_DIR=str(self.root),
                   BUILD_TIMING_SOURCE_BRANCH="feature|<timing>")
        return subprocess.check_output(
            ["bash", str(REPORT), "render", str(results)], cwd=ROOT, env=env, text=True
        )

    def test_only_completed_package_elaboration_is_counted(self):
        self.assertEqual(parse_logs([self.log, self.root / "absent.log"]), {
            "EthLib.Fast": {"seconds": 1.0, "decimals": 1},
            "EthLib.Proofs.Slow": {"seconds": 12.0, "decimals": 0},
            "EthLib.New": {"seconds": 0.85, "decimals": 3},
        })

    def test_overlay_keeps_cached_samples_and_removes_deleted_sources(self):
        result = update_table(self.base, parse_logs([self.log]), "b" * 40, self.root)
        self.assertEqual(result["commit"], "b" * 40)
        self.assertNotIn("EthLib.Gone", result["modules"])
        self.assertEqual(result["modules"]["EthLib.Kept"], self.base["modules"]["EthLib.Kept"])
        self.assertEqual(result["modules"]["EthLib.Fast"]["seconds"], 1.0)

    def test_missing_and_unrecognized_tables_have_no_baseline(self):
        table = self.root / "table.json"
        self.assertIsNone(load_table(table))
        for text in ("{broken", '{"schema_version":99,"modules":{}}', "[]"):
            table.write_text(text)
            self.assertIsNone(load_table(table))
        self.assertEqual(update_table(empty_table(), {}, None, self.root)["modules"], {})

    def test_damaged_samples_discard_the_baseline(self):
        table = self.root / "table.json"
        for entry in (None, {}, {"seconds": -1, "decimals": 1},
                      {"seconds": float("nan"), "decimals": 1},
                      {"seconds": 1, "decimals": "1"}):
            data = {"schema_version": 1, "commit": None, "modules": {"EthLib.Bad": entry}}
            table.write_text(json.dumps(data))
            self.assertIsNone(load_table(table))

    def test_report_compares_the_same_rebuilt_modules(self):
        (self.root / "module-times-base.json").write_text(json.dumps(self.base))
        table = update_table(self.base, parse_logs([self.log]), "b" * 40, self.root)
        (self.root / "module-times.json").write_text(json.dumps(table))
        report = self.render({"label": "proofs_build", "real": 90.0,
                              "user": 70.0, "sys": 10.0, "exit_code": 0})
        self.assertIn("| Proofs build | 90.00 | 80.00 | ok |", report)
        self.assertIn("Rebuilt 3 modules (1 without an earlier time)", report)
        self.assertIn("13s here against 20s", report)
        self.assertIn("| 0.850 | - | - | `EthLib/New.lean` |", report)
        self.assertIn("feature|&lt;timing&gt;", report)
        self.assertNotIn("Mathlib.Other", report)

    def test_missing_data_and_failed_build_do_not_claim_a_cache_hit(self):
        self.assertIn("No timing data was captured", self.render())
        self.log.write_text("")
        report = self.render({"label": "library_build", "real": 1.0,
                              "user": 0.5, "sys": 0.1, "exit_code": 7})
        self.assertIn("exit 7", report)
        self.assertIn("No completed EthLib module builds were captured", report)
        self.assertNotIn("every module was already up to date", report)

    def test_command_exit_code_and_output_survive_tee(self):
        results = self.root / "run.jsonl"
        run = subprocess.run(
            ["bash", str(REPORT), "run", "library_build", str(results), "--",
             "bash", "-c", "echo diagnostic; exit 7"],
            env={**os.environ, "BUILD_TIMING_LOG_DIR": str(self.root)},
            capture_output=True, text=True,
        )
        self.assertEqual(run.returncode, 7)
        self.assertIn("diagnostic", run.stdout)
        self.assertIn("diagnostic", self.log.read_text())
        self.assertEqual(json.loads(results.read_text())["exit_code"], 7)

    def test_invalid_label_is_rejected_before_execution(self):
        marker = self.root / "should-not-exist"
        run = subprocess.run(
            ["bash", str(REPORT), "run", "../outside", str(self.root / "run.jsonl"),
             "--", "touch", str(marker)], capture_output=True,
        )
        self.assertEqual(run.returncode, 2)
        self.assertFalse(marker.exists())

    def test_unavailable_command_is_recorded_as_a_failure(self):
        results = self.root / "run.jsonl"
        run = subprocess.run(
            ["bash", str(REPORT), "run", "library_build", str(results), "--",
             str(self.root / "absent-command")], capture_output=True,
        )
        self.assertNotEqual(run.returncode, 0)
        self.assertEqual(json.loads(results.read_text())["exit_code"], run.returncode)

    def test_missing_measurement_does_not_report_zero_time(self):
        report = self.render({"label": "declarations", "real": 0,
                              "user": 0, "sys": 0, "exit_code": 127, "measured": False})
        self.assertIn("| Declaration check | n/a | n/a | measurement failed (exit 127) |", report)


if __name__ == "__main__":
    unittest.main()
