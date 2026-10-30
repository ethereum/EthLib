"""Exercise CI timing and cache commands against a small native Lean library."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile
import unittest

from ruamel.yaml import YAML

from module_times import parse_logs


ROOT = Path(__file__).resolve().parent.parent


class BuildPipelineTests(unittest.TestCase):
    def setUp(self):
        self.work = tempfile.TemporaryDirectory()
        self.addCleanup(self.work.cleanup)
        self.root = Path(self.work.name)
        self.project = self.root / "project"
        self.project.mkdir()
        self.logs = self.root / "logs"
        self.logs.mkdir()
        self.build = self.project / ".lake" / "build"
        self.module = "EthLib.Exports.Probe"
        self.source = self.project / "EthLib" / "Exports" / "Probe.lean"
        self.source.parent.mkdir(parents=True)
        shutil.copyfile(ROOT / "lean-toolchain", self.project / "lean-toolchain")
        # Run the workflow's commands with the real production scripts.
        (self.project / "scripts").symlink_to(ROOT / "scripts", target_is_directory=True)
        (self.project / "lakefile.toml").write_text(
            'name = "BuildPipelineTest"\n'
            'defaultTargets = ["Exports"]\n'
            '[[lean_lib]]\nname = "Exports"\n'
            'roots = ["EthLib.Exports"]\n'
            'requiresModuleSystem = true\nprecompileModules = true\n'
        )
        (self.project / "EthLib" / "Exports.lean").write_text(
            "module\npublic import EthLib.Exports.Probe\n"
        )
        self.write_export(1)
        with (ROOT / ".github" / "workflows" / "ci.yml").open() as handle:
            self.steps = YAML(typ="safe").load(handle)["jobs"]["build"]["steps"]
        # Keep fixture measurements and summaries apart from the hosting workflow's files.
        self.env = {key: value for key, value in os.environ.items()
                    if not key.startswith("BUILD_TIMING_")}
        self.env.update(
            BUILD_TIMING_LOG_DIR=str(self.logs),
            BUILD_TIMING_RESULTS=str(self.logs / "results.jsonl"),
            GITHUB_SHA="a" * 40,
            GITHUB_STEP_SUMMARY=str(self.root / "summary.md"),
            LEAN_NUM_THREADS="2",
        )

    def write_export(self, value):
        self.source.write_text(
            "module\n"
            "@[export ethlib_timing_probe]\n"
            f"public def probe (_ : Unit) : UInt64 := {value}\n"
        )

    def run_command(self, args):
        run = subprocess.run(args, cwd=self.project, env=self.env,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        self.assertEqual(run.returncode, 0, run.stdout)
        return run.stdout

    def step(self, name):
        matches = [step for step in self.steps if step.get("name") == name]
        self.assertEqual(len(matches), 1, f"Missing or repeated CI step: {name}")
        return matches[0]

    def run_step(self, name):
        return self.run_command(["bash", "-euo", "pipefail", "-c", self.step(name)["run"]])

    def test_export_only_edit_is_reported_before_the_cached_proof_build(self):
        baseline_log = self.logs / "baseline.log"
        baseline_log.write_text(self.run_command(["lake", "build", "--wfail", "Exports"]))
        baseline = {"schema_version": 1, "commit": None, "modules": parse_logs([baseline_log])}
        self.assertIn(self.module, baseline["modules"])
        (self.build / "ethlib-module-times.json").write_text(json.dumps(baseline))
        self.run_step("keep earlier module times")

        # Change executable export code while the specification and proofs stay untouched.
        self.assertLess(self.steps.index(self.step("exports")), self.steps.index(self.step("bindings")))
        self.write_export(2)
        self.run_step("exports")
        self.run_step("proofs")
        samples = parse_logs([self.logs / "exports_build.log"])
        self.assertIn(self.module, samples)
        self.assertNotIn(self.module, parse_logs([self.logs / "proofs_build.log"]))

        self.run_step("build timing report")
        report = (self.logs / "report.md").read_text()
        self.assertIn("| Exports build |", report)
        self.assertIn("`EthLib/Exports/Probe.lean`", report)
        row = next(line for line in report.splitlines() if "`EthLib/Exports/Probe.lean`" in line)
        self.assertNotEqual(row.split("|")[2].strip(), "-")
        table = json.loads((self.logs / "module-times.json").read_text())
        self.assertEqual(table["modules"][self.module], samples[self.module])

    def test_saved_parent_archive_excludes_setup_files_and_restores_a_warm_build(self):
        self.run_command(["lake", "build", "--wfail", "Exports"])
        # Include nested paths, spaces, and a dangling setup-file symlink.
        nested = self.build / "ir" / "a directory"
        nested.mkdir(parents=True)
        setup = nested / "Probe.setup.json"
        setup.write_text('{"path":"/another/runner/EthLib/.lake/build"}')
        (nested / "Link.setup.json").symlink_to("/another/runner/missing.setup.json")
        (self.build / "ethlib-module-times.json").write_text(
            json.dumps({"schema_version": 1, "commit": None, "modules": {}})
        )
        keep = nested / "ordinary.json"
        keep.write_text("{}")

        # Run cleanup only if the workflow actually wires it before cache/save.
        save = self.step("save EthLib build")
        prepare = [step for step in self.steps if step.get("name") == "prepare EthLib cache"]
        if prepare:
            self.assertEqual(self.steps.index(prepare[0]) + 1, self.steps.index(save))
            self.assertEqual(prepare[0]["if"], save["if"])
            self.run_step("prepare EthLib cache")
        paths = save["with"]["path"].splitlines()
        self.assertIn(".lake/build", paths)
        self.assertEqual(self.step("restore EthLib build")["with"]["path"], save["with"]["path"])

        # cacheUtils.resolvePaths returns the parent directory; tar recurses into it.
        archive = self.root / "cache.tar"
        self.run_command(["tar", "-cf", str(archive), "--", ".lake/build"])
        with tarfile.open(archive) as saved:
            names = saved.getnames()
        self.assertEqual([name for name in names if name.endswith(".setup.json")], [])
        self.assertIn(".lake/build/lib/lean/EthLib/Exports/Probe.olean.private", names)
        self.assertIn(".lake/build/ir/EthLib/Exports/Probe.c.o.export", names)
        self.assertIn(".lake/build/ethlib-module-times.json", names)
        self.assertIn(".lake/build/ir/a directory/ordinary.json", names)

        # Restoring the saved payload must retain Lake's content-hash cache hits.
        shutil.rmtree(self.build)
        self.run_command(["tar", "-xf", str(archive)])
        output = self.run_command(["lake", "--no-build", "build", "--wfail", "Exports"])
        self.assertIn("All targets up-to-date", output)


if __name__ == "__main__":
    unittest.main()
