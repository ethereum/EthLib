"""Check the native build's runtime import selection."""

import ast
import json
import os
import re
import tempfile
import unittest
from collections.abc import Sequence
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent.parent


class SetupRuntimeTests(unittest.TestCase):
    def setUp(self) -> None:
        self.work = tempfile.TemporaryDirectory()
        self.addCleanup(self.work.cleanup)
        self.root = Path(self.work.name)
        self.ir = self.root / ".lake/build/ir"
        self.lean = self.root / ".lake/build/lib/lean"
        tree = ast.parse((ROOT / "setup.py").read_text())
        helpers: list[ast.stmt] = [
            node
            for node in tree.body
            if isinstance(node, ast.FunctionDef)
            and node.name
            in ("_collect_lean_objects", "_should_run_lake", "_enable_parallel_compile")
        ]
        self.assertEqual(len(helpers), 3)
        self.namespace: dict[str, Any] = {
            "json": json,
            "os": os,
            "Any": Any,
            "ThreadPoolExecutor": ThreadPoolExecutor,
            "Path": Path,
            "REPO_ROOT": self.root,
            "LAKE_IR": self.ir,
        }
        exec(compile(ast.Module(body=helpers, type_ignores=[]), "setup.py", "exec"), self.namespace)

    def write_module(self, module: str, imports: Sequence[list[str | bool]] = ()) -> Path:
        path = Path(*module.split("."))
        source = self.root / path.with_suffix(".lean")
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text("module\n")
        metadata = self.lean / path.with_suffix(".ilean")
        metadata.parent.mkdir(parents=True, exist_ok=True)
        metadata.write_text(json.dumps({"version": 5, "module": module, "directImports": imports}))
        obj = self.ir / path.with_suffix(".c.o.export")
        obj.parent.mkdir(parents=True, exist_ok=True)
        obj.touch()
        return obj

    def collect(self) -> list[str]:
        return self.namespace["_collect_lean_objects"]()

    def test_runtime_walk_keeps_private_and_all_imports_but_skips_meta_closure(self) -> None:
        root = self.write_module(
            "EthLib.Exports",
            [
                ["EthLib.Base.Exports.Probe", True, True, False],
                ["EthLib.Base.Proofs.Laws", False, False, True],
                ["Lean", False, False, False],
            ],
        )
        probe = self.write_module(
            "EthLib.Base.Exports.Probe", [["EthLib.Base.Value", False, False, False]]
        )
        value = self.write_module("EthLib.Base.Value")
        self.write_module(
            "EthLib.Base.Proofs.Laws", [["EthLib.Base.Proofs.Other", False, False, False]]
        )
        self.write_module("EthLib.Base.Proofs.Other")
        self.assertEqual(self.collect(), sorted(map(str, [root, probe, value])))

    def test_ordinary_proof_import_is_selected_so_the_boundary_check_can_reject_it(self) -> None:
        root = self.write_module(
            "EthLib.Exports", [["EthLib.Base.Proofs.Laws", False, False, False]]
        )
        laws = self.write_module("EthLib.Base.Proofs.Laws")
        self.assertEqual(self.collect(), sorted(map(str, [root, laws])))

    def test_ordinary_import_wins_when_the_same_module_is_also_meta_imported(self) -> None:
        root = self.write_module(
            "EthLib.Exports",
            [
                ["EthLib.Base.Value", False, False, True],
                ["EthLib.Base.Value", False, False, False],
            ],
        )
        value = self.write_module("EthLib.Base.Value")
        self.assertEqual(self.collect(), sorted(map(str, [root, value])))

    def test_unreachable_and_removed_module_objects_do_not_enter_the_link(self) -> None:
        root = self.write_module("EthLib.Exports")
        self.write_module("EthLib.Base.Unreachable")
        self.write_module("EthLib.Base.Removed")
        (self.root / "EthLib/Base/Removed.lean").unlink()
        self.assertEqual(self.collect(), [str(root)])

    def test_missing_runtime_object_fails_instead_of_shortening_the_link(self) -> None:
        self.write_module("EthLib.Exports", [["EthLib.Base.Value", False, False, False]])
        obj = self.write_module("EthLib.Base.Value")
        obj.unlink()
        message = f"runtime Lean object is missing: {obj}"
        with self.assertRaisesRegex(RuntimeError, rf"\A{re.escape(message)}\Z"):
            self.collect()

    def test_missing_runtime_source_fails_instead_of_using_its_stale_object(self) -> None:
        self.write_module("EthLib.Exports", [["EthLib.Base.Value", False, False, False]])
        self.write_module("EthLib.Base.Value")
        source = self.root / "EthLib/Base/Value.lean"
        source.unlink()
        message = f"runtime Lean source is missing: {source}"
        with self.assertRaisesRegex(RuntimeError, rf"\A{re.escape(message)}\Z"):
            self.collect()

    def test_metadata_must_match_the_module_and_supported_schema(self) -> None:
        self.write_module("EthLib.Exports")
        metadata = self.lean / "EthLib/Exports.ilean"
        for changes in [{"version": 4}, {"module": "EthLib.Other"}]:
            with self.subTest(changes=changes):
                data = {"version": 5, "module": "EthLib.Exports", "directImports": []}
                metadata.write_text(json.dumps(data | changes))
                message = f"unsupported or mismatched Lean import metadata: {metadata}"
                with self.assertRaisesRegex(RuntimeError, rf"\A{re.escape(message)}\Z"):
                    self.collect()

    def test_skip_lake_env_controls_lake_invocation(self) -> None:
        should_run = self.namespace["_should_run_lake"]
        with patch.dict(os.environ, {}, clear=True):
            self.assertTrue(should_run())
        with patch.dict(os.environ, {"ETHLIB_SKIP_LAKE": "0"}, clear=True):
            self.assertTrue(should_run())
        with patch.dict(os.environ, {"ETHLIB_SKIP_LAKE": "1"}, clear=True):
            self.assertFalse(should_run())

    def test_parallel_compile_dispatches_every_source_object(self) -> None:
        compiled: list[tuple[str, str]] = []

        class FakeCompiler:
            def _setup_compile(self, output_dir, macros, include_dirs, sources, depends, post):
                objects = [f"{s}.o" for s in sources]
                build = {f"{s}.o": (s, ".c") for s in sources}
                return macros, objects, post, [], build

            def _get_cc_args(self, pp_opts, debug, pre):
                return []

            def _compile(self, obj, src, ext, cc_args, post, pp_opts):
                compiled.append((obj, src))

            def compile(self, *args, **kwargs):
                raise AssertionError("sequential compile must be replaced")

        compiler = FakeCompiler()
        self.namespace["_enable_parallel_compile"](compiler, 4)
        result = compiler.compile(["a.c", "b.c", "c.c"])
        self.assertEqual(result, ["a.c.o", "b.c.o", "c.c.o"])
        self.assertEqual(sorted(compiled), [("a.c.o", "a.c"), ("b.c.o", "b.c"), ("c.c.o", "c.c")])


if __name__ == "__main__":
    unittest.main()
