"""Pure-Python closure/receipt tests. No Lean, Lake, exporter, or large allocation."""
from pathlib import Path
import contextlib
import copy
import importlib.util
import io
import json
import os
import subprocess
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location("check_lean_closure", Path(__file__).with_name("check_lean_closure.py"))
closure = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(closure)
checker = closure.load_checker(Path(__file__).with_name("check_lean.py"))
P = closure.PREFIX


class ClosureTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name).resolve()
        self.repo, self.logs = self.base / "repo", self.base / "logs"
        self.formal = self.repo / "formal"
        self.formal.mkdir(parents=True)
        (self.formal / "lean-toolchain").write_text("pinned lean\n")
        (self.formal / "lake-manifest.json").write_text("{}\n")
        self.checker_path = self.repo / "scripts/check_lean.py"
        self.checker_path.parent.mkdir()
        self.checker_path.write_text("# supervisor fingerprint fixture\n")

    def source(self, suffix, imports=()):
        name = P + ("." + suffix if suffix else "")
        path = self.formal / Path(name.replace(".", "/")).with_suffix(".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("".join("import " + x + "\n" for x in imports) + "-- fixture\n")
        return name

    def object(self, name, companion=False):
        path = self.formal / ".lake/build/lib/lean" / Path(name.replace(".", "/")).with_suffix(".olean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(b"object " + name.encode())
        if companion:
            Path(str(path) + ".private").write_bytes(b"private")
            Path(str(path) + ".server").write_bytes(b"server")
        return path

    def receipt(self, name, deps):
        self.object(name, companion=True)
        for dep in deps:
            self.object(dep, companion=True)
        source = closure.source_path(self.formal, name)
        return {
            "schema": 2, "success": True, "status": "complete", "reason": None,
            "inputs_unchanged": True, "returncode": 0, "source": str(source.relative_to(self.formal)),
            "source_sha256": checker.digest(source),
            "runner_sha256": checker.digest(self.checker_path),
            "environment": {k: os.environ.get(k) for k in closure.ENV_KEYS},
            "legacy_unverified_dependencies": [],
            "dependency_source_sha256": {str(closure.source_path(self.formal, d)): checker.digest(closure.source_path(self.formal, d)) for d in deps},
            "import_olean_hashes": {str(p): checker.digest(p) for d in deps for p in closure.objects(self.formal, d)},
            "output_hashes": {str(p): checker.digest(p) for p in closure.objects(self.formal, name)},
            "toolchain_fingerprints": {str(p): checker.digest(p) for p in (self.formal / "lean-toolchain", self.formal / "lake-manifest.json")},
        }

    def save(self, name, receipt):
        self.logs.mkdir(exist_ok=True)
        (self.logs / (name + ".json")).write_text(json.dumps(receipt))

    def reusable(self, name, deps):
        return closure.resumable(self.formal, self.logs, name, deps, checker, self.checker_path)

    def test_topological_order_shared_import_and_external_ignored(self):
        leaf = self.source("Leaf", ["Mathlib.Data.Nat.Basic"])
        b = self.source("B", [leaf])
        a = self.source("A", [leaf])
        root = self.source("", [b, a])
        order, graph = closure.closure(self.formal, [root], checker.direct_imports)
        self.assertEqual(order, [leaf, a, b, root])
        self.assertEqual(graph[root], [a, b])
        self.assertEqual(len(order), len(set(order)))

    def test_cycle_and_missing_local_source_rejected(self):
        a = self.source("A", [P + ".B"])
        self.source("B", [a])
        with self.assertRaisesRegex(ValueError, "cycle"):
            closure.closure(self.formal, [a], checker.direct_imports)
        missing = self.source("MissingRoot", [P + ".Absent"])
        with self.assertRaisesRegex(ValueError, "missing"):
            closure.closure(self.formal, [missing], checker.direct_imports)

    def test_source_object_companions_and_pins_invalidate_resume(self):
        dep = self.source("Dep")
        root = self.source("", [dep])
        original = self.receipt(root, [dep])
        self.save(root, original)
        self.assertTrue(self.reusable(root, [dep]))
        source = closure.source_path(self.formal, root)
        cases = [source, closure.source_path(self.formal, dep),
                 closure.objects(self.formal, root)[0], closure.objects(self.formal, dep)[0],
                 self.formal / "lean-toolchain", self.formal / "lake-manifest.json", self.checker_path]
        for path in cases:
            with self.subTest(path=path):
                old = path.read_bytes()
                path.write_bytes(old + b"changed")
                self.assertFalse(self.reusable(root, [dep]))
                path.write_bytes(old)
        private = Path(str(closure.objects(self.formal, root)[0]) + ".private")
        old = private.read_bytes()
        private.unlink()
        self.assertFalse(self.reusable(root, [dep]))
        private.write_bytes(old)
        self.assertTrue(self.reusable(root, [dep]))

    def test_module_ir_output_is_required_and_hashed_but_not_an_import_object(self):
        dep = self.source("ModuleDep")
        root = self.source("", [dep])
        receipt = self.receipt(root, [dep])
        ir = closure.objects(self.formal, root)[0].with_suffix(".ir")
        ir.write_bytes(b"module IR")
        dep_ir = closure.objects(self.formal, dep)[0].with_suffix(".ir")
        dep_ir.write_bytes(b"dependency IR")
        self.save(root, receipt)
        self.assertFalse(self.reusable(root, [dep]))
        receipt["output_hashes"][str(ir)] = checker.digest(ir)
        self.save(root, receipt)
        self.assertTrue(self.reusable(root, [dep]))
        self.assertNotIn(str(dep_ir), receipt["import_olean_hashes"])
        ir.write_bytes(b"changed IR")
        self.assertFalse(self.reusable(root, [dep]))
        ir.unlink()
        self.assertFalse(self.reusable(root, [dep]))

    def test_omitted_direct_dependency_fingerprints_and_legacy_rejected(self):
        dep = self.source("Dep")
        root = self.source("", [dep])
        original = self.receipt(root, [dep])
        for key in ("dependency_source_sha256", "import_olean_hashes", "output_hashes", "toolchain_fingerprints"):
            with self.subTest(key=key):
                forged = copy.deepcopy(original)
                forged[key] = {}
                self.save(root, forged)
                self.assertFalse(self.reusable(root, [dep]))
        forged = copy.deepcopy(original)
        forged["legacy_unverified_dependencies"] = [dep]
        self.save(root, forged)
        self.assertFalse(self.reusable(root, [dep]))
        self.save(root, original)
        self.assertTrue(self.reusable(root, [dep]))
        forged = copy.deepcopy(original)
        forged["dependency_source_sha256"] = {}
        forged["import_olean_hashes"] = {}
        self.save(root, forged)
        self.assertFalse(self.reusable(root, []))  # current source import list is authoritative
        self.save(root, original)
        (self.logs / (root + ".json")).unlink()
        self.assertFalse(self.reusable(root, [dep]))  # objects alone never suffice

    def test_non_dictionary_receipt_rejected(self):
        name = self.source("")
        for value in ([], None, 7, "not a receipt"):
            with self.subTest(value=value):
                self.save(name, value)
                self.assertFalse(self.reusable(name, []))

    def test_final_scan_rejects_late_source_or_earlier_object_edit(self):
        leaf = self.source("Leaf")
        middle = self.source("Middle", [leaf])
        root = self.source("", [middle])
        deps = {leaf: [], middle: [leaf], root: [middle]}
        for kind in ("source", "object"):
            with self.subTest(kind=kind):
                calls = []
                def fake_run(command):
                    module = Path(command[3]).with_suffix("").as_posix().replace("/", ".")
                    calls.append(module)
                    self.assertEqual(command[command.index("--seconds") + 1], "3600")
                    self.save(module, self.receipt(module, deps[module]))
                    if module == root:
                        target = (closure.source_path(self.formal, leaf) if kind == "source"
                                  else closure.objects(self.formal, leaf)[0])
                        target.write_bytes(target.read_bytes() + b" late edit")
                    return subprocess.CompletedProcess(command, 0)
                with patch.object(closure, "__file__", str(self.repo / "scripts/check_lean_closure.py")), \
                     patch.object(closure, "load_checker", return_value=checker), \
                     patch.object(closure.subprocess, "run", side_effect=fake_run), \
                     contextlib.redirect_stdout(io.StringIO()), \
                     contextlib.redirect_stderr(io.StringIO()) as errors:
                    self.assertEqual(closure.main(["--log-dir", str(self.logs)]), 1)
                self.assertEqual(calls, [leaf, middle, root])
                self.assertIn("final closure validation failed", errors.getvalue())

    def test_archive_preserves_prior_failed_receipt_and_log(self):
        name = self.source("")
        self.save(name, {"success": False, "reason": "failure"})
        log = self.logs / (name + ".log")
        log.write_text("old failure evidence")
        closure.archive_attempt(self.logs, name)
        saved = list((self.logs / "previous-attempts").iterdir())
        self.assertEqual(len(saved), 1)
        self.assertEqual((saved[0] / log.name).read_text(), log.read_text())
        self.assertTrue((saved[0] / (name + ".json")).is_file())
        self.assertTrue(log.is_file())

    def test_plan_no_subprocess_no_logs_and_serial_fail_stop(self):
        leaf = self.source("Leaf")
        middle = self.source("Middle", [leaf])
        root = self.source("", [middle])
        wrapper_path = self.repo / "scripts/check_lean_closure.py"
        with patch.object(closure, "__file__", str(wrapper_path)), \
             patch.object(closure, "load_checker", return_value=checker), \
             patch.object(closure.subprocess, "run") as run, \
             contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(closure.main(["--log-dir", str(self.logs), "--plan"]), 0)
            run.assert_not_called()
            self.assertFalse(self.logs.exists())
        calls = []
        def fake_run(command):
            module = Path(command[3]).with_suffix("").as_posix().replace("/", ".")
            calls.append(module)
            if module == leaf:
                self.save(leaf, self.receipt(leaf, []))
                return subprocess.CompletedProcess(command, 0)
            return subprocess.CompletedProcess(command, 1)
        with patch.object(closure, "__file__", str(wrapper_path)), \
             patch.object(closure, "load_checker", return_value=checker), \
             patch.object(closure.subprocess, "run", side_effect=fake_run), \
             contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(closure.main(["--log-dir", str(self.logs)]), 1)
        self.assertEqual(calls, [leaf, middle])  # root is never launched


if __name__ == "__main__":
    unittest.main()
