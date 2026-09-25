"""Tiny supervisor/receipt regressions; no Lean, Lake, or large allocations."""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location("check_lean", Path(__file__).with_name("check_lean.py"))
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)


def live(pid):
    p = subprocess.run(["ps", "-p", str(pid), "-o", "stat="], capture_output=True, text=True, timeout=2)
    return bool(p.stdout.strip()) and not p.stdout.strip().startswith("Z")


class SupervisorTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="lean-supervisor-test-")
        self.path = Path(self.temp.name).resolve()

    def tearDown(self):
        self.temp.cleanup()

    def run_child(self, code, **kwargs):
        options = dict(rss_limit_mb=48, seconds=2, log_limit_bytes=4096,
                       cancellation=runner.Cancellation())
        options.update(kwargs)
        return runner.run_monitored([sys.executable, "-c", code], self.path,
                                    self.path / "child.log", **options)

    def test_success_and_bounded_output(self):
        result = self.run_child("print('ok')")
        self.assertEqual(result["returncode"], 0)
        self.assertIsNone(result["reason"])
        self.assertEqual((self.path / "child.log").read_text(), "ok\n")
        result = self.run_child("import os\nwhile True: os.write(1,b'x'*4096)")
        self.assertEqual(result["reason"], "log-output limit exceeded")
        self.assertEqual((self.path / "child.log").stat().st_size, 4096)
        self.assertFalse(live(result["child_pgid"]))

    def test_timeout_rss_and_probe_exception(self):
        for kwargs, reason in [
            ({"seconds": 0.1}, "wall-time"),
            ({"rss_probe": lambda _: 49 * 1024}, "RSS limit"),
            ({"rss_probe": lambda _: (_ for _ in ()).throw(RuntimeError("probe failed"))}, "probe failed"),
        ]:
            with self.subTest(reason=reason):
                result = self.run_child("import time; time.sleep(10)", **kwargs)
                self.assertIn(reason, result["reason"])
                self.assertFalse(live(result["child_pgid"]))

    def test_exception_immediately_after_spawn(self):
        def fail(_):
            raise RuntimeError("spawn callback failed")
        result = self.run_child("import time; time.sleep(10)", on_started=fail)
        self.assertIn("spawn callback failed", result["reason"])
        self.assertIsNotNone(result["returncode"])
        self.assertFalse(live(result["child_pgid"]))

    def test_group_probe_failure_still_reaps_and_preserves_error(self):
        original = runner.signal_group
        def fail_after_term(pgid, sig):
            result = original(pgid, sig)
            if sig == signal.SIGTERM:
                raise PermissionError("synthetic post-TERM group error")
            return result
        with patch.object(runner, "signal_group", fail_after_term):
            result = self.run_child("import time; time.sleep(10)", seconds=0.1)
        self.assertIn("synthetic post-TERM group error", result["reason"])
        self.assertEqual(result["returncode"], -signal.SIGTERM)
        self.assertFalse(live(result["child_pgid"]))

    def test_exited_leader_descendant_is_killed(self):
        code = """import subprocess,sys,time
from pathlib import Path
p=subprocess.Popen([sys.executable,'-c','import signal,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); time.sleep(10)'])
Path('descendant.pid').write_text(str(p.pid))
time.sleep(.15)
"""
        result = self.run_child(code)
        self.assertEqual(result["returncode"], 0)
        self.assertFalse(live(int((self.path / "descendant.pid").read_text())))

    def test_controller_sigterm_and_sigint(self):
        wrapper = self.path / "wrapper.py"
        wrapper.write_text(f"""import importlib.util,json,sys
from pathlib import Path
s=importlib.util.spec_from_file_location('r',{str(Path(runner.__file__))!r});r=importlib.util.module_from_spec(s);s.loader.exec_module(r)
c=r.Cancellation()
with c.installed():
 result=r.run_monitored([sys.executable,'-c',"import time; time.sleep(10)"],Path('.'),Path('signal.log'),rss_limit_mb=48,seconds=3,log_limit_bytes=4096,cancellation=c,on_started=lambda p:Path('signal.pid').write_text(str(p)))
Path('result.json').write_text(json.dumps(result))
""")
        for sig in (signal.SIGTERM, signal.SIGINT):
            with self.subTest(signal=sig):
                (self.path / "signal.pid").unlink(missing_ok=True)
                p = subprocess.Popen([sys.executable, "-B", str(wrapper)], cwd=self.path)
                try:
                    deadline = time.monotonic() + 2
                    while not (self.path / "signal.pid").exists() and time.monotonic() < deadline:
                        time.sleep(0.01)
                    self.assertTrue((self.path / "signal.pid").exists())
                    child = int((self.path / "signal.pid").read_text())
                    p.send_signal(sig)
                    p.wait(timeout=3)
                    result = json.loads((self.path / "result.json").read_text())
                    self.assertIn(f"signal {sig}", result["reason"])
                    self.assertFalse(live(child))
                finally:
                    if p.poll() is None:
                        p.kill(); p.wait()

    def test_header_imports_and_failed_receipt_blocks_stale_object(self):
        project = self.path / "project"
        formal = project / "formal"
        sources = formal / "SymmetricSubgroupAsymptotics"
        sources.mkdir(parents=True)
        logs = self.path / "logs"
        fake = self.path / "fake-lake"
        fake.write_text(f"#!{sys.executable}\nimport sys\nfrom pathlib import Path\np=Path(sys.argv[sys.argv.index('-o')+1])\ns=Path(sys.argv[sys.argv.index('-o')-1]).read_text()\nif 'FAIL' in s: sys.exit(1)\np.write_text('checked object')\n")
        fake.chmod(0o700)
        a, b = sources / "A.lean", sources / "B.lean"
        a.write_text("def a := 1\n")
        b.write_text("/- outer /- nested -/ comment -/\n  public import SymmetricSubgroupAsymptotics.A -- trailing\ndef b := 1\n")
        self.assertEqual(runner.direct_imports(b), ["SymmetricSubgroupAsymptotics.A"])
        def check(name):
            argv = [str(Path(runner.__file__)), f"SymmetricSubgroupAsymptotics/{name}.lean",
                    "--log-dir", str(logs), "--lake", str(fake)]
            with patch.object(runner, "ROOT", project), patch.object(runner, "FORMAL", formal), \
                 patch.object(sys, "argv", argv), contextlib.redirect_stdout(io.StringIO()):
                return runner.main()
        self.assertEqual(check("A"), 0)
        obj = formal / ".lake/build/lib/lean/SymmetricSubgroupAsymptotics/A.olean"
        self.assertEqual(check("B"), 0)
        a.write_text("FAIL\n")
        self.assertEqual(check("A"), 1)
        self.assertEqual(obj.read_text(), "checked object")
        receipt = json.loads((logs / "SymmetricSubgroupAsymptotics.A.json").read_text())
        self.assertFalse(receipt["success"])
        self.assertEqual(check("B"), 1)
        receipt = json.loads((logs / "SymmetricSubgroupAsymptotics.B.json").read_text())
        self.assertIn("stale or unsuccessful", receipt["reason"])


if __name__ == "__main__":
    unittest.main()
