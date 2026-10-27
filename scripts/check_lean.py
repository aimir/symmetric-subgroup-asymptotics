#!/usr/bin/env python3
"""Check one Lean source with a shared compiler lock and strict resource limits.

Dependencies must already be built. This command never launches a Lake build.
The Lean allocator limit is supplemented by a sampled process-group RSS watchdog.
The user-authorized defaults and ceiling are 16 GiB for both the allocator and
the process-group RSS watchdog. The single-compiler lock applies to both.
Successful objects replace existing objects only after checking completes.
Logs and receipts must be kept outside the publication repository.
An isolated project may select another toolchain without changing the default
project; it still uses this repository's same single-compiler lock and limits.
"""
from pathlib import Path
import argparse
import contextlib
import fcntl
import hashlib
import json
import os
import re
import selectors
import signal
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / "formal"


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def atomic_json(path, value):
    fd, temp = tempfile.mkstemp(prefix=path.name + ".", dir=path.parent)
    try:
        with os.fdopen(fd, "w") as f:
            json.dump(value, f, indent=2)
            f.write("\n")
            f.flush()
            os.fsync(f.fileno())
        os.replace(temp, path)
    finally:
        with contextlib.suppress(FileNotFoundError):
            os.unlink(temp)


class Cancellation:
    """Do not raise asynchronously in the interval between spawn and assignment."""
    signum = None

    def handler(self, signum, _frame):
        self.signum = self.signum or signum

    @contextlib.contextmanager
    def installed(self):
        signals = (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)
        previous = {s: signal.signal(s, self.handler) for s in signals}
        try:
            yield self
        finally:
            for s, handler in previous.items():
                signal.signal(s, handler)


def group_rss_kib(pgid):
    # macOS can stall while reading unrelated processes in a full snapshot.
    # Select the entire monitored group directly there; retain the same
    # bounded probe and fail closed on timeout or a genuine ps error.
    grouped = sys.platform == "darwin"
    command = (["ps", "-g", str(pgid), "-o", "pgid=,rss="] if grouped else
               ["ps", "-axo", "pgid=,rss="])
    try:
        result = subprocess.run(
            command, check=True, capture_output=True, text=True, timeout=10
        )
    except subprocess.CalledProcessError as exc:
        # BSD ps returns 1 with no output when the selected group has exited.
        if grouped and exc.returncode == 1 and not exc.stdout and not exc.stderr:
            return 0
        raise
    return sum(int(rss) for group, rss in
               (line.split() for line in result.stdout.splitlines())
               if int(group) == pgid)


def signal_group(pgid, sig):
    try:
        os.killpg(pgid, sig)
        return True
    except ProcessLookupError:
        return False


def stop_group(process):
    # The leader may have exited while a descendant still holds its pipes.
    group_error = None
    try:
        if signal_group(process.pid, signal.SIGTERM):
            until = time.monotonic() + 0.5
            while time.monotonic() < until:
                process.poll()
                if not signal_group(process.pid, 0):
                    break
                time.sleep(0.025)
            signal_group(process.pid, signal.SIGKILL)
    except BaseException as exc:
        group_error = exc
    finally:
        # A disappearing-group probe can fail after TERM already killed the
        # leader. Reap it even then, while preserving the original kill error.
        try:
            process.wait(timeout=2)
        except BaseException as exc:
            if group_error is None:
                raise RuntimeError("process group leader could not be reaped") from exc
            group_error.add_note(f"Additional reaping failure: {type(exc).__name__}: {exc}")
    if group_error is not None:
        raise group_error


def run_monitored(command, cwd, log_path, *, rss_limit_mb, seconds,
                  log_limit_bytes, cancellation, lock_fd=None,
                  rss_probe=group_rss_kib, on_started=None):
    """Small testable supervisor: every path after Popen cleans the group."""
    started, peak, written = time.monotonic(), 0, 0
    process, reason, code = None, None, None
    try:
        with log_path.open("wb") as log, selectors.DefaultSelector() as selector:
            process = subprocess.Popen(command, cwd=cwd, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, start_new_session=True,
                pass_fds=(() if lock_fd is None else (lock_fd,)))
            os.set_blocking(process.stdout.fileno(), False)
            selector.register(process.stdout, selectors.EVENT_READ)
            if on_started:
                on_started(process.pid)
            next_probe = started
            while True:
                now = time.monotonic()
                if cancellation.signum:
                    reason = f"interrupted by signal {cancellation.signum}"
                    break
                if now - started > seconds:
                    reason = "wall-time limit exceeded"
                    break
                if now >= next_probe:
                    rss = rss_probe(process.pid)
                    peak = max(peak, rss)
                    if rss > rss_limit_mb * 1024:
                        reason = "process-group RSS limit exceeded"
                        break
                    next_probe = time.monotonic() + 0.1
                for key, _ in selector.select(timeout=0.05):
                    chunk = os.read(key.fd, 65536)
                    if not chunk:
                        selector.unregister(key.fileobj)
                        continue
                    remaining = log_limit_bytes - written
                    log.write(chunk[:remaining])
                    written += min(len(chunk), remaining)
                    if len(chunk) > remaining:
                        reason = "log-output limit exceeded"
                        break
                if reason:
                    break
                code = process.poll()
                if code is not None:
                    # Drain ready tail bytes, never wait for a descendant's pipe.
                    while True:
                        try:
                            chunk = os.read(process.stdout.fileno(), 65536)
                        except BlockingIOError:
                            break
                        if not chunk:
                            break
                        remaining = log_limit_bytes - written
                        log.write(chunk[:remaining])
                        written += min(len(chunk), remaining)
                        if len(chunk) > remaining:
                            reason = "log-output limit exceeded"
                            break
                    break
    except BaseException as exc:
        reason = f"monitor error: {type(exc).__name__}: {exc}"
    finally:
        if process is not None:
            try:
                stop_group(process)
            except BaseException as exc:
                reason = f"{reason or ''}; cleanup error: {type(exc).__name__}: {exc}"
            code = process.poll()
            process.stdout.close()
    return {"returncode": code, "reason": reason,
            "peak_rss_mib": round(peak / 1024, 2),
            "seconds": round(time.monotonic() - started, 2), "log_bytes": written,
            "child_pgid": None if process is None else process.pid}


def direct_imports(source):
    imports, depth = [], 0
    with source.open() as f:
        for line in f:
            clean, i = [], 0
            while i < len(line):
                pair = line[i:i + 2]
                if pair == "/-":
                    depth += 1; i += 2
                elif depth and pair == "-/":
                    depth -= 1; i += 2
                elif depth:
                    i += 1
                elif pair == "--":
                    break
                else:
                    clean.append(line[i]); i += 1
            text = "".join(clean).strip()
            if not text or text in ("module", "prelude"):
                continue
            match = re.fullmatch(r"(?:(?:public|private)\s+)?import\s+(.+)", text)
            if not match:
                if re.match(r"(?:(?:public|private)\s+)?import\b", text):
                    raise ValueError(f"unsupported import syntax in {source}: {text}")
                break
            names = match.group(1).split()
            if not all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", n)
                       for n in names):
                raise ValueError(f"unsupported module name in {source}: {text}")
            imports.extend(names)
    return imports


def fingerprints_unchanged(files):
    return all(Path(path).is_file() and digest(Path(path)) == sha for path, sha in files.items())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", help="Lean source relative to the selected project")
    parser.add_argument("--project-dir", type=Path,
                        help="Isolated Lake project (default: this repository's formal/)")
    parser.add_argument("--local-module-prefix", action="append",
                        help="Local module root to fingerprint; repeat for multiple roots")
    parser.add_argument("--execute-main", action="store_true",
                        help="Run a Lean utility's main under the same caps; emits no proof object")
    parser.add_argument("--run-arg", action="append", default=[],
                        help="Argument to an executed Lean utility; repeat for multiple arguments")
    parser.add_argument("--log-dir", type=Path, required=True)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--memory-mb", type=int, default=16384)
    parser.add_argument("--rss-limit-mb", type=int, default=16384)
    parser.add_argument("--seconds", type=int, default=900)
    parser.add_argument("--log-limit-mb", type=int, default=16)
    args = parser.parse_args()
    if args.run_arg and not args.execute_main:
        parser.error("--run-arg requires --execute-main")
    if not 64 <= args.memory_mb <= 16384:
        parser.error("--memory-mb must be between 64 and 16384")
    if not args.memory_mb <= args.rss_limit_mb <= 16384:
        parser.error("--rss-limit-mb must be at least the allocator limit and at most 16384")
    if not 1 <= args.seconds <= 3600:
        parser.error("--seconds must be between1 and3600")
    if not 1 <= args.log_limit_mb <= 64:
        parser.error("--log-limit-mb must be between1 and64")
    formal = args.project_dir.resolve() if args.project_dir else FORMAL.resolve()
    if args.project_dir and (not (formal / "lean-toolchain").is_file() or
                            not any((formal / name).is_file() for name in
                                    ("lakefile.lean", "lakefile.toml"))):
        parser.error("--project-dir must have lean-toolchain and a Lake configuration")
    local_prefixes = args.local_module_prefix or ["SymmetricSubgroupAsymptotics"]
    if any(not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", p)
           for p in local_prefixes):
        parser.error("--local-module-prefix must be a dotted Lean module name")
    source = (formal / args.source).resolve()
    if not source.is_relative_to(formal) or source.suffix != ".lean" or not source.is_file():
        parser.error("source must be an existing .lean file inside the selected project")
    logs = args.log_dir.resolve()
    if logs.is_relative_to(ROOT) or logs.is_relative_to(formal):
        parser.error("logs must be outside the publication repository and selected project")
    logs.mkdir(parents=True, exist_ok=True)
    relative = source.relative_to(formal)
    tag = str(relative.with_suffix("")).replace(os.sep, ".")
    if args.execute_main:
        tag += ".execution"
    output = formal / ".lake/build/lib/lean" / relative.with_suffix(".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    lock_path = FORMAL / ".lake/one-lean-compiler.lock"
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    cancellation = Cancellation()
    receipt = {"schema": 2, "source": str(relative), "success": False,
               "mode": "execution" if args.execute_main else "check",
               "status": "waiting", "reason": None,
               "memory_mb": args.memory_mb, "rss_limit_mb": args.rss_limit_mb,
               "log_limit_bytes": args.log_limit_mb * 1024 * 1024,
               "rss_enforcement": "sampled watchdog, nominal 0.1s interval; not an OS hard allocation limit",
               "proof_boundary": "Current source and direct local object/source fingerprints only. Schema-2 dependency receipts in this log directory are validated. Other local dependencies are legacy/unverified; their existing objects do not certify current source correspondence. External/transitive installed object contents are not recursively verified.",
               "runner_sha256": digest(Path(__file__)),
               "project_dir": str(formal), "compiler_lock": str(lock_path.resolve()),
               "local_module_prefixes": local_prefixes,
               "environment": {k: os.environ.get(k) for k in
                               ("LEAN_PATH", "LEAN_SRC_PATH", "ELAN_TOOLCHAIN", "ELAN_HOME")}}
    if args.execute_main:
        receipt["proof_boundary"] = "Utility execution only; no checked proof object is emitted or replaced."
        receipt["run_args"] = args.run_arg
    with cancellation.installed(), lock_path.open("a+") as lock:
        print("Waiting for the shared single-compiler lock", flush=True)
        while True:
            if cancellation.signum:
                return 128 + cancellation.signum
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except BlockingIOError:
                time.sleep(0.1)
        # Invalidate any old PASS before operations that can fail. The existing
        # object remains a last-known artifact, not a successful current attempt.
        receipt.update(status="checking", source_sha256=digest(source))
        atomic_json(logs / (tag + ".json"), receipt)
        try:
            group_rss_kib(os.getpgrp())  # Fail closed before launching the compiler.
            imports, dependency_sources, legacy = {}, {}, []
            for module in direct_imports(source):
                if not any(module == p or module.startswith(p + ".") for p in local_prefixes):
                    continue
                dep_source = formal / Path(module.replace(".", "/")).with_suffix(".lean")
                obj = formal / ".lake/build/lib/lean" / Path(module.replace(".", "/")).with_suffix(".olean")
                if not obj.is_file() or not dep_source.is_file():
                    raise ValueError(f"missing local dependency source/object: {module}")
                objects = [obj, Path(str(obj) + ".private"), Path(str(obj) + ".server")]
                hashes = {str(p): digest(p) for p in objects if p.is_file()}
                imports.update(hashes)
                dependency_sources[str(dep_source)] = digest(dep_source)
                dep_receipt = logs / (module + ".json")
                previous = json.loads(dep_receipt.read_text()) if dep_receipt.is_file() else {}
                if previous.get("schema") == 2:
                    if (previous.get("mode", "check") != "check" or not previous.get("success") or
                            previous.get("source_sha256") != dependency_sources[str(dep_source)] or
                            any(previous.get("output_hashes", {}).get(p) != h for p, h in hashes.items()) or
                            not fingerprints_unchanged(previous.get("import_olean_hashes", {})) or
                            not fingerprints_unchanged(previous.get("dependency_source_sha256", {}))):
                        raise ValueError(f"stale or unsuccessful checked dependency: {module}")
                else:
                    legacy.append(module)
            toolchain = {str(p): digest(p) for p in
                         [formal / n for n in ("lean-toolchain", "lake-manifest.json",
                                               "lakefile.lean", "lakefile.toml")] if p.is_file()}
            receipt.update(import_olean_hashes=imports, dependency_source_sha256=dependency_sources,
                           legacy_unverified_dependencies=legacy, toolchain_fingerprints=toolchain)
            with tempfile.TemporaryDirectory(prefix="lean-check-", dir=output.parent) as temp:
                temporary = Path(temp) / output.name
                command = [args.lake, "--no-cache", "env", "lean", "-M", str(args.memory_mb),
                           "-j", "1"]
                command += (["--run", str(relative), *args.run_arg] if args.execute_main else
                            [str(relative), "-o", str(temporary)])
                def started(pid):
                    receipt["child_pgid"] = pid
                    atomic_json(logs / (tag + ".json"), receipt)
                    print(f"Checking {relative}, pgid={pid}, allocator={args.memory_mb}MB, RSS threshold={args.rss_limit_mb}MB", flush=True)
                receipt.update(run_monitored(command, formal, logs / (tag + ".log"),
                    rss_limit_mb=args.rss_limit_mb, seconds=args.seconds,
                    log_limit_bytes=receipt["log_limit_bytes"], cancellation=cancellation,
                    lock_fd=lock.fileno(), on_started=started))
                unchanged = fingerprints_unchanged({str(source): receipt["source_sha256"],
                                                    **imports, **dependency_sources, **toolchain})
                receipt["inputs_unchanged"] = unchanged
                if cancellation.signum:
                    receipt["reason"] = f"interrupted by signal {cancellation.signum}"
                if not unchanged:
                    receipt["reason"] = "input fingerprint changed during check"
                success = (receipt.get("returncode") == 0 and not receipt["reason"] and unchanged
                           and (args.execute_main or temporary.is_file()))
                if success and not args.execute_main:
                    artifacts = sorted(Path(temp).iterdir(), key=lambda p: p == temporary)
                    for artifact in artifacts:
                        artifact.replace(output.parent / artifact.name)
                    names = {p.name for p in artifacts}
                    for suffix in (".private", ".server"):
                        companion = Path(str(output) + suffix)
                        if companion.name not in names:
                            companion.unlink(missing_ok=True)
                    receipt["output_hashes"] = {str(output.parent / p.name): digest(output.parent / p.name)
                                                for p in artifacts}
                elif success:
                    receipt["output_hashes"] = {}
                elif not receipt["reason"]:
                    receipt["reason"] = "compiler failed or produced no object"
                receipt["success"] = success
        except BaseException as exc:
            receipt.update(success=False, reason=f"{type(exc).__name__}: {exc}")
        finally:
            if cancellation.signum:
                receipt.update(success=False, reason=f"interrupted by signal {cancellation.signum}")
            receipt["status"] = "complete"
            atomic_json(logs / (tag + ".json"), receipt)
        print(json.dumps(receipt), flush=True)
        return (128 + cancellation.signum) if cancellation.signum else (0 if receipt["success"] else 1)


if __name__ == "__main__":
    raise SystemExit(main())
