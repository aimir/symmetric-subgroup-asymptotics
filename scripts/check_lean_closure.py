#!/usr/bin/env python3
"""Plan or serially check a local Lean import closure through check_lean.py.

No Lake build, exporter, parallel compiler, or independent axiom audit.
Resume accepts only complete schema-2 receipts bound to ALL current direct
local imports, their objects, source files, compiler/checker pins and outputs.
"""
from pathlib import Path
import argparse
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

PREFIX = "SymmetricSubgroupAsymptotics"
MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*")
ENV_KEYS = ("LEAN_PATH", "LEAN_SRC_PATH", "ELAN_TOOLCHAIN")


def load_checker(path):
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location("closure_single_checker", path)
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    return checker


def local(module):
    return module == PREFIX or module.startswith(PREFIX + ".")


def source_path(formal, module):
    if not MODULE.fullmatch(module) or not local(module):
        raise ValueError(f"not a local project module: {module}")
    path = formal / Path(module.replace(".", "/")).with_suffix(".lean")
    if not path.is_file() or not path.resolve().is_relative_to(formal.resolve()):
        raise ValueError(f"missing or outside-checkout local source: {module}")
    return path


def closure(formal, roots, direct_imports):
    """Deterministic dependency-first order, and exact local direct imports."""
    graph, order, state, stack = {}, [], {}, []

    def visit(module):
        if state.get(module) == 2:
            return
        if state.get(module) == 1:
            raise ValueError("local import cycle: " + " -> ".join(stack + [module]))
        source = source_path(formal, module)
        state[module] = 1
        stack.append(module)
        graph[module] = sorted(set(m for m in direct_imports(source) if local(m)))
        for dep in graph[module]:
            visit(dep)
        stack.pop()
        state[module] = 2
        order.append(module)

    for root in sorted(set(roots)):
        visit(root)
    return order, graph


def objects(formal, module):
    primary = formal / ".lake/build/lib/lean" / Path(module.replace(".", "/")).with_suffix(".olean")
    if not primary.is_file():
        raise ValueError(f"missing object: {module}")
    return [p for p in (primary, Path(str(primary) + ".private"),
                        Path(str(primary) + ".server")) if p.is_file()]


def resumable(formal, logs, module, deps, checker, checker_path, environment=None):
    """Fail closed; exact map equality rejects omitted or extra fingerprints."""
    try:
        receipt = json.loads((logs / (module + ".json")).read_text())
        if not isinstance(receipt, dict):
            return False
        source = source_path(formal, module)
        environment = os.environ if environment is None else environment
        current_deps = sorted(set(d for d in checker.direct_imports(source) if local(d)))
        if sorted(set(deps)) != current_deps:
            return False
        expected_sources = {str(source_path(formal, dep)): checker.digest(source_path(formal, dep))
                            for dep in deps}
        expected_imports = {str(p): checker.digest(p) for dep in deps for p in objects(formal, dep)}
        expected_outputs = {str(p): checker.digest(p) for p in objects(formal, module)}
        pins = {str(p): checker.digest(p) for p in
                (formal / "lean-toolchain", formal / "lake-manifest.json")}
        return (receipt.get("schema") == 2 and receipt.get("success") is True
                and receipt.get("status") == "complete"
                and receipt.get("inputs_unchanged") is True
                and receipt.get("returncode") == 0
                and receipt.get("reason") is None
                and receipt.get("source") == str(source.relative_to(formal))
                and receipt.get("source_sha256") == checker.digest(source)
                and receipt.get("runner_sha256") == checker.digest(checker_path)
                and receipt.get("environment") == {k: environment.get(k) for k in ENV_KEYS}
                and receipt.get("legacy_unverified_dependencies") == []
                and receipt.get("dependency_source_sha256") == expected_sources
                and receipt.get("import_olean_hashes") == expected_imports
                and receipt.get("output_hashes") == expected_outputs
                and receipt.get("toolchain_fingerprints") == pins)
    except (OSError, ValueError, TypeError, KeyError):
        return False


def frozen_inputs(formal, order, graph, checker, checker_path):
    paths = [source_path(formal, module) for module in order]
    paths += [checker_path, formal / "lean-toolchain", formal / "lake-manifest.json"]
    return {"files": {str(p): checker.digest(p) for p in paths}, "imports": graph}


def archive_attempt(logs, module):
    """Copy previous evidence before the supervisor replaces its live files."""
    old = [logs / (module + suffix) for suffix in (".json", ".log")]
    if not any(p.exists() for p in old):
        return
    history = logs / "previous-attempts"
    history.mkdir(parents=True, exist_ok=True)
    target = Path(tempfile.mkdtemp(prefix=module + ".", dir=history))
    for path in old:
        if path.is_file():
            shutil.copy2(path, target / path.name)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", action="append", help="local module; repeatable (default: public root)")
    parser.add_argument("--log-dir", type=Path, required=True)
    parser.add_argument("--plan", "--dry-run", action="store_true", help="print order; write nothing and run no checker")
    parser.add_argument("--resume", action="store_true", help="reuse only matching complete checked receipts")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--memory-mb", type=int, default=16384)
    parser.add_argument("--rss-limit-mb", type=int, default=16384)
    parser.add_argument("--seconds", type=int, default=3600)
    parser.add_argument("--log-limit-mb", type=int, default=16)
    args = parser.parse_args(argv)
    if not 64 <= args.memory_mb <= args.rss_limit_mb <= 16384:
        parser.error("require 64 <= memory-mb <= rss-limit-mb <= 16384")
    if not 1 <= args.seconds <= 3600 or not 1 <= args.log_limit_mb <= 64:
        parser.error("seconds must be1..3600 and log-limit-mb1..64")
    repo = Path(__file__).resolve().parents[1]
    formal, checker_path = repo / "formal", Path(__file__).with_name("check_lean.py").resolve()
    logs = args.log_dir.resolve()
    if logs.is_relative_to(repo):
        parser.error("logs must be outside the publication repository")
    checker = load_checker(checker_path)
    try:
        order, graph = closure(formal, args.root or [PREFIX], checker.direct_imports)
    except (OSError, ValueError) as exc:
        parser.error(str(exc))
    if args.plan:
        print(json.dumps({"roots": args.root or [PREFIX], "order": order,
                          "local_imports": graph}, indent=2))
        return 0
    initial = frozen_inputs(formal, order, graph, checker, checker_path)
    logs.mkdir(parents=True, exist_ok=True)
    # All predecessor receipts have been checked or refreshed in this run
    # before considering a consumer. Never infer validity from a sole object.
    for index, module in enumerate(order, 1):
        if args.resume and resumable(formal, logs, module, graph[module], checker, checker_path):
            print(f"[{index}/{len(order)}] reuse {module}", flush=True)
            continue
        archive_attempt(logs, module)
        command = [sys.executable, "-B", str(checker_path),
                   str(source_path(formal, module).relative_to(formal)),
                   "--log-dir", str(logs), "--lake", args.lake,
                   "--memory-mb", str(args.memory_mb), "--rss-limit-mb", str(args.rss_limit_mb),
                   "--seconds", str(args.seconds), "--log-limit-mb", str(args.log_limit_mb)]
        print(f"[{index}/{len(order)}] check {module}", flush=True)
        result = subprocess.run(command)
        if result.returncode:
            return result.returncode if result.returncode > 0 else 1
        if not resumable(formal, logs, module, graph[module], checker, checker_path):
            print(f"fresh checker receipt did not match current inputs: {module}", file=sys.stderr)
            return 1
    # A later compile must not conceal edits to an already visited subtree.
    for module in order:
        if not resumable(formal, logs, module, graph[module], checker, checker_path):
            print(f"final closure validation failed: {module}", file=sys.stderr)
            return 1
    try:
        final_order, final_graph = closure(formal, args.root or [PREFIX], checker.direct_imports)
        final = frozen_inputs(formal, final_order, final_graph, checker, checker_path)
    except (OSError, ValueError) as exc:
        print(f"final frozen-input validation failed: {exc}", file=sys.stderr)
        return 1
    if final != initial:
        print("source/import graph, supervisor or pins changed during closure check", file=sys.stderr)
        return 1
    print(f"Checked closure: {len(order)} local modules; no independent axiom-audit claim.")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        raise SystemExit(130)
