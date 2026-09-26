#!/usr/bin/env python3
"""Bounded sparse Schreier Source/Binding producer, admitted source 16T832 only.

Requires --source b16_832 --record ABS_PRIVATE_JSON --record-sha256 SHA,
and one of --write / read-only --check. Optional --report is private JSON
and is forbidden with --check. The record is the compact output of the
separate bounded selected-record extractor. Only the pinned catalogue header
is read here; the action/normal record stream is never scanned.

Every group search shares one charged-operation/time/state budget. Immutable
ceilings: 512 rows per BFS, 8192 cumulative inserted rows, 500000 charged
operations, 5 seconds, four assignments, eight candidate hints, six target
generators, word length128, 8192 returned word letters, 128KiB combined output.
Bounds may only be lowered. No dense multiplication or inverse table, compiler,
subprocess, external search, network, or legacy search entry point is invoked.
Only pinned pure proof-rendering functions are loaded from the old exporters.
All group claims require subsequent kernel checks of BOTH generated files.
"""
from __future__ import annotations

import sys
sys.dont_write_bytecode = True
import argparse
import ast
import gzip
import hashlib
import json
import math
import os
from pathlib import Path
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
FORMAL = ROOT / "formal/SymmetricSubgroupAsymptotics"
PYTHON = ROOT / "computations/python"
SOURCE = "b16_832"
HEADER_SHA = "3e137e152a68aa3a3ac2f745f866082a2cb16f9d6d31bf1a09acfbb73cbdf1a1"
NODE_SHA = "0e40491ba44ca59bc1a51fdbcf8dc3b39932bf4e400275bb2b0a6b566aa5e4cd"
INPUT_SHA = "a28f0c47797feb254647ffa2dd345c4c565266859eed8968a06a3db6c2ba888a"
MAX_ROWS, MAX_TOTAL_ROWS, MAX_OPERATIONS = 512, 8192, 500_000
MAX_SECONDS, MAX_OUTPUT = 5.0, 128 * 1024
MAX_HEADER, MAX_RECORD = 1024 * 1024, 32 * 1024
MAX_WORD, MAX_LETTERS, MAX_EDGES, MAX_TARGET_GENERATORS = 128, 8192, 8, 6
EMITTERS = {
    "export_lean_menu_cayley.py": (
        "22017015f9419d1dc94f8ae7ac8d3d169b833e0783c2fd3c9fbdab819f676c08",
        ("lookup", "array")),
    "export_lean_schreier_actions.py": (
        "df1bfdb79cd66dbfbda8883e3dd051799408723ca301556a87a21ecd12763159",
        ("raw", "label", "word_literal", "permutation", "generator_tuple", "emit")),
    "export_lean_schreier_bindings.py": (
        "6269a5bb9532fb3434a6435abfefe5bc5b7094b6499569cf3d15936214f31eb6",
        ("emit_binding",)),
}


class Refused(Exception):
    pass


def require(ok, message):
    if not ok:
        raise Refused(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def bounded_read(path, limit):
    require(path.is_file() and not path.is_symlink(), f"not a regular input: {path}")
    with path.open("rb") as handle:
        data = handle.read(limit + 1)
    require(len(data) <= limit, f"input exceeds byte ceiling: {path}")
    return data


def private_path(raw):
    path = Path(raw).expanduser()
    require(path.is_absolute() and path.suffix == ".json", "need absolute private JSON path")
    require(not path.is_symlink(), "refusing symbolic-link private path")
    path = path.resolve()
    require(not path.is_relative_to(ROOT.resolve()), "JSON audit/hints must be outside repository")
    require(path.parent.is_dir(), "private parent directory must exist")
    return path


def atomic_write(path, data):
    require(not path.is_symlink(), "refusing symbolic-link output")
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(prefix=f".{path.name}.", dir=path.parent,
                                         delete=False) as handle:
            temporary = Path(handle.name)
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if temporary is not None and temporary.exists():
            temporary.unlink()


class Budget:
    def __init__(self, rows, operations, seconds):
        self.max_rows, self.max_operations, self.seconds = rows, operations, seconds
        self.started = time.monotonic()
        self.operations = self.inserted = self.returned_letters = self.searches = 0

    def tick(self, amount=1):
        self.operations += amount
        require(self.operations <= self.max_operations, "shared operation ceiling reached")
        require(time.monotonic() - self.started <= self.seconds, "shared time ceiling reached")

    def insert(self, local_count):
        self.tick()
        require(local_count < self.max_rows, "per-search row ceiling reached")
        require(self.inserted < MAX_TOTAL_ROWS, "cumulative search-row ceiling reached")
        self.inserted += 1

    def compose(self, a, b):
        self.tick(17)
        return tuple(a[x] for x in b)

    def inverse(self, p):
        self.tick(16)
        result = [0] * 16
        for i, x in enumerate(p):
            result[x] = i
        return tuple(result)

    def evaluate(self, generators, word):
        result = tuple(range(16))
        for letter in word:
            result = self.compose(result, generators[letter])
        return result

    def word(self, parents, letters, index):
        result = []
        while index:
            self.tick()
            require(len(result) < MAX_WORD, "word-length ceiling reached")
            result.append(letters[index])
            index = parents[index]
        self.returned_letters += len(result)
        require(self.returned_letters <= MAX_LETTERS, "cumulative returned-word ceiling reached")
        return list(reversed(result))


class WordPrefix:
    """One exact ordered tuple; cache retains parents, never full words per row."""
    def __init__(self, generators, budget):
        self.generators, self.budget = tuple(generators), budget
        budget.insert(0)
        budget.searches += 1
        identity = tuple(range(16))
        self.rows, self.indices = [identity], {identity: 0}
        self.parents, self.letters, self.cursor = [0], [0], 0

    def words(self, targets):
        budget = self.budget
        budget.tick(len(targets))
        missing = set(targets).difference(self.indices)
        while missing and self.cursor < len(self.rows):
            for j, generator in enumerate(self.generators):
                product = budget.compose(self.rows[self.cursor], generator)
                budget.tick()
                if product in self.indices:
                    continue
                budget.insert(len(self.rows))
                self.indices[product] = len(self.rows)
                self.rows.append(product)
                self.parents.append(self.cursor)
                self.letters.append(j)
                missing.discard(product)
            self.cursor += 1
        if missing:
            raise KeyError("literal target is outside this completed finite closure")
        result = [budget.word(self.parents, self.letters, self.indices[t]) for t in targets]
        for word, target in zip(result, targets):
            require(budget.evaluate(self.generators, word) == target, "positive-word validation failed")
        return result


def relations(generators, budget):
    prefix = WordPrefix(generators, budget)
    parity, pivots, witnesses = [0], {}, []
    while prefix.cursor < len(prefix.rows):
        i = prefix.cursor
        for j, generator in enumerate(generators):
            product = budget.compose(prefix.rows[i], generator)
            bits = parity[i] ^ (1 << j)
            budget.tick()
            if product not in prefix.indices:
                budget.insert(len(prefix.rows))
                prefix.indices[product] = len(prefix.rows)
                prefix.rows.append(product)
                prefix.parents.append(i)
                prefix.letters.append(j)
                parity.append(bits)
                continue
            target = prefix.indices[product]
            mask = bits ^ parity[target]
            reduced = mask
            while reduced and reduced.bit_length() - 1 in pivots:
                budget.tick()
                reduced ^= pivots[reduced.bit_length() - 1]
            if reduced:
                pivots[reduced.bit_length() - 1] = reduced
                u = budget.word(prefix.parents, prefix.letters, i) + [j]
                v = budget.word(prefix.parents, prefix.letters, target)
                budget.returned_letters += 1
                require(len(u) <= MAX_WORD and budget.returned_letters <= MAX_LETTERS,
                        "relation word ceiling reached")
                require(budget.evaluate(generators, u) == budget.evaluate(generators, v),
                        "literal relation validation failed")
                witnesses.append((mask, u, v))
        prefix.cursor += 1
    return witnesses


def schreier(generators, bits, outside, budget):
    identity = tuple(range(16))
    return [budget.compose(budget.compose(identity if side else outside, generator),
                           budget.inverse(identity if side == bit else outside))
            for side in (False, True) for generator, bit in zip(generators, bits)]


def coloring(generators, budget):
    reached, queue, cursor = {0}, [0], 0
    while cursor < len(queue):
        for generator in generators:
            budget.tick()
            point = generator[queue[cursor]]
            if point not in reached:
                reached.add(point)
                queue.append(point)
        cursor += 1
    color = [x in reached for x in range(16)]
    for generator in generators:
        for x in range(16):
            budget.tick()
            require(color[generator[x]] == color[x], "orbit-colouring validation failed")
    return color, next((x for x in range(16) if x not in reached), None)


def generators_of(node, limit):
    rows = node.get("generators")
    require(isinstance(rows, list) and 1 <= len(rows) <= limit, "generator count outside admission")
    require(all(isinstance(g, list) and len(g) == 16 and all(type(x) is int for x in g)
                and sorted(g) == list(range(1, 17)) for g in rows), "invalid original generators")
    return [tuple(x - 1 for x in row) for row in rows]


def compile_selected(node, edges, nodes, budget):
    source_generators = generators_of(node, 2)
    require(len(source_generators) == 2, "832 pilot needs exactly two source generators")
    relation_words = relations(source_generators, budget)
    branches, cache = [], {}
    for assignment in range(4):
        budget.tick()
        if assignment == 3:
            branches.append({"kind": "trivial"})
            continue
        bad = next(((u, v) for mask, u, v in relation_words
                    if (mask & ~assignment).bit_count() % 2), None)
        if bad is not None:
            branches.append({"kind": "relation", "words": bad})
            continue
        bits = [bool(assignment & (1 << j)) for j in range(2)]
        outside = bits.index(False)
        child = schreier(source_generators, bits, source_generators[outside], budget)
        color, missing = coloring(child, budget)
        if missing is not None:
            branches.append({"kind": "color", "outside": outside, "color": color, "missing": missing})
            continue
        for edge in edges:
            budget.tick()
            target = generators_of(nodes[edge["target"]], MAX_TARGET_GENERATORS)
            conjugator = tuple(x - 1 for x in edge["conjugator"])
            inverse = budget.inverse(conjugator)
            conjugated = [budget.compose(budget.compose(conjugator, g), inverse) for g in child]
            key = tuple(target)
            if key not in cache:
                cache[key] = WordPrefix(target, budget)
            try:
                forward = cache[key].words(conjugated)
                backward = WordPrefix(conjugated, budget).words(target)
            except KeyError:
                continue
            branches.append({"kind": "accepted", "outside": outside, "target": edge["target"],
                             "conjugator": conjugator, "forward": forward, "backward": backward})
            break
        else:
            raise Refused(f"no checked two-way hint for assignment {assignment}; no partial source emitted")
    require(len(branches) == 4, "incomplete assignment coverage")
    return branches


def load_header():
    path = ROOT / "certificates/data/binary_menu.jsonl.gz"
    require(path.is_file() and not path.is_symlink(), "missing/redirected catalogue")
    with gzip.open(path, "rb") as stream:
        data = stream.readline(MAX_HEADER + 1)
    require(len(data) <= MAX_HEADER and data.endswith(b"\n") and digest(data) == HEADER_SHA,
            "pinned bounded header changed")
    header = json.loads(data)
    names = [n["id"] for n in header["nodes"] if n["degree"] == 16]
    nodes = {n["id"]: n for n in header["nodes"]}
    require(len(names) == 1427 and len(set(names)) == 1427 and names[698] == SOURCE,
            "original family indices changed")
    require(digest(canonical(nodes[SOURCE])) == NODE_SHA, "original source tuple changed")
    return data, names, nodes


def checked_hint_edges(bundle, nodes):
    require(bundle.get("schema") == "selected-schreier-action-hints-v1"
            and bundle.get("source") == SOURCE and bundle.get("header_sha256") == HEADER_SHA
            and bundle.get("compressed_input_sha256") == INPUT_SHA
            and bundle.get("source_node_sha256") == NODE_SHA, "wrong admitted hint bundle")
    action = bundle.get("action", {})
    require(action.get("kind") == "action" and action.get("id") == SOURCE, "wrong selected record")
    edges = action.get("action_children")
    require(isinstance(edges, list) and len(edges) <= MAX_EDGES, "hint edge ceiling reached")
    for edge in edges:
        require(isinstance(edge, dict), "malformed child hint")
        target, conjugator = edge.get("target"), edge.get("conjugator")
        require(isinstance(target, str) and target in nodes and nodes[target]["degree"] == 16,
                "target is not an original sixteen-point action")
        require(bundle.get("target_node_sha256", {}).get(target) == digest(canonical(nodes[target])),
                "original target tuple hash mismatch")
        generators_of(nodes[target], MAX_TARGET_GENERATORS)
        require(isinstance(conjugator, list) and len(conjugator) == 16
                and all(type(x) is int for x in conjugator)
                and sorted(conjugator) == list(range(1, 17)), "invalid original point conjugator")
    return edges


def render(node, names, nodes, branches, budget, snapshots):
    """Load ONLY named pinned pure function definitions, never legacy imports/main/search."""
    environment = {"inverse": budget.inverse}
    for filename, (expected, allowed) in EMITTERS.items():
        path = PYTHON / filename
        data = bounded_read(path, MAX_HEADER)
        require(digest(data) == expected, f"pinned pure-emitter source changed: {filename}")
        snapshots[path] = data
        tree = ast.parse(data, filename=str(path))
        functions = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name in allowed]
        require({f.name for f in functions} == set(allowed), "pure-emitter function set changed")
        require(all(not f.decorator_list for f in functions), "unexpected emitter decorator")
        code = compile(ast.Module(body=functions, type_ignores=[]), str(path), "exec")
        exec(code, environment)
        budget.tick()
    local = environment["emit"](node, nodes, branches)
    local = local.replace("Generated by export_lean_schreier_actions.py.",
                          "Generated by export_lean_selected_schreier.py (bounded selected words).")
    binding = environment["emit_binding"](node, names, branches)
    # Preserve exact theorem APIs while using the default heartbeat budget.
    return [text.replace("set_option maxHeartbeats 2000000\n", "").encode()
            for text in (local, binding)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True, choices=(SOURCE,))
    parser.add_argument("--record", required=True)
    parser.add_argument("--record-sha256", required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--report")
    parser.add_argument("--max-rows", type=int, default=MAX_ROWS)
    parser.add_argument("--max-operations", type=int, default=MAX_OPERATIONS)
    parser.add_argument("--max-seconds", type=float, default=MAX_SECONDS)
    args = parser.parse_args()
    require(1 <= args.max_rows <= MAX_ROWS and 1 <= args.max_operations <= MAX_OPERATIONS,
            "requested search ceiling exceeds immutable admission")
    require(math.isfinite(args.max_seconds) and 0 < args.max_seconds <= MAX_SECONDS,
            "requested time ceiling exceeds immutable admission")
    require(not(args.check and args.report), "--check is read-only and forbids report output")
    record_path = private_path(args.record)
    report_path = private_path(args.report) if args.report else None
    require(report_path != record_path, "report must not overwrite selected hints")
    budget = Budget(args.max_rows, args.max_operations, args.max_seconds)
    snapshots = {Path(__file__).resolve(): bounded_read(Path(__file__).resolve(), MAX_HEADER)}
    record = bounded_read(record_path, MAX_RECORD)
    require(digest(record) == args.record_sha256, "selected-record SHA256 mismatch")
    snapshots[record_path] = record
    header, names, nodes = load_header()
    bundle = json.loads(record)
    edges = checked_hint_edges(bundle, nodes)
    # Snapshot every actual original Data dependency used by the selected
    # source and target tuples. The emitted binding still checks each equality.
    chunks = {names.index(label) // 32 for label in [SOURCE] + [e["target"] for e in edges]}
    data_paths = [FORMAL / "GeneratedAction16/Data.lean"] + [
        FORMAL / "GeneratedAction16" / f"DataChunk{i:03d}.lean" for i in sorted(chunks)]
    for path in data_paths:
        snapshots[path] = bounded_read(path, MAX_HEADER)
    branches = compile_selected(nodes[SOURCE], edges, nodes, budget)
    outputs = render(nodes[SOURCE], names, nodes, branches, budget, snapshots)
    output_dir = FORMAL / "GeneratedSchreierActions"
    require(output_dir.is_dir() and not output_dir.is_symlink()
            and output_dir.resolve().is_relative_to(ROOT.resolve()), "unsafe/missing canonical output directory")
    paths = [output_dir / "Source16T832.lean", output_dir / "Binding16T832.lean"]
    for path in paths:
        require(not path.is_symlink(), "refusing symbolic-link source output")
    report = {"schema": "bounded-selected-schreier-v1", "source": SOURCE,
              "record_sha256": digest(record), "header_sha256": HEADER_SHA,
              "charged_operations": budget.operations, "cumulative_rows": budget.inserted,
              "searches": budget.searches, "returned_word_letters": budget.returned_letters,
              "branches": {kind: sum(b["kind"] == kind for b in branches)
                           for kind in ("trivial", "relation", "color", "accepted")},
              "targets": sorted({b["target"] for b in branches if b["kind"] == "accepted"}),
              "outputs": [{"path": str(p.relative_to(ROOT)), "bytes": len(data), "sha256": digest(data)}
                          for p, data in zip(paths, outputs)],
              "input_sha256": {str(p): digest(data) for p, data in snapshots.items()},
              "limits": {"rows_per_search": args.max_rows, "cumulative_rows": MAX_TOTAL_ROWS,
                         "operations": args.max_operations, "seconds": args.max_seconds,
                         "combined_output_bytes": MAX_OUTPUT, "word_length": MAX_WORD,
                         "returned_letters": MAX_LETTERS, "assignments": 4, "hints": MAX_EDGES},
              "status": "candidate original local proofs; separate Lean checks required"}
    report_bytes = (json.dumps(report, indent=2, sort_keys=True) + "\n").encode()
    require(sum(map(len, outputs)) + (len(report_bytes) if report_path else 0) <= MAX_OUTPUT,
            "combined source/binding/report output ceiling reached")
    for path, data in snapshots.items():
        limit = MAX_RECORD if path == record_path else MAX_HEADER
        require(bounded_read(path, limit) == data, f"input changed during selected run: {path}")
    require(load_header()[0] == header, "catalogue header changed during selected run")
    budget.tick(0)
    if args.check:
        for path, data in zip(paths, outputs):
            require(bounded_read(path, MAX_OUTPUT) == data, f"generated bytes differ: {path.name}")
    else:
        # Each file is atomic; the pair is not a cross-file transaction.
        # A partial interrupted pair has no proof status or acceptance receipt.
        for path, data in zip(paths, outputs):
            atomic_write(path, data)
        if report_path:
            atomic_write(report_path, report_bytes)
    print(json.dumps({"source": SOURCE, "mode": "checked" if args.check else "written",
                      "operations": budget.operations, "rows": budget.inserted,
                      "branches": report["branches"], "outputs": report["outputs"]}, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (Refused, OSError, ValueError, TypeError, KeyError) as error:
        raise SystemExit(f"selected Schreier certificate refused: {error}") from None
