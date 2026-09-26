#!/usr/bin/env python3
"""Produce one bounded original-generator square certificate, never a batch.

Examples (the report directory must already exist outside this repository):
  python3 -B computations/python/export_lean_derived_square_words.py \
    --master 1082 --report /private/path/derived-1082.json
  python3 -B computations/python/export_lean_derived_square_words.py \
    --master 1082 --write --report /private/path/derived-1082.json
  python3 -B computations/python/export_lean_derived_square_words.py \
    --master 1082 --check

The default only searches and prints a compact summary. --write installs the
single canonical Lean module; --check recomputes and compares its exact bytes,
without creating or editing any file. --report is optional private search
metadata and cannot be combined with --check. No compiler is invoked.

Multiplication is (a*b)(x)=a(b(x)), matching Lean. Every visited element is a
product of explicit derived words, not a source-group enumeration. Search
does not establish order, normal coverage, or a Lean theorem. The generated
module independently checks literal Fin16 point equations with decide +kernel.
"""
from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
import hashlib
import json
import math
import os
from pathlib import Path
import re
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "certificates/data/base_alphabet.json"
OUT = ROOT / "formal/SymmetricSubgroupAsymptotics"
# Values are JSON indices in the exact existing Lean tuple order.
SPECS = {
    1082: (27, (2, 3, 4, 5, 0, 1)),
    1083: (27, (2, 3, 4, 5, 6, 0, 1)),
    1084: (27, (3, 2, 4, 5, 6, 0, 1)),
    1332: (34, (3, 4, 1, 2, 0)),
    1547: (39, (0, 1, 4, 5, 2, 3)),
}
MAX_STATES = 4096
MAX_MOVES = 4096
MAX_OPERATIONS = 2_000_000
MAX_SECONDS = 30.0
MAX_WORD_NODES = 4096
MAX_WORD_DEPTH = 128
MAX_INPUT_BYTES = 1024 * 1024
MAX_OUTPUT_BYTES = 1024 * 1024
CONJUGATION_ROUNDS = 4
Perm = tuple[int, ...]


class CertificateError(ValueError):
    """The selected bounded certificate could not be produced or replayed."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CertificateError(message)


def mul(a: Perm, b: Perm) -> Perm:
    return tuple(a[x] for x in b)


def inv(a: Perm) -> Perm:
    result = [0] * len(a)
    for i, x in enumerate(a):
        result[x] = i
    return tuple(result)


@dataclass(frozen=True)
class Word:
    tag: str
    args: tuple
    nodes: int
    depth: int


def word(tag: str, *args: int | Word) -> Word:
    children = [arg for arg in args if isinstance(arg, Word)]
    nodes = 1 + sum(child.nodes for child in children)
    depth = 1 + max((child.depth for child in children), default=0)
    require(nodes <= MAX_WORD_NODES, "expanded derived-word node ceiling reached")
    require(depth <= MAX_WORD_DEPTH, "derived-word depth ceiling reached")
    return Word(tag, args, nodes, depth)


def lean_word(w: Word, nested: bool = False) -> str:
    if w.tag == "one":
        return ".one"
    if w.tag == "comm":
        result = f".comm {w.args[0]} {w.args[1]}"
    elif w.tag == "inv":
        result = f".inv {lean_word(w.args[0], True)}"
    elif w.tag == "mul":
        result = f".mul {lean_word(w.args[0], True)} {lean_word(w.args[1], True)}"
    else:
        require(w.tag in ("conj", "conjInv"), "unknown word constructor")
        result = f".{w.tag} {w.args[0]} {lean_word(w.args[1], True)}"
    return f"({result})" if nested else result


def json_word(w: Word) -> list:
    return [w.tag, *(json_word(arg) if isinstance(arg, Word) else arg for arg in w.args)]


def evaluate(w: Word, g: list[Perm]) -> Perm:
    if w.tag == "one":
        return tuple(range(16))
    if w.tag == "comm":
        a, b = g[w.args[0]], g[w.args[1]]
        return mul(mul(mul(a, b), inv(a)), inv(b))
    if w.tag == "inv":
        return inv(evaluate(w.args[0], g))
    if w.tag == "mul":
        return mul(evaluate(w.args[0], g), evaluate(w.args[1], g))
    a = g[w.args[0]]
    if w.tag == "conjInv":
        a = inv(a)
    return mul(mul(a, evaluate(w.args[1], g)), inv(a))


@dataclass
class Budget:
    max_states: int
    max_operations: int
    seconds: float
    start: float
    operations: int = 0

    def time_check(self) -> None:
        require(time.monotonic() - self.start <= self.seconds,
                "selected wall-time ceiling reached")

    def operation(self) -> None:
        self.operations += 1
        require(self.operations <= self.max_operations,
                "selected operation ceiling reached")
        self.time_check()


def bounded_read(path: Path) -> bytes:
    require(path.stat().st_size <= MAX_INPUT_BYTES, f"input byte ceiling: {path.name}")
    with path.open("rb") as stream:
        content = stream.read(MAX_INPUT_BYTES + 1)
    require(len(content) <= MAX_INPUT_BYTES, f"input grew beyond byte ceiling: {path.name}")
    return content


def unique_object(pairs: list[tuple]) -> dict:
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON object key: {key}")
        result[key] = value
    return result


def lookup(values: list[str], start: int = 0) -> str:
    """The selected original data producer's balanced tuple selector."""
    if len(values) == 1:
        return values[0]
    split = len(values) // 2
    return (f"(if j.val < {start + split} then {lookup(values[:split], start)} "
            f"else {lookup(values[split:], start + split)})")


def selected_generators(master: int) -> tuple[list[Perm], dict[Path, bytes]]:
    chunk, order = SPECS[master]
    source_path = OUT / f"GeneratedAction16/DataChunk{chunk:03d}.lean"
    data_bytes, source_bytes = bounded_read(DATA), bounded_read(source_path)
    data = json.loads(data_bytes, object_pairs_hook=unique_object)
    require(isinstance(data, dict) and isinstance(data.get("actions"), list),
            "invalid original action catalogue")
    selected = [a for a in data["actions"] if isinstance(a, dict)
                and a.get("catalogue_locator") == [16, master]]
    require(len(selected) == 1, "selected original master absent or duplicated")
    action = selected[0]
    require(action.get("degree") == 16, "selected action degree changed")
    raw = action.get("generators")
    require(isinstance(raw, list) and len(raw) == len(order), "original generator count changed")
    require(sorted(order) == list(range(len(raw))), "invalid fixed original/Lean index permutation")
    original = []
    for images in raw:
        require(isinstance(images, list) and len(images) == 16
                and all(type(x) is int for x in images)
                and sorted(images) == list(range(1, 17)), "invalid original permutation")
        original.append(tuple(x - 1 for x in images))
    generators = [original[i] for i in order]
    source_text = source_bytes.decode("utf-8")
    declarations = re.findall(rf"^def node{master}Generator(\d+) :", source_text, re.M)
    require(declarations == [str(i) for i in range(len(generators))],
            "selected Lean generator declarations changed")
    for i, permutation in enumerate(generators):
        forward = ",".join(map(str, permutation))
        backward = ",".join(map(str, inv(permutation)))
        expected = f'''def node{master}Generator{i} : Equiv.Perm (Fin 16) where
  toFun x := (#[{forward}] : Array (Fin 16))[x.val]!
  invFun x := (#[{backward}] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
'''
        require(source_text.count(expected) == 1,
                f"original JSON/Lean forward or inverse literal disagreement at generator {i}")
    choices = [f"node{master}Generator{i}" for i in range(len(generators))]
    selector = f'''def node{master}Generators (j : Fin {len(generators)}) : Equiv.Perm (Fin 16) :=
  {lookup(choices)}
'''
    require(source_text.count(selector) == 1, "selected original Lean tuple selector changed")
    return generators, {DATA: data_bytes, source_path: source_bytes}


def search(g: list[Perm], budget: Budget) -> tuple[list[Word], list[dict]]:
    identity = tuple(range(16))
    targets = {mul(x, x) for x in g}
    moves: dict[Perm, Word] = {}

    def add(permutation: Perm, tag: str, *args: int | Word) -> None:
        if permutation != identity and permutation not in moves:
            require(len(moves) < MAX_MOVES, "derived-move ceiling reached")
            moves[permutation] = word(tag, *args)

    for i, a in enumerate(g):
        for j, b in enumerate(g):
            budget.operation()
            add(mul(mul(mul(a, b), inv(a)), inv(b)), "comm", i, j)
    visited = {identity: word("one")}
    rounds = []
    for depth in range(CONJUGATION_ROUNDS):
        if depth:
            for permutation, expression in list(moves.items()):
                for i, a in enumerate(g):
                    budget.operation()
                    add(mul(mul(a, permutation), inv(a)), "conj", i, expression)
                    budget.operation()
                    add(mul(mul(inv(a), permutation), a), "conjInv", i, expression)
        for permutation, expression in list(moves.items()):
            budget.time_check()
            add(inv(permutation), "inv", expression)
        queue = deque(visited)
        while queue and not targets <= visited.keys():
            permutation = queue.popleft()
            for step, expression in moves.items():
                budget.operation()
                product = mul(permutation, step)
                if product in visited:
                    continue
                require(len(visited) < budget.max_states, "selected state ceiling reached")
                visited[product] = (expression if permutation == identity
                                    else word("mul", visited[permutation], expression))
                queue.append(product)
        rounds.append({"conjugation_depth": depth, "moves": len(moves), "visited": len(visited)})
        if targets <= visited.keys():
            break
    require(targets <= visited.keys(), "no witness within selected conjugation depth")
    result = [visited[mul(x, x)] for x in g]
    for permutation, expression in zip(g, result):
        budget.time_check()
        require(evaluate(expression, g) == mul(permutation, permutation),
                "derived-word self-verification failed")
    budget.time_check()
    return result, rounds


def emit(master: int, words: list[Word]) -> bytes:
    chunk, _ = SPECS[master]
    count = len(words)
    leading = 0
    while leading < count and words[leading].tag == "one":
        leading += 1
    first_count = max(1, leading)
    lines = ["  ![" + ", ".join(lean_word(w) for w in words[:first_count])]
    for expression in words[first_count:]:
        lines[-1] += ","
        lines.append("    " + lean_word(expression))
    lines[-1] += "]"
    literal = "\n".join(lines)
    text = f'''import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.GeneratedAction16.DataChunk{chunk:03d}

/-! Original-generator square certificates on the literal 16T{master} closure.
The finite point equations are checked by the kernel. No order, catalogue
coverage, or ambient symmetric-group derived membership is inferred. -/
set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics.BinaryCarrierDerived16T{master}

def squareWords : Fin {count} → DerivedGeneratorWord (Fin {count}) :=
{literal}

theorem squareWords_pointwise : ∀ (i : Fin {count}) (x : Fin 16),
    BinaryActionData16.node{master}Generators i (BinaryActionData16.node{master}Generators i x) =
      (squareWords i).eval BinaryActionData16.node{master}Generators x := by
  decide +kernel

theorem evaluationKernel_eq_commutator :
    (primeAbelianizationGroupMap 2
      (Subgroup.closure (Set.range BinaryActionData16.node{master}Generators))).ker =
      commutator (Subgroup.closure (Set.range BinaryActionData16.node{master}Generators)) :=
  binaryEvaluationKernel_permClosure_eq_commutator_of_pointwise
    BinaryActionData16.node{master}Generators squareWords squareWords_pointwise

end SymmetricSubgroupAsymptotics.BinaryCarrierDerived16T{master}
'''
    content = text.encode("utf-8")
    require(len(content) <= MAX_OUTPUT_BYTES, "Lean output byte ceiling reached")
    return content


def atomic_write(path: Path, content: bytes) -> None:
    require(path.parent.is_dir(), f"output parent directory does not exist: {path.parent}")
    require(not path.is_symlink(), "refusing to overwrite an output symlink")
    require(len(content) <= MAX_OUTPUT_BYTES, "output byte ceiling reached")
    temporary_path = None
    try:
        with tempfile.NamedTemporaryFile(dir=path.parent, prefix=path.name + ".",
                                         suffix=".tmp", delete=False) as stream:
            temporary_path = Path(stream.name)
            stream.write(content)
        os.replace(temporary_path, path)
    finally:
        if temporary_path is not None and temporary_path.exists():
            temporary_path.unlink()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--master", required=True, type=int, choices=SPECS)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="compare exact Lean bytes, no writes")
    mode.add_argument("--write", action="store_true", help="write the one canonical Lean module")
    parser.add_argument("--report", type=Path, help="private JSON metadata, outside publication")
    parser.add_argument("--max-states", type=int, default=1024)
    parser.add_argument("--max-operations", type=int, default=1_000_000)
    parser.add_argument("--seconds", type=float, default=10.0)
    args = parser.parse_args()
    if not (1 <= args.max_states <= MAX_STATES
            and 1 <= args.max_operations <= MAX_OPERATIONS
            and math.isfinite(args.seconds) and 0 < args.seconds <= MAX_SECONDS):
        parser.error("selected ceilings: 4096 states, 2000000 operations, 30 seconds")
    if args.check and args.report is not None:
        parser.error("--check is strictly read-only and cannot be combined with --report")
    report_path = None
    if args.report is not None:
        require(not args.report.is_symlink(), "private report must not be a symlink")
        report_path = args.report.resolve()
        require(not report_path.is_relative_to(ROOT), "--report must be outside publication")
        require(report_path.suffix == ".json" and report_path.parent.is_dir(),
                "--report requires a .json path in an existing private directory")
    budget = Budget(args.max_states, args.max_operations, args.seconds, time.monotonic())
    generators, snapshots = selected_generators(args.master)
    budget.time_check()
    words, rounds = search(generators, budget)
    content = emit(args.master, words)
    target = OUT / f"BinaryCarrierDerived16T{args.master}.lean"
    require(OUT.resolve().is_relative_to(ROOT) and not target.is_symlink(),
            "canonical output directory or file escapes publication")
    for source_path, source_bytes in snapshots.items():
        require(bounded_read(source_path) == source_bytes, "original input changed during production")
    budget.time_check()
    if args.check:
        require(target.is_file(), f"selected canonical Lean module is missing: {target.name}")
        require(bounded_read(target) == content, f"selected Lean bytes differ: {target.name}")
    elif args.write:
        if not target.is_file() or bounded_read(target) != content:
            atomic_write(target, content)
    chunk, order = SPECS[args.master]
    result = {
        "master": args.master, "chunk": chunk, "original_to_lean_order": list(order),
        "original_data_sha256": hashlib.sha256(snapshots[DATA]).hexdigest(),
        "lean_source_sha256": hashlib.sha256(snapshots[OUT / f"GeneratedAction16/DataChunk{chunk:03d}.lean"]).hexdigest(),
        "producer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "operations": budget.operations, "seconds": time.monotonic() - budget.start,
        "rounds": rounds,
        "limits": {"states": args.max_states, "operations": args.max_operations,
                   "seconds": args.seconds, "moves": MAX_MOVES,
                   "word_nodes": MAX_WORD_NODES, "word_depth": MAX_WORD_DEPTH,
                   "conjugation_rounds": CONJUGATION_ROUNDS,
                   "input_bytes": MAX_INPUT_BYTES, "output_bytes": MAX_OUTPUT_BYTES},
        "words": [json_word(w) for w in words],
        "lean_words": [lean_word(w) for w in words],
        "module": str(target.relative_to(ROOT)),
        "module_sha256": hashlib.sha256(content).hexdigest(),
        "checked_bytes": args.check, "write_requested": args.write,
        "scope": "Untrusted witness producer only; no order, coverage, normality or Lean theorem claim.",
    }
    if report_path is not None:
        atomic_write(report_path, (json.dumps(result, indent=2) + "\n").encode("utf-8"))
    print(json.dumps({key: result[key] for key in
                      ("master", "operations", "seconds", "rounds", "module",
                       "module_sha256", "checked_bytes", "write_requested")}, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (CertificateError, OSError, UnicodeError, RecursionError, json.JSONDecodeError) as error:
        print(f"selected derived-square certificate: {error}", file=sys.stderr)
        raise SystemExit(2)
