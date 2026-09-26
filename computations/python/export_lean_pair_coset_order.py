#!/usr/bin/env python3
"""One selected original-point compressed order certificate: b16_832 only.

Required --source b16_832 and exactly one of --write / --check. This producer
reads only the pinned, bounded catalogue header and original Lean generator
chunk. It tries at most fifteen partners of point zero to find an invariant
pair partition, then enumerates ONLY the induced eight-point top action.
Original sixteen-point representatives are retained along that word BFS;
the original group is never enumerated. Right-generator defects are encoded
in a correlated binary span and checked on the original points in Lean.

Immutable ceilings: 128 top rows, 500000 charged operations, 5 seconds,
128 KiB combined Lean/report output, 1 MiB header/chunk/source input, fifteen
pair candidates, eight pairs, two original generators and eight basis bits.
CLI limits may only lower these ceilings. Time checks are cooperative, not a
hard process/RSS limit. There is no dense multiplication table, subprocess,
compiler, network, legacy exporter import, bulk mode, or catalogue-order
premise. Emitted source is a candidate until its separate Lean check passes.
"""
from __future__ import annotations

import sys
sys.dont_write_bytecode = True

import argparse
import gzip
import hashlib
import json
import math
import os
from pathlib import Path
import tempfile
import time


ROOT = Path(__file__).resolve().parents[2]
SELF = Path(__file__).resolve()
FORMAL = ROOT / "formal/SymmetricSubgroupAsymptotics"
INPUT = ROOT / "certificates/data/binary_menu.jsonl.gz"
CHUNK = FORMAL / "GeneratedAction16/DataChunk021.lean"
OUTPUT = FORMAL / "GeneratedPrunedActions/CosetOrder16T832.lean"
SOURCE = "b16_832"
ORIGINAL_INDEX = 698
HEADER_SHA = "3e137e152a68aa3a3ac2f745f866082a2cb16f9d6d31bf1a09acfbb73cbdf1a1"
NODE_SHA = "0e40491ba44ca59bc1a51fdbcf8dc3b39932bf4e400275bb2b0a6b566aa5e4cd"
GENERATOR_SHA = "bf14947af75faabd664ce19ba8348fa038fbdd0921a770680c667fe552658b0e"
CHUNK_SHA = "4591539cc0aeb2fea6b57ab729b6c8fd60349edaf193a034c2a179f4cdddd3e8"
MAX_ROWS = 128
MAX_OPERATIONS = 500_000
MAX_SECONDS = 5.0
MAX_OUTPUT = 128 * 1024
MAX_INPUT = 1024 * 1024
MAX_COMPRESSED = 8 * 1024 * 1024
MAX_CANDIDATES = 15
MAX_PAIRS = 8
MAX_WORD_DEPTH = 127
GENERATOR_COUNT = 2
DEGREE = 16


class Refused(Exception):
    pass


def require(condition, message):
    if not condition:
        raise Refused(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def bounded_read(path, limit=MAX_INPUT):
    require(path.is_file() and not path.is_symlink(), f"not a regular input: {path}")
    with path.open("rb") as handle:
        data = handle.read(limit + 1)
    require(len(data) <= limit, f"input byte ceiling reached: {path}")
    return data


def read_header():
    require(INPUT.is_file() and not INPUT.is_symlink(), "missing/redirected catalogue")
    require(INPUT.stat().st_size <= MAX_COMPRESSED, "compressed input size ceiling reached")
    with gzip.open(INPUT, "rb") as handle:
        data = handle.readline(MAX_INPUT + 1)
    require(0 < len(data) <= MAX_INPUT and data.endswith(b"\n"),
            "selected header is incomplete or exceeds 1 MiB")
    require(digest(data) == HEADER_SHA, "pinned original header mismatch")
    return data


class Budget:
    def __init__(self, rows, operations, seconds):
        self.rows, self.limit, self.seconds = rows, operations, seconds
        self.started = time.monotonic()
        self.operations = 0
        self.pair_candidates = 0
        self.pair_states = 0
        self.top_insertions = 0

    def check_time(self):
        require(time.monotonic() - self.started <= self.seconds,
                "selected cooperative time ceiling reached")

    def charge(self, amount=1):
        self.operations += amount
        require(self.operations <= self.limit, "shared charged-operation ceiling reached")
        self.check_time()

    def compose(self, a, b):
        require(len(a) == len(b) and len(a) in (8, 16), "invalid permutation dimensions")
        self.charge(len(a) + 1)
        return tuple(a[x] for x in b)

    def inverse(self, p):
        self.charge(len(p))
        inverse = [0] * len(p)
        for i, x in enumerate(p):
            inverse[x] = i
        return tuple(inverse)


def selected_generators(header, budget):
    data = json.loads(header)
    require(isinstance(data, dict) and isinstance(data.get("nodes"), list),
            "missing original node list")
    matches = []
    for node in data["nodes"]:
        budget.charge()
        require(isinstance(node, dict), "malformed original node")
        if node.get("id") == SOURCE:
            matches.append(node)
    require(len(matches) == 1, "selected original node missing or duplicated")
    node = matches[0]
    require(digest(canonical(node)) == NODE_SHA, "pinned selected-node mismatch")
    require(node.get("degree") == DEGREE, "wrong original point count")
    raw = node.get("generators")
    require(isinstance(raw, list) and len(raw) == GENERATOR_COUNT,
            "wrong original ordered generator count")
    generators = []
    for row in raw:
        budget.charge(DEGREE)
        require(isinstance(row, list) and len(row) == DEGREE and
                all(type(x) is int for x in row) and sorted(row) == list(range(1, 17)),
                "invalid original generator permutation")
        generators.append(tuple(x - 1 for x in row))
    require(digest(canonical(generators)) == GENERATOR_SHA,
            "ordered original generator tuple mismatch")
    # The node's order and normalizer fields are deliberately never used.
    return generators


def invariant_pairs(generators, budget):
    """Orbit only an unordered pair; overlapping pair images reject a candidate."""
    for partner in range(1, MAX_CANDIDATES + 1):
        budget.charge()
        budget.pair_candidates += 1
        queue = [(0, partner)]
        seen = {queue[0]}
        used = {0, partner}
        cursor = 0
        valid = True
        budget.pair_states += 1
        while cursor < len(queue) and valid:
            pair = queue[cursor]
            for generator in generators:
                budget.charge(4)
                image = tuple(sorted((generator[pair[0]], generator[pair[1]])))
                if image in seen:
                    continue
                if image[0] in used or image[1] in used:
                    valid = False
                    break
                require(len(queue) < MAX_PAIRS, "pair-orbit state ceiling reached")
                seen.add(image)
                used.update(image)
                queue.append(image)
                budget.pair_states += 1
            cursor += 1
        if valid and len(queue) == MAX_PAIRS and used == set(range(DEGREE)):
            return sorted(queue), partner
    raise Refused("none of the fifteen original partners gives a complete invariant pair partition")


def top_search(generators, pairs, budget):
    block = [0] * DEGREE
    bit = [0] * DEGREE
    for i, pair in enumerate(pairs):
        for t, x in enumerate(pair):
            budget.charge()
            block[x], bit[x] = i, t
    top_generators = []
    for generator in generators:
        row = []
        for pair in pairs:
            budget.charge(2)
            require(block[generator[pair[0]]] == block[generator[pair[1]]],
                    "original generator does not preserve the selected pairs")
            row.append(block[generator[pair[0]]])
        require(sorted(row) == list(range(MAX_PAIRS)), "invalid induced top permutation")
        top_generators.append(tuple(row))
    top_rows = [tuple(range(MAX_PAIRS))]
    representatives = [tuple(range(DEGREE))]
    indices = {top_rows[0]: 0}
    parents, letters, depths = [0], [0], [0]
    transitions = []
    budget.top_insertions = 1
    cursor = 0
    while cursor < len(top_rows):
        edges = []
        for j, top_generator in enumerate(top_generators):
            top_product = budget.compose(top_rows[cursor], top_generator)
            budget.charge()
            target = indices.get(top_product)
            if target is None:
                require(len(top_rows) < budget.rows, "128-row induced-top ceiling reached")
                require(depths[cursor] < MAX_WORD_DEPTH, "representative word-depth ceiling reached")
                target = len(top_rows)
                indices[top_product] = target
                top_rows.append(top_product)
                representatives.append(budget.compose(representatives[cursor], generators[j]))
                parents.append(cursor)
                letters.append(j)
                depths.append(depths[cursor] + 1)
                budget.top_insertions += 1
                budget.charge(5)
            edges.append(target)
        transitions.append(edges)
        cursor += 1
    for i, representative in enumerate(representatives):
        budget.charge(DEGREE)
        require(sorted(representative) == list(range(DEGREE)), "invalid lifted original representative")
        for x in range(DEGREE):
            budget.charge()
            require(block[representative[x]] == top_rows[i][block[x]],
                    "original representative/top-row inconsistency")
    return {"block": block, "bit": bit, "top_rows": top_rows,
            "representatives": representatives, "next": transitions,
            "parents": parents, "letters": letters, "depths": depths}


def span_coordinates(masks, budget):
    """At most eight pivot bits; no enumeration of the binary span."""
    basis = []
    pivots = {}
    for mask in masks:
        value, code = mask, 0
        while value:
            budget.charge()
            pivot = value.bit_length() - 1
            if pivot in pivots:
                row, row_code = pivots[pivot]
                value ^= row
                code ^= row_code
            else:
                require(len(basis) < MAX_PAIRS, "binary basis exceeds eight coordinates")
                index = len(basis)
                basis.append(mask)
                pivots[pivot] = (value, code ^ (1 << index))
                break
    coefficients = []
    for mask in masks:
        value, code = mask, 0
        while value:
            budget.charge()
            pivot = value.bit_length() - 1
            require(pivot in pivots, "internal binary span failure")
            row, row_code = pivots[pivot]
            value ^= row
            code ^= row_code
        reconstructed = 0
        for j, row in enumerate(basis):
            budget.charge()
            if (code >> j) & 1:
                reconstructed ^= row
        require(reconstructed == mask, "binary coefficient reconstruction failed")
        coefficients.append(code)
    return basis, coefficients


def search(generators, budget):
    pairs, partner = invariant_pairs(generators, budget)
    result = top_search(generators, pairs, budget)
    representatives = result["representatives"]
    inverses = [budget.inverse(p) for p in representatives]
    masks = []
    for i, representative in enumerate(representatives):
        for j, generator in enumerate(generators):
            defect = budget.compose(budget.compose(representative, generator),
                                    inverses[result["next"][i][j]])
            mask = 0
            for b, (x, y) in enumerate(pairs):
                budget.charge(3)
                require({defect[x], defect[y]} == {x, y},
                        "original transition defect does not fix each physical pair")
                if defect[x] == y:
                    mask |= 1 << b
            masks.append(mask)
    basis, coefficients = span_coordinates(masks, budget)
    bound = len(representatives) * (1 << len(basis))
    require(bound <= 512, "correlated coset upper bound exceeds 512")
    result.update(pairs=pairs, partner=partner, inverses=inverses, defect_masks=masks,
                  basis=basis, coefficients=coefficients, order_upper_bound=bound)
    return result


def lookup(values, index, start=0):
    require(bool(values), "cannot emit an empty natural lookup")
    if len(values) == 1:
        return str(values[0])
    split = len(values) // 2
    return (f"(if {index} < {start + split} then {lookup(values[:split], index, start)} "
            f"else {lookup(values[split:], index, start + split)})")


def finite_cases(names):
    require(bool(names), "cannot assemble an empty row family")
    if len(names) == 1:
        return f"(Fin.cases {names[0]} (fun i => Fin.elim0 i))"
    split = len(names) // 2
    return (f"(Fin.addCases (m := {split}) (n := {len(names) - split}) "
            f"{finite_cases(names[:split])} {finite_cases(names[split:])})")


def permutation_code(row, budget):
    budget.charge(DEGREE)
    return sum(value << (4 * i) for i, value in enumerate(row))


def emit(result, budget):
    q, d = len(result["representatives"]), len(result["basis"])
    forward = [permutation_code(row, budget) for row in result["representatives"]]
    backward = [permutation_code(row, budget) for row in result["inverses"]]
    pairs = result["pairs"]
    next_values = [target for row in result["next"] for target in row]
    coefficients = result["coefficients"]
    column_body = (f"((({lookup(result['basis'], 't.val')} : ℕ) / 2 ^ i.val % 2 : ℕ) : ZMod 2)"
                   if d else "Fin.elim0 t")
    coefficient_body = (f"((({lookup(coefficients, '(i.val * 2 + j.val)')} : ℕ) / 2 ^ t.val % 2 : ℕ) : ZMod 2)"
                        if d else "Fin.elim0 t")
    text = f'''import SymmetricSubgroupAsymptotics.BinaryFlipCosetOrderBound
import SymmetricSubgroupAsymptotics.GeneratedAction16.DataChunk021

/-!
# Selected compressed original order bound: 16T832

Generated by export_lean_pair_coset_order.py from the pinned original ordered
generator tuple (common-family index 698). There are {q} representatives and
{d} correlated binary columns. Only the induced eight-point top action was
searched; no original-group rows or dense multiplication table were produced.
The theorem follows from the literal identity and original-point transition
equations below. Neither the catalogue order nor search success is a premise.
This is an order upper bound, not a complete action/normal registry.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryPrunedCosetOrder16T832

abbrev generators : Fin 2 → Equiv.Perm (Fin 16) :=
  BinaryActionData16.node832Generators

abbrev Original : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range generators)

private def frame : Fin 8 × ZMod 2 ≃ Fin 16 where
  toFun p := Fin.ofNat 16
    (if p.2.val = 0 then {lookup([p[0] for p in pairs], 'p.1.val')}
     else {lookup([p[1] for p in pairs], 'p.1.val')})
  invFun x := (Fin.ofNat 8 {lookup(result['block'], 'x.val')},
    (({lookup(result['bit'], 'x.val')} : ℕ) : ZMod 2))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def representativeImage (i : Fin {q}) (x : Fin 16) : Fin 16 :=
  Fin.ofNat 16 (({lookup(forward, 'i.val')} : ℕ) / 16 ^ x.val)

private def representativeInverse (i : Fin {q}) (x : Fin 16) : Fin 16 :=
  Fin.ofNat 16 (({lookup(backward, 'i.val')} : ℕ) / 16 ^ x.val)

private def RepresentativeChecked (i : Fin {q}) : Prop :=
  (∀ x : Fin 16, representativeInverse i (representativeImage i x) = x) ∧
  (∀ x : Fin 16, representativeImage i (representativeInverse i x) = x)

'''
    representative_names = []
    for i in range(q):
        budget.charge()
        name = f"representative_checked_{i:03d}"
        representative_names.append(name)
        text += f"private theorem {name} : RepresentativeChecked {i} := by\n  unfold RepresentativeChecked; decide +kernel\n\n"
    text += f'''private theorem representative_checked : ∀ i : Fin {q}, RepresentativeChecked i :=
  {finite_cases(representative_names)}

private def representatives (i : Fin {q}) : Equiv.Perm (Fin 16) where
  toFun := representativeImage i
  invFun := representativeInverse i
  left_inv := (representative_checked i).1
  right_inv := (representative_checked i).2

private def nextRow (i : Fin {q}) (j : Fin 2) : Fin {q} :=
  Fin.ofNat {q} {lookup(next_values, '(i.val * 2 + j.val)')}

private def columns (t : Fin {d}) (i : Fin 8) : ZMod 2 :=
  {column_body}

private def coefficients (i : Fin {q}) (j : Fin 2) (t : Fin {d}) : ZMod 2 :=
  {coefficient_body}

private def RowChecked (i : Fin {q}) : Prop :=
  ∀ j : Fin 2, ∀ p : Fin 8 × ZMod 2,
    (representatives i * generators j * (representatives (nextRow i j))⁻¹) (frame p) =
      frame (p.1, p.2 + BinaryFlipCoset.bits columns (coefficients i j) p.1)

'''
    names = []
    for i in range(q):
        budget.charge()
        name = f"row_checked_{i:03d}"
        names.append(name)
        text += f"private theorem {name} : RowChecked {i} := by\n  unfold RowChecked; decide +kernel\n\n"
    text += f'''private theorem row_checked : ∀ i : Fin {q}, RowChecked i :=
  {finite_cases(names)}

private theorem representative_identity : representatives 0 = 1 := by
  apply Equiv.ext
  exact (by decide +kernel : ∀ x : Fin 16, representatives 0 x = x)

private def certificate :
    BinaryFlipCosetOrderCertificate generators 8 {d} {q} where
  frame := frame
  columns := columns
  representatives := representatives
  identity := 0
  identity_eq := representative_identity
  next := nextRow
  coefficients := coefficients
  step := row_checked

theorem card_le_compressed : Nat.card Original ≤ {q} * 2 ^ {d} :=
  certificate.card_closure_le

theorem card_le : Nat.card Original ≤ 512 :=
  card_le_compressed.trans (by decide +kernel)

end SymmetricSubgroupAsymptotics.BinaryPrunedCosetOrder16T832

end
'''
    budget.check_time()
    return text.encode()


def private_report_path(raw):
    path = Path(raw).expanduser()
    require(path.is_absolute() and path.suffix == ".json", "report needs an absolute private JSON path")
    require(not path.is_symlink(), "refusing symbolic-link report")
    path = path.resolve()
    require(not path.is_relative_to(ROOT.resolve()), "report must be outside the publication repository")
    require(path.parent.is_dir(), "report parent directory must already exist")
    return path


def atomic_write(path, data):
    require(path.parent.is_dir() and not path.parent.is_symlink(), "unsafe/missing output directory")
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True, choices=[SOURCE])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--report")
    parser.add_argument("--max-rows", type=int, default=MAX_ROWS)
    parser.add_argument("--max-operations", type=int, default=MAX_OPERATIONS)
    parser.add_argument("--seconds", type=float, default=MAX_SECONDS)
    parser.add_argument("--max-output-bytes", type=int, default=MAX_OUTPUT)
    args = parser.parse_args()
    require(1 <= args.max_rows <= MAX_ROWS, "row limit may only lower the immutable ceiling")
    require(1 <= args.max_operations <= MAX_OPERATIONS, "operation limit may only lower the ceiling")
    require(math.isfinite(args.seconds) and 0 < args.seconds <= MAX_SECONDS,
            "time limit may only lower the immutable ceiling")
    require(1 <= args.max_output_bytes <= MAX_OUTPUT, "output limit may only lower the ceiling")
    require(not (args.check and args.report), "--check is read-only and forbids --report")
    report_path = private_report_path(args.report) if args.report else None
    budget = Budget(args.max_rows, args.max_operations, args.seconds)
    own = bounded_read(SELF)
    header = read_header()
    chunk = bounded_read(CHUNK)
    require(digest(chunk) == CHUNK_SHA, "pinned original Lean generator chunk mismatch")
    generators = selected_generators(header, budget)
    result = search(generators, budget)
    source = emit(result, budget)
    report = {
        "schema": "selected-original-pair-coset-order-v1",
        "source": SOURCE, "original_index": ORIGINAL_INDEX,
        "status": "candidate certificate; separate Lean check required",
        "producer_sha256": digest(own), "header_sha256": HEADER_SHA,
        "node_sha256": NODE_SHA, "original_generators_sha256": GENERATOR_SHA,
        "original_chunk_sha256": CHUNK_SHA, "generated_source_sha256": digest(source),
        "generated_source_bytes": len(source), "charged_operations": budget.operations,
        "pair_candidates_tried": budget.pair_candidates, "pair_orbit_states": budget.pair_states,
        "selected_partner_zero_based": result["partner"], "pairs_zero_based": result["pairs"],
        "top_rows": len(result["top_rows"]), "binary_columns": len(result["basis"]),
        "order_upper_bound": result["order_upper_bound"],
        "basis_masks": result["basis"], "coefficient_masks": result["coefficients"],
        "top_generators_original_order": [tuple(result["block"][g[p[0]]] for p in result["pairs"])
                                          for g in generators],
        "representative_parents": result["parents"], "representative_letters": result["letters"],
        "maximum_representative_word_depth": max(result["depths"]),
        "original_representatives_sha256": digest(canonical(result["representatives"])),
        "limits": {"top_rows": args.max_rows, "operations": args.max_operations,
                   "seconds": args.seconds, "output_bytes": args.max_output_bytes,
                   "header_bytes_per_read": MAX_INPUT, "header_reads": 2,
                   "pair_candidates": MAX_CANDIDATES, "pair_states_per_candidate": MAX_PAIRS},
        "scope": "original generated order bound only; no action/normal coverage claim",
    }
    report_bytes = (json.dumps(report, indent=2, sort_keys=True) + "\n").encode()
    require(len(source) + (len(report_bytes) if report_path else 0) <= args.max_output_bytes,
            "combined selected output ceiling reached")
    require(bounded_read(SELF) == own and bounded_read(CHUNK) == chunk and read_header() == header,
            "selected producer/original inputs changed during the run")
    budget.check_time()
    if args.check:
        require(bounded_read(OUTPUT, args.max_output_bytes) == source,
                "generated source differs from deterministic selected replay")
    else:
        if OUTPUT.exists():
            previous = bounded_read(OUTPUT, args.max_output_bytes)
            require(b"Generated by export_lean_pair_coset_order.py" in previous,
                    "refusing to replace output not owned by this producer")
        atomic_write(OUTPUT, source)
        if report_path:
            atomic_write(report_path, report_bytes)
    print(json.dumps({"source": SOURCE, "mode": "check" if args.check else "write",
                      "top_rows": report["top_rows"], "binary_columns": report["binary_columns"],
                      "order_upper_bound": result["order_upper_bound"],
                      "charged_operations": budget.operations, "source_bytes": len(source),
                      "source_sha256": digest(source)}, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (Refused, OSError, ValueError, TypeError, KeyError) as exc:
        print(f"REFUSED: {exc}", file=sys.stderr)
        raise SystemExit(2)
