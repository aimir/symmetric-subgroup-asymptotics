#!/usr/bin/env python3
"""Export complete normal registries for the two split-frontier base tops.

The ordinary width-eight normal dataset deliberately omits the carrier-base
actions.  The degree-sixteen split frontier needs only 8T18 and 8T22, both
of order 32.  This selected producer enumerates their literal subgroups from
the committed generators, keeps the normal ones, and feeds them through the
same Lean quotient-row certificate exporter as the ordinary registry.  The
enumeration supplies witnesses only; registry completeness is proved again
in Lean from the checked central-involution edges.
"""

from pathlib import Path
import argparse
import gzip
import json
import sys

sys.dont_write_bytecode = True

from export_lean_menu_cayley import compose, table
from export_lean_normal_registry import emit, emit_registry


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_NODES = ("b8_18", "b8_22")


def inverse(p):
    return tuple(p.index(i) for i in range(len(p)))


def unpack(code, width):
    return tuple((code // width**i) % width for i in range(width))


def closure(generators, width):
    certificate = table(tuple(generators), width)
    return frozenset(unpack(code, width) for code in certificate["codes"])


def all_subgroups(group, width):
    identity = tuple(range(width))
    seen = {frozenset((identity,))}
    todo = list(seen)
    elements = tuple(sorted(group))
    for subgroup in todo:
        for x in elements:
            if x in subgroup:
                continue
            enlarged = closure(tuple(subgroup) + (x,), width)
            if enlarged not in seen:
                seen.add(enlarged)
                todo.append(enlarged)
    return seen


def is_normal(group, subgroup):
    inverses = {g: inverse(g) for g in group}
    return all(
        compose(compose(g, x), inverses[g]) in subgroup
        for g in group
        for x in subgroup
    )


def generators_of(subgroup, width):
    identity = tuple(range(width))
    generated = frozenset((identity,))
    result = []
    for x in sorted(subgroup):
        if x not in generated:
            result.append(x)
            generated = closure(result, width)
    assert generated == subgroup
    return result


def one_based(permutation):
    return [x + 1 for x in permutation]


def complete_record(node):
    width = node["degree"]
    source_generators = tuple(tuple(x - 1 for x in g) for g in node["generators"])
    group = closure(source_generators, width)
    normals = sorted(
        (h for h in all_subgroups(group, width) if is_normal(group, h)),
        key=lambda h: (len(h), tuple(sorted(h))),
    )
    index = {h: i for i, h in enumerate(normals)}
    rows = []
    for h in normals:
        children = [
            index[k] + 1
            for k in normals
            if len(k) == 2 * len(h) and h.issubset(k)
        ]
        rows.append(
            {
                "kind": "split_top_normal",
                "normal_generators": [one_based(x) for x in generators_of(h, width)],
                "children": children,
            }
        )
    return {"id": node["id"], "kind": "action", "normals": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--node", action="append", choices=DEFAULT_NODES)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    with gzip.open(ROOT / "certificates/data/binary_menu.jsonl.gz", "rt") as stream:
        metadata = json.loads(next(stream))
    nodes = {node["id"]: node for node in metadata["nodes"]}

    for name in args.node or DEFAULT_NODES:
        node = nodes[name]
        record = complete_record(node)
        for path, source in (emit(node, record), emit_registry(node, record)):
            payload = source.encode()
            if args.check:
                if not path.exists() or path.read_bytes() != payload:
                    raise SystemExit(f"Stale generated file {path}")
            elif not path.exists() or path.read_bytes() != payload:
                path.write_bytes(payload)
            print(path.relative_to(ROOT))


if __name__ == "__main__":
    main()
