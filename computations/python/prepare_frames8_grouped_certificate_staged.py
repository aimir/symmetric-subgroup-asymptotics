#!/usr/bin/env python3
"""Prepare one grouped eight-frame top and its rows in bounded stages.

The older selected preparer deliberately performs every top, normal-lattice,
radical, and module check in one process.  Some order-576 and order-1152 tops
exceed its 40M-operation ceiling.  This companion keeps the same certificate
semantics but gives every expensive normal-lattice cell its own bounded
process:

* ``top`` checks the Cayley table, conjugacy cover, and normal-state list;
* ``normality``, ``transition``, and ``radical`` check one explicit cell;
* ``assemble-top`` requires the complete rectangular collection of cells;
* ``row`` checks one local quotient and one binary module over that top.

It never scans for work and never invokes Lean or another exporter.  The
grouped batch driver supplies every state and class index explicitly.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import tempfile

import prepare_frames8_selected_top_certificate as base


TOP_SCHEMA = "frames8-grouped-top-structure-v1"
ASSEMBLED_SCHEMA = "frames8-selected-top-certificate-v1"
CHUNK_SCHEMA = "frames8-grouped-top-chunk-v1"
INPUT_LIMIT = 20 * 1024 * 1024
OUTPUT_LIMIT = 20 * 1024 * 1024


def read(path: Path, schema: str | None = None) -> dict:
    base.require(path.is_file() and not path.is_symlink(),
                 f"missing or redirected input {path}")
    raw = path.read_bytes()
    base.require(len(raw) <= INPUT_LIMIT, "grouped input ceiling reached")
    value = json.loads(raw)
    base.require(isinstance(value, dict), "grouped input is not an object")
    if schema is not None:
        base.require(value.get("schema") == schema,
                     f"unexpected grouped schema in {path}")
    return value


def write(path: Path, value: dict, force: bool) -> None:
    payload = (json.dumps(value, separators=(",", ":")) + "\n").encode()
    base.require(len(payload) <= OUTPUT_LIMIT, "grouped output ceiling reached")
    base.require(force or not path.exists(), "output exists; use --force")
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("wb", delete=False, dir=path.parent,
                                     prefix=path.name + ".",
                                     suffix=".partial") as stream:
        temporary = Path(stream.name)
        stream.write(payload)
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def budget(args: argparse.Namespace) -> base.Budget:
    base.require(1 <= args.operation_limit <= 40_000_000,
                 "operation limit outside selected ceiling")
    base.require(1.0 <= args.seconds_limit <= 300.0,
                 "time limit outside selected ceiling")
    return base.Budget(operation_limit=args.operation_limit,
                       seconds_limit=args.seconds_limit)


def prepare_top(binding: dict, work: base.Budget) -> dict:
    base.require(binding.get("schema") == base.BINDING_SCHEMA,
                 "unexpected selected binding schema")
    base.require(binding.get("bindings_sha256") == base.BINDINGS_SHA256,
                 "selected binding source digest changed")
    generators = base.permutation_rows(binding["top_generators"], 8, work)
    top = base.generator_enumeration(
        generators, 8, work, max_states=base.MAX_TOP_ORDER)
    base.require(len(top.rows) == binding["top_order"] <= base.MAX_TOP_ORDER,
                 "literal top order mismatch")
    cayley = base.positive_cayley(generators, 8, len(top.rows), work)

    representatives = base.permutation_rows(
        binding["class_representatives"], 8, work)
    class_sizes = binding["class_sizes"]
    base.require(len(representatives) == len(class_sizes) <= base.MAX_CLASSES,
                 "invalid selected class list")
    class_sets, centralizers = [], []
    for representative, supplied_size in zip(representatives, class_sizes):
        base.require(representative in top.position,
                     "class representative is outside the top")
        conjugates = {base.conjugate(g, representative, work) for g in top.rows}
        centralizer = [g for g in top.rows
                       if base.compose(g, representative, work) ==
                       base.compose(representative, g, work)]
        base.require(len(conjugates) == supplied_size,
                     "supplied conjugacy class size mismatch")
        base.require(len(conjugates) * len(centralizer) == len(top.rows),
                     "class/centralizer orbit-stabilizer mismatch")
        class_sets.append(conjugates)
        centralizers.append(len(centralizer))
    base.require(all(class_sets[i].isdisjoint(class_sets[j])
                     for i in range(len(class_sets)) for j in range(i)),
                 "selected conjugacy classes overlap")
    base.require(sum(map(len, class_sets)) == len(top.rows),
                 "selected conjugacy classes do not exhaust the top")
    class_code = []
    for row1 in cayley["rows"]:
        row = tuple(value - 1 for value in row1)
        labels = [i for i, conjugacy_class in enumerate(class_sets)
                  if row in conjugacy_class]
        base.require(len(labels) == 1,
                     "literal top row has no unique class label")
        class_code.append(labels[0])

    raw_normal_generators = binding["normal_generators"]
    normal_orders = binding["normal_orders"]
    base.require(isinstance(raw_normal_generators, list) and
                 len(raw_normal_generators) == len(normal_orders) <=
                 base.MAX_NORMALS, "invalid selected normal list")
    parsed = [base.permutation_rows(row, 8, work)
              for row in raw_normal_generators]
    width = max([1] + [len(row) for row in parsed])
    one = base.identity(8)
    padded = []
    seen: set[frozenset[tuple[int, ...]]] = set()
    for generators0, supplied_order in zip(parsed, normal_orders):
        generators1 = generators0 + [one] * (width - len(generators0))
        enumeration = base.generator_enumeration(
            generators1, 8, work, max_states=base.MAX_TOP_ORDER)
        base.require(len(enumeration.rows) == supplied_order,
                     "normal-state order mismatch")
        key = frozenset(enumeration.rows)
        base.require(key not in seen, "selected normal states are duplicated")
        seen.add(key)
        base.require(set(enumeration.rows) <= set(top.rows),
                     "normal state escaped the literal top")
        padded.append([[x + 1 for x in g] for g in generators1])

    return {
        "schema": TOP_SCHEMA,
        "source_row": binding["row"],
        "top_index": binding["top_index"],
        "top_order": len(top.rows),
        "generators": binding["top_generators"],
        "cayley": cayley,
        "class_representatives": binding["class_representatives"],
        "class_sizes": class_sizes,
        "centralizer_orders": centralizers,
        "class_code": class_code,
        "normal_generator_width": width,
        "normal_generators": padded,
        "normal_orders": normal_orders,
        "state_count": len(normal_orders),
        "class_count": len(class_sizes),
        "binding": binding,
    }


def reconstruct(value: dict, work: base.Budget):
    generators = base.permutation_rows(value["generators"], 8, work)
    top = base.generator_enumeration(
        generators, 8, work, max_states=base.MAX_TOP_ORDER)
    base.require(len(top.rows) == value["top_order"], "top reconstruction mismatch")
    representatives = base.permutation_rows(
        value["class_representatives"], 8, work)
    parsed = [base.permutation_rows(row, 8, work)
              for row in value["normal_generators"]]
    states = []
    for generators0, order in zip(parsed, value["normal_orders"]):
        enumeration = base.generator_enumeration(
            generators0, 8, work, max_states=base.MAX_TOP_ORDER)
        base.require(len(enumeration.rows) == order,
                     "normal-state reconstruction mismatch")
        states.append({"generators": generators0,
                       "rows": enumeration.rows,
                       "enumeration": enumeration})
    lookup = {frozenset(state["rows"]): i for i, state in enumerate(states)}
    base.require(len(lookup) == len(states), "normal-state lookup collision")
    for state in states:
        state["all_states"] = states
    return generators, top, representatives, states, lookup


def normality_chunk(value: dict, state: int, work: base.Budget) -> dict:
    generators, _top, _reps, states, _lookup = reconstruct(value, work)
    base.require(0 <= state < len(states), "normality state out of range")
    return {"schema": CHUNK_SCHEMA, "kind": "normality", "state": state,
            "value": base.normality_words(
                generators, states[state]["generators"], 8, work,
                max_states=base.MAX_TOP_ORDER)}


def transition_chunk(value: dict, state: int, class_index: int,
                     work: base.Budget) -> dict:
    generators, top, reps, states, lookup = reconstruct(value, work)
    base.require(0 <= state < len(states), "transition state out of range")
    base.require(0 <= class_index < len(reps), "transition class out of range")
    child_group = base.normal_closure_child(
        top, states[state]["generators"], reps[class_index], 8, work)
    child = lookup.get(frozenset(child_group.rows))
    base.require(child is not None, "normal join escaped the selected state list")
    transition = base.join_transition_words(
        generators, states[state]["generators"], reps[class_index],
        states[child]["generators"], 8, work,
        max_states=base.MAX_TOP_ORDER)
    return {"schema": CHUNK_SCHEMA, "kind": "transition", "state": state,
            "class": class_index, "child": child, "value": transition}


def radical_chunk(value: dict, state: int, work: base.Budget) -> dict:
    generators, _top, _reps, states, lookup = reconstruct(value, work)
    base.require(0 <= state < len(states), "radical state out of range")
    return {"schema": CHUNK_SCHEMA, "kind": "radical", "state": state,
            "value": base.radical_search(generators, states[state], lookup, work)}


def assemble_top(value: dict, chunks: Path) -> dict:
    n, c = value["state_count"], value["class_count"]
    normality, children, transitions, radicals = [], [], [], []
    for i in range(n):
        h = read(chunks / f"normality-{i}.json", CHUNK_SCHEMA)
        r = read(chunks / f"radical-{i}.json", CHUNK_SCHEMA)
        base.require((h.get("kind"), h.get("state")) == ("normality", i),
                     "mislabelled normality chunk")
        base.require((r.get("kind"), r.get("state")) == ("radical", i),
                     "mislabelled radical chunk")
        normality.append(h["value"])
        radicals.append(r["value"])
        child_row, transition_row = [], []
        for j in range(c):
            t = read(chunks / f"transition-{i}-{j}.json", CHUNK_SCHEMA)
            base.require((t.get("kind"), t.get("state"), t.get("class")) ==
                         ("transition", i, j), "mislabelled transition chunk")
            child_row.append(t["child"])
            transition_row.append(t["value"])
        children.append(child_row)
        transitions.append(transition_row)
    result = dict(value)
    result.update({"schema": ASSEMBLED_SCHEMA, "grouped_top_assembled": True,
                   "normality": normality,
                   "children": children, "transitions": transitions,
                   "radicals": radicals})
    return result


def prepare_row(top_value: dict, binding: dict, module: dict,
                work: base.Budget) -> dict:
    base.require(binding.get("schema") == base.BINDING_SCHEMA,
                 "unexpected selected binding schema")
    base.require(binding.get("bindings_sha256") == base.BINDINGS_SHA256,
                 "selected binding source digest changed")
    base.require(module.get("schema") == base.MODULE_SCHEMA,
                 "unexpected selected module schema")
    base.require(module.get("source_sha256") == base.FRAMES_SHA256,
                 "selected module source digest changed")
    base.require(binding.get("row") == module.get("source_row"),
                 "binding/module row mismatch")
    base.require(binding.get("top_index") == top_value["top_index"] ==
                 module.get("top_id") - 1, "grouped top mismatch")
    base.require(binding.get("top_order") == top_value["top_order"] ==
                 module.get("top_order"), "grouped top order mismatch")
    base.require(binding.get("top_generators") == top_value["generators"],
                 "grouped top generators changed")
    base.require(binding.get("kernel_order") ==
                 module.get("stabilizer_kernel_order"), "kernel order mismatch")
    base.require(module.get("local_quotient_order") in (3, 6),
                 "unexpected local quotient order")
    generators = base.permutation_rows(top_value["generators"], 8, work)
    top = base.generator_enumeration(
        generators, 8, work, max_states=base.MAX_TOP_ORDER)
    base.require(len(top.rows) == top_value["top_order"],
                 "row top reconstruction mismatch")
    rank = max(row["head_rank"] for row in top_value["radicals"])
    base.require(rank == module["top_relative_binary_rank"] <= 2,
                 "top relative binary-rank mismatch")
    induced = base.validate_induced_binding(
        binding, top, module["local_quotient_order"], work)
    base.validate_binary_basis(binding, module, work)
    base.validate_module_provenance(module, work)
    result = {key: value for key, value in top_value.items()
              if key not in ("state_count", "class_count")}
    result.update({"schema": "frames8-selected-top-certificate-v1",
                   "source_row": binding["row"],
                   "induced_binding": induced,
                   "module_certificate": module, "binding": binding})
    return result


def add_limits(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--operation-limit", type=int, default=40_000_000)
    parser.add_argument("--seconds-limit", type=float, default=300.0)
    parser.add_argument("--force", action="store_true")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("top")
    p.add_argument("--binding", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path)
    add_limits(p)
    for name in ("normality", "radical"):
        p = sub.add_parser(name)
        p.add_argument("--top", required=True, type=Path)
        p.add_argument("--state", required=True, type=int)
        p.add_argument("--output", required=True, type=Path)
        add_limits(p)
    p = sub.add_parser("transition")
    p.add_argument("--top", required=True, type=Path)
    p.add_argument("--state", required=True, type=int)
    p.add_argument("--class-index", required=True, type=int)
    p.add_argument("--output", required=True, type=Path)
    add_limits(p)
    p = sub.add_parser("assemble-top")
    p.add_argument("--top", required=True, type=Path)
    p.add_argument("--chunks", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path)
    p.add_argument("--force", action="store_true")
    p = sub.add_parser("row")
    p.add_argument("--top", required=True, type=Path)
    p.add_argument("--binding", required=True, type=Path)
    p.add_argument("--module", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path)
    add_limits(p)
    args = parser.parse_args()

    if args.command == "top":
        result = prepare_top(read(args.binding), budget(args))
    elif args.command == "normality":
        result = normality_chunk(read(args.top, TOP_SCHEMA), args.state, budget(args))
    elif args.command == "transition":
        result = transition_chunk(read(args.top, TOP_SCHEMA), args.state,
                                  args.class_index, budget(args))
    elif args.command == "radical":
        result = radical_chunk(read(args.top, TOP_SCHEMA), args.state, budget(args))
    elif args.command == "assemble-top":
        result = assemble_top(read(args.top, TOP_SCHEMA), args.chunks)
    else:
        result = prepare_row(read(args.top, ASSEMBLED_SCHEMA),
                             read(args.binding), read(args.module), budget(args))
    write(args.output, result, args.force)
    operations = getattr(locals().get("args"), "operation_limit", None)
    print(f"{args.output}: {args.command}; {len(json.dumps(result))} characters"
          + (f"; ceiling {operations}" if operations else ""))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, KeyError, TypeError, json.JSONDecodeError,
            base.Refused, ValueError) as error:
        raise SystemExit(f"refused: {error}")
