#!/usr/bin/env python3
"""Emit one small pair-top Cayley source and all quotient-socle tuples.

The input is one payload written by ``export_lean_pair_top_selected.py``.
This selected-row recovery tool reconstructs the literal group, checks every
stored normal subgroup, computes the relative socle carrier over every
normal state, and finds a shortest tuple whose normal closure reaches that
carrier.  The emitted Lean file rechecks the Cayley table, normal lattice,
and every carrier/generator equality with executable finite proofs.

This tool deliberately has no catalogue or directory mode.  Direct normal
lattice checking is restricted to order at most 1,024; larger rows use the
sparse conjugacy/join-word importer instead.
"""
from __future__ import annotations

import argparse
from collections import deque
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile

sys.dont_write_bytecode = True


INPUT_LIMIT = 8 * 1024 * 1024
OUTPUT_LIMIT = 16 * 1024 * 1024
ORDER_LIMIT = 1_024
MODULE_RE = re.compile(r"[A-Z][A-Za-z0-9_]*\Z")
IDENT_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]*\Z")


class Refused(ValueError):
    """The selected payload or reconstructed certificate failed a pin."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refused(message)


def compose(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    require(len(a) == len(b), "permutation widths differ")
    return tuple(a[b[x]] for x in range(len(a)))


def inverse(a: tuple[int, ...]) -> tuple[int, ...]:
    require(sorted(a) == list(range(len(a))), "invalid permutation")
    result = [0] * len(a)
    for x, y in enumerate(a):
        result[y] = x
    return tuple(result)


def conjugate(g: tuple[int, ...], x: tuple[int, ...]) -> tuple[int, ...]:
    return compose(compose(g, x), inverse(g))


def permutation(value: object, width: int) -> tuple[int, ...]:
    require(isinstance(value, list) and len(value) == width,
            "invalid literal permutation width")
    require(all(type(x) is int for x in value),
            "nonintegral permutation image")
    result = tuple(x - 1 for x in value)
    require(sorted(result) == list(range(width)),
            "invalid literal permutation")
    return result


def packed(row: tuple[int, ...]) -> int:
    width = len(row)
    return sum(x * width ** i for i, x in enumerate(row))


def lookup(values: list[object], var: str = "i.val", start: int = 0) -> str:
    require(values, "empty Lean lookup")
    if len(values) == 1:
        return str(values[0])
    middle = len(values) // 2
    return (f"(if {var} < {start + middle} then "
            f"{lookup(values[:middle], var, start)} else "
            f"{lookup(values[middle:], var, start + middle)})")


def lean_array(values: tuple[int, ...] | list[int]) -> str:
    return "#[" + ",".join(str(x) for x in values) + "]"


def finite_checks(n: int) -> str:
    require(n >= 1, "empty finite check")
    if n <= 16:
        return "(by decide +kernel)"
    left = n // 2
    return (f"(Fin.addCases (m := {left}) (n := {n-left}) "
            f"{finite_checks(left)} {finite_checks(n-left)})")


def fin_cases_chain(values: list[str]) -> str:
    result = "(fun i => Fin.elim0 i)"
    for value in reversed(values):
        result = f"(Fin.cases {value} {result})"
    return result


def read_selected(path: Path) -> tuple[dict, str]:
    require(path.is_file() and not path.is_symlink(),
            "missing or redirected selected payload")
    raw = path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, "selected payload ceiling reached")
    value = json.loads(raw)
    require(isinstance(value, dict) and value.get("schema_version") == 1,
            "unexpected selected payload schema")
    action, group = value.get("action"), value.get("group")
    require(isinstance(action, dict) and isinstance(group, dict),
            "selected payload lacks action/group rows")
    require(action.get("id") == group.get("id"),
            "selected action/group identifiers disagree")
    require(action.get("generators") == group.get("generators"),
            "selected ordered generators disagree")
    return value, hashlib.sha256(raw).hexdigest()


def enumerate_group(generators: list[tuple[int, ...]], width: int) -> dict:
    require(generators, "empty generator list")
    one = tuple(range(width))
    rows = [one]
    position = {one: 0}
    parent = [0]
    letter = [0]
    transitions: list[list[int]] = []
    cursor = 0
    while cursor < len(rows):
        require(len(rows) <= ORDER_LIMIT,
                "selected direct-Cayley order ceiling reached")
        current = rows[cursor]
        edges = []
        for j, generator in enumerate(generators):
            target = compose(current, generator)
            if target not in position:
                position[target] = len(rows)
                rows.append(target)
                parent.append(cursor)
                letter.append(j)
            edges.append(position[target])
        transitions.append(edges)
        cursor += 1
    order = sorted(range(len(rows)), key=lambda i: packed(rows[i]))
    remap = {old: new for new, old in enumerate(order)}
    sorted_rows = [rows[i] for i in order]
    nxt = [[remap[x] for x in transitions[i]] for i in order]
    prev = [[0] * len(generators) for _ in sorted_rows]
    for i, edges in enumerate(nxt):
        for j, target in enumerate(edges):
            prev[target][j] = i
    return {
        "rows": sorted_rows,
        "position": {row: i for i, row in enumerate(sorted_rows)},
        "codes": [packed(row) for row in sorted_rows],
        "rank": [order[i] for i in range(len(order))],
        "parent": [remap[parent[i]] for i in order],
        "letter": [letter[i] for i in order],
        "identity": remap[0],
        "next": nxt,
        "prev": prev,
    }


def generated_set(generators: list[tuple[int, ...]], width: int) -> frozenset[tuple[int, ...]]:
    one = tuple(range(width))
    rows = [one]
    seen = {one}
    cursor = 0
    signed = generators + [inverse(g) for g in generators]
    while cursor < len(rows):
        current = rows[cursor]
        for generator in signed:
            target = compose(current, generator)
            if target not in seen:
                require(len(rows) < ORDER_LIMIT,
                        "selected subgroup order ceiling reached")
                seen.add(target)
                rows.append(target)
        cursor += 1
    return frozenset(rows)


def prepare(value: dict, selected_sha256: str) -> dict:
    action, stored = value["action"], value["group"]
    width = action.get("degree")
    require(type(width) is int and width in (6, 8, 12, 16),
            "unsupported pair-top degree")
    generators = [permutation(row, width) for row in action["generators"]]
    table = enumerate_group(generators, width)
    require(len(table["rows"]) == action.get("order"),
            "selected action order mismatch")
    require(2 <= len(table["rows"]) <= ORDER_LIMIT,
            "selected action is outside direct-Cayley scope")

    raw_normals = stored.get("normals")
    require(isinstance(raw_normals, list) and raw_normals,
            "selected row has no normal states")
    state_generators = []
    state_sets = []
    for normal in raw_normals:
        raw = normal.get("generators")
        require(isinstance(raw, list), "normal generator row is absent")
        actual = [permutation(row, width) for row in raw]
        require(all(row in table["position"] for row in actual),
                "normal generator escaped selected top")
        state = generated_set(actual, width)
        require(len(state) == normal.get("order"),
                "normal order disagrees with literal generators")
        require(all(conjugate(g, x) in state
                    for g in generators for x in state),
                "stored state is not normal under ambient generators")
        state_generators.append(actual)
        state_sets.append(state)
    require(len(set(state_sets)) == len(state_sets),
            "stored normal states are not distinct")
    require(frozenset(table["rows"]) in state_sets and
            frozenset({tuple(range(width))}) in state_sets,
            "normal lattice lacks top or bottom")

    # The relative socle carrier is the join of all minimal normal states
    # strictly above the base.  A transition adds one element's normal
    # closure.  Breadth-first search therefore gives a shortest padded tuple.
    normal_closures = []
    for representative in table["rows"]:
        orbit = sorted({conjugate(g, representative)
                        for g in table["rows"]}, key=packed)
        closure = generated_set(orbit, width)
        require(closure in state_sets,
                "element normal closure is absent from stored lattice")
        normal_closures.append(state_sets.index(closure))

    def join_state(left: int, right: int) -> int:
        joined = generated_set(
            state_generators[left] + state_generators[right], width)
        matches = [i for i, state in enumerate(state_sets) if state == joined]
        require(len(matches) == 1, "normal join escaped stored lattice")
        return matches[0]

    children = [[join_state(i, closure)
                 for closure in normal_closures]
                for i in range(len(state_sets))]
    carriers = []
    paths = []
    cap = action.get("kappa")
    require(type(cap) is int and 0 <= cap <= 8,
            "selected kappa is outside the narrow ceiling")
    for base, base_set in enumerate(state_sets):
        above = [j for j, state in enumerate(state_sets) if base_set < state]
        components = [j for j in above if not any(
            base_set < state_sets[k] < state_sets[j] for k in above)]
        candidates = [j for j, state in enumerate(state_sets)
                      if base_set <= state and all(
                          state_sets[k] <= state for k in components)]
        minimal = [j for j in candidates if not any(
            state_sets[k] < state_sets[j] for k in candidates)]
        require(len(minimal) == 1, "relative socle carrier is not unique")
        carrier = minimal[0]
        queue = deque([base])
        shortest: dict[int, list[int]] = {base: []}
        while queue and carrier not in shortest:
            state = queue.popleft()
            for representative, child in enumerate(children[state]):
                if child not in shortest:
                    shortest[child] = shortest[state] + [representative]
                    queue.append(child)
        require(carrier in shortest, "relative socle carrier is unreachable")
        path = shortest[carrier]
        require(len(path) <= cap,
                "relative socle tuple exceeds stored kappa")
        carriers.append(carrier)
        paths.append(path + [table["identity"]] * (cap - len(path)))

    generator_width = max(1, max(len(row) for row in state_generators))
    padded_state_generators = [
        [table["position"][row] for row in row_generators] +
        [table["identity"]] * (generator_width - len(row_generators))
        for row_generators in state_generators
    ]
    require(all(len(row) == generator_width
                for row in padded_state_generators),
            "normal generator padding failed")
    return {
        "selected_sha256": selected_sha256,
        "action_id": action["id"],
        "family": action.get("family"),
        "branch": action.get("branch"),
        "index": action.get("index"),
        "width": width,
        "order": len(table["rows"]),
        "kappa": cap,
        "generators": generators,
        "table": table,
        "normal_count": len(state_sets),
        "normal_generator_width": generator_width,
        "state_generators": padded_state_generators,
        "carriers": carriers,
        "socle_generators": paths,
    }


def permutation_def(name: str, row: tuple[int, ...], width: int) -> str:
    inv = inverse(row)
    return f"""private def {name} : Equiv.Perm (Fin {width}) where
  toFun x := ({lean_array(row)} : Array (Fin {width}))[x.val]!
  invFun x := ({lean_array(inv)} : Array (Fin {width}))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

"""


def emit_module(module: str, catalogue_module: str, catalogue_namespace: str,
                generators_name: str, top_name: str, interface_name: str,
                prepared: dict, input_name: str) -> str:
    width = prepared["width"]
    order = prepared["order"]
    generators = prepared["generators"]
    generator_count = len(generators)
    table = prepared["table"]
    normal_count = prepared["normal_count"]
    normal_width = prepared["normal_generator_width"]
    kappa = prepared["kappa"]
    next_expr = (f"({lookup([lean_array(row) for row in table['next']])} : "
                 f"Array (Fin {order}))[j.val]!")
    prev_expr = (f"({lookup([lean_array(row) for row in table['prev']])} : "
                 f"Array (Fin {order}))[j.val]!")
    state_names = [f"state{i}Generators" for i in range(normal_count)]
    socle_names = [f"state{i}SocleGenerators" for i in range(normal_count)]

    text = f"""import SymmetricSubgroupAsymptotics.{catalogue_module}
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import SymmetricSubgroupAsymptotics.FiniteNormalRegistryQuotientSocle
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Selected pair-top row {prepared['action_id']}: Cayley and quotient socles

Generated by `emit_lean_pair_top_selected_cayley_socles.py` from the single
bounded payload `{input_name}` (SHA-256 `{prepared['selected_sha256']}`).
Lean rechecks the literal Cayley table, all {normal_count} distinct normal
states, their completeness, and every uniformly padded {kappa}-position
relative-socle generator tuple.  The JSON file is not a proof premise.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace {module}

namespace Catalogue := {catalogue_namespace}

"""
    text += f"""def generators : Fin {generator_count} → Equiv.Perm (Fin {width}) :=
  Catalogue.{generators_name}

private def codes (i : Fin {order}) : Fin ({width}^{width}) :=
  {lookup(table['codes'])}

private def ranks (i : Fin {order}) : ℕ :=
  {lookup(table['rank'])}

private def parents (i : Fin {order}) : Fin {order} :=
  {lookup(table['parent'])}

private def letters (i : Fin {order}) : Fin {generator_count} :=
  {lookup(table['letter'])}

private def nextRow (i : Fin {order}) (j : Fin {generator_count}) : Fin {order} :=
  {next_expr}

private def prevRow (i : Fin {order}) (j : Fin {generator_count}) : Fin {order} :=
  {prev_expr}

private theorem parent_lt_checked : ∀ i : Fin {order},
    i ≠ {table['identity']} → ranks (parents i) < ranks i := {finite_checks(order)}

private theorem parent_next_checked : ∀ i : Fin {order},
    i ≠ {table['identity']} → nextRow (parents i) (letters i) = i := {finite_checks(order)}

def certificate : EncodedCayleyCertificate
    (permutationGeneratorEncoding generators) {order} where
  rows := codes
  identity := {table['identity']}
  identity_eq := by decide +kernel
  next := nextRow
  next_eq := {finite_checks(order)}
  rank := ranks
  parent i _ := parents i
  letter i _ := letters i
  parent_lt := parent_lt_checked
  parent_next := parent_next_checked

private theorem codes_strict : StrictMono codes :=
  Fin.strictMono_iff_lt_succ.mpr {finite_checks(order - 1)}

theorem rows_injective : Function.Injective certificate.rows :=
  codes_strict.injective

private theorem prev_checked : ∀ i j,
    certificate.next (prevRow i j) j = i := {finite_checks(order)}

@[reducible] def group : Group (FiniteGroupRow {order}) :=
  certificate.rowGroup rows_injective prevRow prev_checked

abbrev Source := FiniteGroupRow {order}
local instance sourceGroup : Group Source := group

def originalEquiv : letI := group
    Source ≃* Catalogue.{top_name} :=
  certificate.rowEquiv rows_injective prevRow prev_checked

def ambient (j : Fin {generator_count}) : Source :=
  ⟨certificate.next certificate.identity j⟩

theorem ambient_full : Subgroup.closure (Set.range ambient) = ⊤ :=
  certificate.row_generators_full rows_injective prevRow prev_checked

theorem source_card : Nat.card Source = {order} := by
  rw [Nat.card_eq_fintype_card]
  rfl

"""
    for i, rows in enumerate(prepared["state_generators"]):
        text += f"""private def state{i}Generators (j : Fin {normal_width}) : Source :=
  ⟨{lookup(rows, 'j.val')}⟩

"""
    text += f"""def stateGenerators (i : Fin {normal_count}) : Fin {normal_width} → Source :=
  {fin_cases_chain(state_names)}

private def rowState (i : Fin {normal_count}) : Subgroup Source :=
  Subgroup.closure (Set.range (stateGenerators i))

private theorem rowState_normal : ∀ i : Fin {normal_count},
    (rowState i).Normal := by
  native_decide

private theorem rowState_injective : Function.Injective rowState := by
  native_decide

private theorem rowState_complete :
    ∀ N : {{N : Subgroup Source // N.Normal}},
      ∃ i : Fin {normal_count}, rowState i = N.1 := by
  native_decide

noncomputable def rowRegistry : FiniteNormalStateRegistry Source where
  State := Fin {normal_count}
  state := rowState
  state_normal := rowState_normal
  state_injective := rowState_injective
  complete := by
    intro N hN
    letI : N.Normal := hN
    exact rowState_complete ⟨N, inferInstance⟩

noncomputable def topRegistry :
    FiniteNormalStateRegistry Catalogue.{top_name} :=
  rowRegistry.mapEquiv originalEquiv

private abbrev RR := rowRegistry

private theorem rowRegistry_state (i : Fin {normal_count}) :
    RR.state i = rowState i := rfl

private def RowIsMinimalStateAbove (base j : Fin {normal_count}) : Prop :=
  rowState base < rowState j ∧
    ∀ k : Fin {normal_count}, rowState base < rowState k →
      rowState k ≤ rowState j → rowState k = rowState j

private theorem rowRegistry_minimal_iff (base j : Fin {normal_count}) :
    RR.IsMinimalStateAbove base j ↔ RowIsMinimalStateAbove base j := by
  rfl

private def carrierState (i : Fin {normal_count}) : Fin {normal_count} :=
  {lookup(prepared['carriers'])}

"""
    for i, rows in enumerate(prepared["socle_generators"]):
        if kappa == 0:
            expression = "fun j => Fin.elim0 j"
        else:
            expression = lookup(rows, "j.val")
            expression = f"fun j => (⟨{expression}⟩ : Source)"
        text += f"""private def state{i}SocleGenerators : Fin {kappa} → Source :=
  {expression}

"""
    text += f"""private def rowSocleGenerator (i : Fin {normal_count}) :
    Fin {kappa} → Source :=
  {fin_cases_chain(socle_names)}

private theorem row_carrier_eq_checked : ∀ i : Fin {normal_count},
    rowState (carrierState i) = rowState i ⊔
      ⨆ j : {{j : Fin {normal_count} // RowIsMinimalStateAbove i j}},
        rowState j.1 := by
  native_decide

private theorem row_generated_checked : ∀ i : Fin {normal_count},
    Subgroup.normalClosure (Set.range (rowSocleGenerator i)) ⊔ rowState i =
      rowState (carrierState i) := by
  native_decide

noncomputable def rowStateData (i : Fin {normal_count}) :
    FiniteRelativeSocleGeneratorData Source (RR.state i) {kappa} :=
  RR.relativeSocleGeneratorDataOfStates i (carrierState i) {kappa}
    {{j : Fin {normal_count} // RowIsMinimalStateAbove i j}}
    Subtype.val
    (fun j ↦ (rowRegistry_minimal_iff i j).2 j.property)
    (fun j hj ↦ ⟨⟨j, (rowRegistry_minimal_iff i j).1 hj⟩, rfl⟩)
    (by simpa only [rowRegistry_state] using row_carrier_eq_checked i)
    (rowSocleGenerator i)
    (by simpa only [rowRegistry_state] using row_generated_checked i)

noncomputable def topStateData (i : Fin {normal_count}) :
    FiniteRelativeSocleGeneratorData Catalogue.{top_name}
      (topRegistry.state i) {kappa} :=
  (rowStateData i).mapEquiv originalEquiv

/-- Uniform quotient-socle tuples on the catalogue row's canonical normal
registry, transported from the checked selected Cayley source. -/
noncomputable def family :
    (Catalogue.{interface_name}.normalRegistry).
      QuotientSocleGeneratorFamily {kappa} where
  data := by
    intro i
    let N := Catalogue.{interface_name}.normalRegistry.state i
    letI : N.Normal :=
      Catalogue.{interface_name}.normalRegistry.state_normal i
    obtain ⟨j, hj⟩ := topRegistry.complete N
    exact cast
      (congrArg
        (fun M : Subgroup Catalogue.{top_name} ↦
          FiniteRelativeSocleGeneratorData
            Catalogue.{top_name} M {kappa}) hj)
      (topStateData j)

end {module}
end SymmetricSubgroupAsymptotics

end
"""
    return text


def write_atomic(path: Path, payload: bytes, force: bool) -> None:
    require(force or not path.exists(), "output exists; use --force")
    require(len(payload) <= OUTPUT_LIMIT, "Lean output byte ceiling reached")
    require(path.parent.exists(), "output parent must already exist")
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


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--module", required=True)
    parser.add_argument("--catalogue-module", required=True)
    parser.add_argument("--catalogue-namespace", required=True)
    parser.add_argument("--generators-name", required=True)
    parser.add_argument("--top-name", required=True)
    parser.add_argument("--interface-name", required=True)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    for name in (args.module, args.catalogue_module):
        require(MODULE_RE.fullmatch(name) is not None,
                "invalid Lean module identifier")
    for name in (args.generators_name, args.top_name, args.interface_name):
        require(IDENT_RE.fullmatch(name) is not None,
                "invalid Lean declaration identifier")
    require(all(MODULE_RE.fullmatch(part) is not None
                for part in args.catalogue_namespace.split(".")),
            "invalid catalogue namespace")
    selected, selected_sha256 = read_selected(args.input)
    prepared = prepare(selected, selected_sha256)
    payload = emit_module(
        args.module, args.catalogue_module, args.catalogue_namespace,
        args.generators_name, args.top_name, args.interface_name,
        prepared, args.input.name).encode()
    write_atomic(args.output, payload, args.force)
    print(f"{args.output}: {len(payload)} bytes; {prepared['action_id']}; "
          f"order {prepared['order']}; normals {prepared['normal_count']}; "
          f"socle cap {prepared['kappa']}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, json.JSONDecodeError, Refused) as error:
        raise SystemExit(f"refused: {error}")
