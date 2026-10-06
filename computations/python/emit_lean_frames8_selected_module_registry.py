#!/usr/bin/env python3
"""Render the cyclic-join and displacement registry of one selected row.

The input is one bounded prepared eight-frame certificate.  The generated
Lean source checks every join basis equation and every displacement basis
equation against the literal matrix representation.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import tempfile


SCHEMA = "frames8-selected-top-certificate-v1"
INPUT_LIMIT = 16 * 1024 * 1024
OUTPUT_LIMIT = 4 * 1024 * 1024
MODULE_RE = re.compile(r"[A-Z][A-Za-z0-9_]*\Z")


class Refused(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refused(message)


def lookup(values: list[str], variable: str = "i.val", start: int = 0) -> str:
    require(values, "empty Lean lookup")
    if len(values) == 1:
        return values[0]
    middle = len(values) // 2
    return (f"(if {variable} < {start + middle} then "
            f"{lookup(values[:middle], variable, start)} else "
            f"{lookup(values[middle:], variable, start + middle)})")


def lean_word(word: list[int], orbits_module: str) -> str:
    require(all(type(x) is int and 0 <= x < 3 for x in word),
            "invalid generator word")
    return (f"{orbits_module}.sourceWord [" +
            ",".join(map(str, word)) + "]")


def lean_word_list(words: list[list[int]], orbits_module: str) -> str:
    return "[" + ",".join(lean_word(x, orbits_module) for x in words) + "]"


def lean_nat_array(values: list[int]) -> str:
    return "#[" + ",".join(map(str, values)) + "]"


def read_input(path: Path) -> dict:
    require(path.is_file() and not path.is_symlink(),
            "missing or redirected prepared certificate")
    raw = path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, "prepared certificate ceiling reached")
    value = json.loads(raw)
    require(isinstance(value, dict) and value.get("schema") == SCHEMA,
            "unexpected prepared certificate schema")
    module = value.get("module_certificate")
    require(isinstance(module, dict) and
            module.get("source_row") == value.get("source_row") and
            module.get("top_order") == value.get("top_order"),
            "module/top mismatch")
    modules = module.get("modules")
    cyclic = module.get("cyclic_modules")
    children = module.get("children")
    old = module.get("child_old_coordinates")
    words = module.get("child_orbit_words")
    displacement = module.get("displacement_bases")
    provenance = module.get("displacement_provenance")
    require(isinstance(modules, list) and len(modules) == 5 and
            isinstance(cyclic, list) and len(cyclic) == 5 and
            isinstance(children, list) and len(children) == 5 and
            isinstance(old, list) and len(old) == 5 and
            isinstance(words, list) and len(words) == 5 and
            isinstance(displacement, list) and len(displacement) == 5 and
            isinstance(provenance, list) and len(provenance) == 5,
            "invalid five-state registry")
    dimensions = [len(row) for row in modules]
    require(dimensions == [0, 8, 8, 8, 16],
            "unexpected selected-row dimensions")
    flat_children, flat_old, flat_words = [], [], []
    for i in range(5):
        require(len(children[i]) == len(old[i]) == len(words[i]) == 5,
                "invalid child row")
        for c in range(5):
            child = children[i][c]
            require(type(child) is int and 0 <= child < 5 and
                    len(old[i][c]) == dimensions[child] and
                    len(words[i][c]) == dimensions[child],
                    "invalid child witness width")
            require(all(type(x) is int and 0 <= x < 2 ** dimensions[i]
                        for x in old[i][c]), "invalid old coordinate mask")
            flat_children.append(child)
            flat_old.append(old[i][c])
            flat_words.append(words[i][c])
    require([len(row) for row in displacement] == dimensions,
            "selected row does not have zero module head")
    for i, rows in enumerate(provenance):
        require(len(rows) == dimensions[i], "invalid displacement width")
        for terms in rows:
            require(all(isinstance(pair, list) and len(pair) == 2 and
                        type(pair[0]) is int and 0 <= pair[0] < 3 and
                        type(pair[1]) is int and 0 <= pair[1] < dimensions[i]
                        for pair in terms), "invalid displacement provenance")
    return {
        "source_row": value["source_row"],
        "dimensions": dimensions,
        "children": flat_children,
        "old": flat_old,
        "words": flat_words,
        "provenance": provenance,
    }


def emit(module_name: str, representation_module: str, orbits_module: str,
         top_module: str, data: dict, input_name: str) -> str:
    child_lookup = lookup([str(x) for x in data["children"]],
                          "i.val * 5 + c.val")
    old_lookup = lookup([lean_nat_array(x) for x in data["old"]],
                        "i.val * 5 + c.val")
    word_lookup = lookup(
        ["#[" + ",".join(lean_word_list(ws, orbits_module) for ws in row) + "]"
         for row in data["words"]], "i.val * 5 + c.val")
    text = f"""import SymmetricSubgroupAsymptotics.{orbits_module}
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameDisplacementImporter
import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicOrbitStabilizerRegistry

/-!
# Selected eight-frame row {data['source_row']}: module registry

Generated by `emit_lean_frames8_selected_module_registry.py` from
`{input_name}`.  Lean checks all twenty-five cyclic joins and all literal
generator-displacement decompositions.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.{module_name}

abbrev Source := {representation_module}.Source
local instance sourceGroup : Group Source := {top_module}.group
abbrev ModelModule := {representation_module}.ModelModule

def child (i c : Fin 5) : Fin 5 :=
  {child_lookup}

private def childOldMasks (i c : Fin 5) : Array ℕ :=
  {old_lookup}

private def childOrbitRows (i c : Fin 5) : Array (List Source) :=
  {word_lookup}

private def childOldCoordinates (i c : Fin 5)
    (j : Fin ({representation_module}.charts (child i c)).1) :
    Fin ({representation_module}.charts i).1 → ZMod 2 :=
  binaryVectorOfMask ({representation_module}.charts i).1
    ((childOldMasks i c)[j.val]!)

private def childOrbitWords (i c : Fin 5)
    (j : Fin ({representation_module}.charts (child i c)).1) : List Source :=
  (childOrbitRows i c)[j.val]!

private theorem old_mem_child : ∀ i c j,
    ({representation_module}.charts i).2.inclusion (Pi.single j 1) ∈
      ({representation_module}.charts (child i c)).2.space := by
  intro i c
  refine fun j ↦ (({representation_module}.charts (child i c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i c,
    {orbits_module}.cyclicRepresentative c ∈
      ({representation_module}.charts (child i c)).2.space := by
  intro i c
  apply (({representation_module}.charts (child i c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i c j,
    ({representation_module}.charts (child i c)).2.inclusion
        (Pi.single j 1) =
      ({representation_module}.charts i).2.inclusion
          (childOldCoordinates i c j) +
        ((childOrbitWords i c j).map (fun g ↦
          {representation_module}.representation g
            ({orbits_module}.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;> native_decide +revert

theorem child_eq (i c : Fin 5) :
    ({representation_module}.states (child i c)).toSubmodule =
      ({representation_module}.states i).toSubmodule ⊔
        binaryOrbitSpan {representation_module}.representation
          ({orbits_module}.cyclicRepresentative c) := by
  rw [{representation_module}.states_space,
    {representation_module}.states_space]
  exact binaryCoordinate_orbit_join_eq
    ({representation_module}.charts i).2
    ({representation_module}.charts (child i c)).2
    {representation_module}.representation
    ({representation_module}.states (child i c))
    ({representation_module}.states_space (child i c))
    ({orbits_module}.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates i c) (childOrbitWords i c) (child_basis_eq i c)

private theorem bottom_eq :
    ({representation_module}.states (0 : Fin 5)).toSubmodule = ⊥ := by
  rw [{representation_module}.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact ({representation_module}.charts (0 : Fin 5)).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    {representation_module}.representation {representation_module}.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    {orbits_module}.orbitRepresentative {orbits_module}.orbitCover
    {orbits_module}.cyclicRepresentative {orbits_module}.orbitCyclic
    {orbits_module}.orbit_span_eq (0 : Fin 5) bottom_eq child child_eq

"""
    for i, (d, rows) in enumerate(zip(data["dimensions"], data["provenance"])):
        text += f"namespace D{i}\n\n"
        if d == 0:
            text += f"""noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      {representation_module}.representation {top_module}.ambient
      ({representation_module}.states {i})
      ({representation_module}.charts {i}).2 where
  space_le_state := by
    rw [{representation_module}.states_space]
  termCount := fun j ↦ Fin.elim0 j
  termGenerator := fun j ↦ Fin.elim0 j
  termVector := fun j ↦ Fin.elim0 j
  basis_eq := fun j ↦ Fin.elim0 j

end D{i}

"""
            continue
        count_expr = lookup([str(len(x)) for x in rows], "j.val")
        gen_rows = ["#[" + ",".join(str(pair[0]) for pair in terms) + "]"
                    for terms in rows]
        basis_rows = ["#[" + ",".join(str(pair[1]) for pair in terms) + "]"
                      for terms in rows]
        gen_expr = lookup(gen_rows, "j.val")
        basis_expr = lookup(basis_rows, "j.val")
        text += f"""private def termCount (j : Fin {d}) : ℕ :=
  {count_expr}

private def generatorRows (j : Fin {d}) : Array (Fin 3) :=
  {gen_expr}

private def stateBasisRows (j : Fin {d}) : Array (Fin {d}) :=
  {basis_expr}

private def termGenerator (j : Fin {d}) (t : Fin (termCount j)) : Fin 3 :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin {d}) (t : Fin (termCount j)) : Fin {d} :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin {d}) (t : Fin (termCount j)) :
    ({representation_module}.states {i}).toSubmodule :=
  ⟨({representation_module}.charts {i}).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [{representation_module}.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      {representation_module}.representation {top_module}.ambient
      ({representation_module}.states {i})
      ({representation_module}.charts {i}).2 where
  space_le_state := by
    rw [{representation_module}.states_space]
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D{i}

"""
    text += f"""noncomputable def displacementCertificate (i : Fin 5) :
    BinaryCoordinateDisplacementCertificate
      {representation_module}.representation {top_module}.ambient
      ({representation_module}.states i)
      ({representation_module}.charts i).2 := by
  rcases i with ⟨i, hi⟩
  interval_cases i
  · exact D0.certificate
  · exact D1.certificate
  · exact D2.certificate
  · exact D3.certificate
  · exact D4.certificate

/-- The selected row has zero module head; rank two is retained for the
degree-four consumer's common top/module budget. -/
noncomputable def registry :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry {representation_module}.representation 2 :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry.ofBinaryCoordinateCertificates
        {representation_module}.states axes {top_module}.ambient
        (fun i ↦ ({representation_module}.charts i).1)
        (fun i ↦ ({representation_module}.charts i).2)
        displacementCertificate (by
          intro i
          rw [{representation_module}.states_space,
            ({representation_module}.charts i).2.finrank]
          change ({representation_module}.charts i).1 ≤
            ({representation_module}.charts i).1 + 2
          omega)

end SymmetricSubgroupAsymptotics.{module_name}

end
"""
    return text


def write_atomic(path: Path, payload: bytes, force: bool) -> None:
    require(force or not path.exists(), "output exists; use --force")
    require(len(payload) <= OUTPUT_LIMIT, "Lean output byte ceiling reached")
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


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--module", required=True)
    parser.add_argument("--representation-module", required=True)
    parser.add_argument("--orbits-module", required=True)
    parser.add_argument("--top-module", required=True)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    for name in (args.module, args.representation_module,
                 args.orbits_module, args.top_module):
        require(MODULE_RE.fullmatch(name) is not None, "invalid Lean module")
    data = read_input(args.input)
    payload = emit(args.module, args.representation_module,
                   args.orbits_module, args.top_module, data,
                   args.input.name).encode()
    write_atomic(args.output, payload, args.force)
    print(f"{args.output}: {len(payload)} bytes; five-state registry")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, KeyError, TypeError, json.JSONDecodeError, Refused) as error:
        raise SystemExit(f"refused: {error}")
