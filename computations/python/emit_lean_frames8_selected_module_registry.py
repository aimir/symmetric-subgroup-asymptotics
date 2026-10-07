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


def lean_word(word: list[int], orbits_module: str,
              generator_count: int) -> str:
    require(all(type(x) is int and 0 <= x < generator_count for x in word),
            "invalid generator word")
    return (f"{orbits_module}.sourceWord [" +
            ",".join(map(str, word)) + "]")


def lean_word_list(words: list[list[int]], orbits_module: str,
                   generator_count: int) -> str:
    return "[" + ",".join(
        lean_word(x, orbits_module, generator_count) for x in words) + "]"


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
    displacement_duals = module.get("displacement_coordinate_masks")
    provenance = module.get("displacement_provenance")
    state_count = len(modules) if isinstance(modules, list) else 0
    cyclic_count = len(cyclic) if isinstance(cyclic, list) else 0
    require(1 <= state_count <= 256 and 1 <= cyclic_count <= 256 and
            isinstance(children, list) and len(children) == state_count and
            isinstance(old, list) and len(old) == state_count and
            isinstance(words, list) and len(words) == state_count and
            isinstance(displacement, list) and len(displacement) == state_count and
            isinstance(displacement_duals, list) and
              len(displacement_duals) == state_count and
            isinstance(provenance, list) and len(provenance) == state_count,
            "invalid selected module registry")
    dimensions = [len(row) for row in modules]
    require(dimensions[0] == 0 and dimensions[-1] == 16,
            "selected module registry lacks bottom or whole state")
    flat_children, flat_old, flat_words = [], [], []
    for i in range(state_count):
        require(len(children[i]) == len(old[i]) == len(words[i]) == cyclic_count,
                "invalid child row")
        for c in range(cyclic_count):
            child = children[i][c]
            require(type(child) is int and 0 <= child < state_count and
                    len(old[i][c]) == dimensions[child] and
                    len(words[i][c]) == dimensions[child],
                    "invalid child witness width")
            require(all(type(x) is int and 0 <= x < 2 ** dimensions[i]
                        for x in old[i][c]), "invalid old coordinate mask")
            flat_children.append(child)
            flat_old.append(old[i][c])
            flat_words.append(words[i][c])
    displacement_dimensions = [len(row) for row in displacement]
    require(all(len(displacement_duals[i]) == displacement_dimensions[i]
                for i in range(state_count)),
            "invalid displacement dual-coordinate width")
    for i, rows in enumerate(provenance):
        require(len(rows) == displacement_dimensions[i],
                "invalid displacement width")
        for terms in rows:
            require(all(isinstance(pair, list) and len(pair) == 2 and
                        type(pair[0]) is int and 0 <= pair[0] and
                        type(pair[1]) is int and 0 <= pair[1] < dimensions[i]
                        for pair in terms), "invalid displacement provenance")
    generators = value.get("generators")
    generator_count = len(generators) if isinstance(generators, list) else 0
    require(1 <= generator_count <= 16 and
            all(pair[0] < generator_count
                for rows in provenance for terms in rows for pair in terms),
            "invalid displacement generator index")
    return {
        "source_row": value["source_row"],
        "state_count": state_count,
        "cyclic_count": cyclic_count,
        "generator_count": generator_count,
        "dimensions": dimensions,
        "displacement": displacement,
        "displacement_duals": displacement_duals,
        "displacement_dimensions": displacement_dimensions,
        "children": flat_children,
        "old": flat_old,
        "words": flat_words,
        "provenance": provenance,
    }


def emit(module_name: str, representation_module: str, orbits_module: str,
         top_module: str, data: dict, input_name: str) -> str:
    state_count = data["state_count"]
    cyclic_count = data["cyclic_count"]
    generator_count = data["generator_count"]
    child_rows = [data["children"][i * cyclic_count:(i + 1) * cyclic_count]
                  for i in range(state_count)]
    old_rows = [data["old"][i * cyclic_count:(i + 1) * cyclic_count]
                for i in range(state_count)]
    word_rows = [data["words"][i * cyclic_count:(i + 1) * cyclic_count]
                 for i in range(state_count)]
    word_dictionary: list[list[int]] = []
    word_index: dict[tuple[int, ...], int] = {}
    word_index_rows = []
    for row in word_rows:
        index_row = []
        for entry in row:
            index_entry = []
            for words in entry:
                indices = []
                for word in words:
                    key = tuple(word)
                    if key not in word_index:
                        word_index[key] = len(word_dictionary)
                        word_dictionary.append(word)
                    indices.append(word_index[key])
                index_entry.append(indices)
            index_row.append(index_entry)
        word_index_rows.append(index_row)
    child_table = "#[" + ",".join(lean_nat_array(row) for row in child_rows) + "]"
    old_table = "#[" + ",".join(
        "#[" + ",".join(lean_nat_array(entry) for entry in row) + "]"
        for row in old_rows) + "]"
    word_table = "#[" + ",".join(
        "#[" + ",".join(
            "#[" + ",".join("[" + ",".join(map(str, indices)) + "]"
                              for indices in entry) + "]"
            for entry in row) + "]"
        for row in word_index_rows) + "]"
    word_dictionary_expr = "#[" + ",".join(
        lean_word(word, orbits_module, generator_count)
        for word in word_dictionary) + "]"
    text = f"""import SymmetricSubgroupAsymptotics.{orbits_module}
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameDisplacementImporter
import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicOrbitStabilizerRegistry

/-!
# Selected eight-frame row {data['source_row']}: module registry

Generated by `emit_lean_frames8_selected_module_registry.py` from
`{input_name}`.  Lean checks every cyclic join and every literal
generator-displacement decomposition.
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
local instance sourceInhabited : Inhabited Source := ⟨1⟩
abbrev ModelModule := {representation_module}.ModelModule

private def childTable : Array (Array (Fin {state_count})) :=
  {child_table}

private def childOldTable : Array (Array (Array ℕ)) :=
  {old_table}

private def wordDictionary : Array Source :=
  {word_dictionary_expr}

private def childOrbitTable : Array (Array (Array (List ℕ))) :=
  {word_table}

def child (i : Fin {state_count}) (c : Fin {cyclic_count}) :
    Fin {state_count} :=
  (childTable[i.val]!)[c.val]!

private def childOldMasks (i : Fin {state_count}) (c : Fin {cyclic_count}) :
    Array ℕ :=
  (childOldTable[i.val]!)[c.val]!

private def childOrbitRows (i : Fin {state_count}) (c : Fin {cyclic_count}) :
    Array (List Source) :=
  ((childOrbitTable[i.val]!)[c.val]!).map
    (fun row ↦ row.map (fun k ↦ wordDictionary[k]!))

def childOldCoordinates (i : Fin {state_count})
    (c : Fin {cyclic_count})
    (j : Fin ({representation_module}.charts (child i c)).1) :
    Fin ({representation_module}.charts i).1 → ZMod 2 :=
  binaryVectorOfMask ({representation_module}.charts i).1
    ((childOldMasks i c)[j.val]!)

def childOrbitWords (i : Fin {state_count})
    (c : Fin {cyclic_count})
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

theorem child_eq (i : Fin {state_count}) (c : Fin {cyclic_count}) :
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
    ({representation_module}.states (0 : Fin {state_count})).toSubmodule = ⊥ := by
  rw [{representation_module}.states_space]
  apply Submodule.finrank_eq_zero.mp
  exact ({representation_module}.charts (0 : Fin {state_count})).2.finrank

/-- Complete invariant-submodule registry for the selected module. -/
noncomputable def axes : BinaryInvariantCyclicOrbitRegistry
    {representation_module}.representation {representation_module}.states :=
  BinaryInvariantCyclicOrbitRegistry.ofMinimalStabilizerCover
    {orbits_module}.orbitRepresentative {orbits_module}.orbitCover
    {orbits_module}.cyclicRepresentative {orbits_module}.orbitCyclic
    {orbits_module}.orbit_span_eq (0 : Fin {state_count}) bottom_eq child child_eq

"""
    displacement_entries = []
    for i, (state_dimension, displacement_dimension, basis, dual, rows) in enumerate(
            zip(data["dimensions"], data["displacement_dimensions"],
                data["displacement"], data["displacement_duals"],
                data["provenance"])):
        basis_expr = lookup([str(x) for x in basis], "j.val") if basis else "0"
        dual_expr = lookup([str(x) for x in dual], "j.val") if dual else "0"
        membership_proof = (
            "  exact Fin.elim0 j"
            if displacement_dimension == 0 else
            "  fin_cases j <;> native_decide")
        text += f"""namespace D{i}

private def displacementBasis (j : Fin {displacement_dimension}) : ℕ :=
  {basis_expr}

private def displacementDual (j : Fin {displacement_dimension}) : ℕ :=
  {dual_expr}

def displacementChart :
    BinaryCoordinateSpace 16 {displacement_dimension} :=
  binaryCoordinateSpaceOfMasks 16 {displacement_dimension}
    displacementBasis displacementDual (by native_decide)

private theorem displacement_le_state :
    displacementChart.space ≤
      ({representation_module}.states {i}).toSubmodule := by
  rw [{representation_module}.states_space]
  apply displacementChart.le_of_basis_mem
  intro j
  apply (({representation_module}.charts {i}).2.mem_iff _).mpr
{membership_proof}

"""
        if displacement_dimension == 0:
            text += f"""noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      {representation_module}.representation {top_module}.ambient
      ({representation_module}.states {i}) displacementChart where
  space_le_state := displacement_le_state
  termCount := fun j ↦ Fin.elim0 j
  termGenerator := fun j ↦ Fin.elim0 j
  termVector := fun j ↦ Fin.elim0 j
  basis_eq := fun j ↦ Fin.elim0 j

end D{i}

"""
        else:
            count_expr = lookup([str(len(x)) for x in rows], "j.val")
            gen_rows = ["#[" + ",".join(str(pair[0]) for pair in terms) + "]"
                        for terms in rows]
            state_rows = ["#[" + ",".join(str(pair[1]) for pair in terms) + "]"
                          for terms in rows]
            gen_expr = lookup(gen_rows, "j.val")
            state_expr = lookup(state_rows, "j.val")
            text += f"""private def termCount (j : Fin {displacement_dimension}) : ℕ :=
  {count_expr}

private def generatorRows (j : Fin {displacement_dimension}) :
    Array (Fin {generator_count}) :=
  {gen_expr}

private def stateBasisRows (j : Fin {displacement_dimension}) :
    Array (Fin {state_dimension}) :=
  {state_expr}

private def termGenerator (j : Fin {displacement_dimension})
    (t : Fin (termCount j)) : Fin {generator_count} :=
  (generatorRows j)[t.val]!

private def termStateBasis (j : Fin {displacement_dimension})
    (t : Fin (termCount j)) : Fin {state_dimension} :=
  (stateBasisRows j)[t.val]!

private def termVector (j : Fin {displacement_dimension})
    (t : Fin (termCount j)) :
    ({representation_module}.states {i}).toSubmodule :=
  ⟨({representation_module}.charts {i}).2.inclusion
      (Pi.single (termStateBasis j t) 1), by
    rw [{representation_module}.states_space]
    exact ⟨Pi.single (termStateBasis j t) 1, rfl⟩⟩

noncomputable def certificate :
    BinaryCoordinateDisplacementCertificate
      {representation_module}.representation {top_module}.ambient
      ({representation_module}.states {i}) displacementChart where
  space_le_state := displacement_le_state
  termCount := termCount
  termGenerator := termGenerator
  termVector := termVector
  basis_eq := by
    intro j
    fin_cases j <;> native_decide

end D{i}

"""
        displacement_entries.append(
            f"⟨{displacement_dimension}, D{i}.displacementChart⟩")
    dispatch = "\n".join(
        f"  · exact D{i}.certificate" for i in range(state_count))
    text += f"""noncomputable def displacementCharts (i : Fin {state_count}) :
    Σ d, BinaryCoordinateSpace 16 d :=
  {lookup(displacement_entries)}

noncomputable def displacementCertificate (i : Fin {state_count}) :
    BinaryCoordinateDisplacementCertificate
      {representation_module}.representation {top_module}.ambient
      ({representation_module}.states i) (displacementCharts i).2 := by
  rcases i with ⟨i, hi⟩
  interval_cases i
{dispatch}

/-- Literal displacement spaces have codimension at most two in every
invariant state, while the cyclic join table is complete. -/
noncomputable def registry :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry {representation_module}.representation 2 :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.FiniteFrameModuleCyclicOrbitDisplacementRegistry.ofBinaryCoordinateCertificates
        {representation_module}.states axes {top_module}.ambient
        (fun i ↦ (displacementCharts i).1)
        (fun i ↦ (displacementCharts i).2)
        displacementCertificate (by
          intro i
          rw [{representation_module}.states_space,
            ({representation_module}.charts i).2.finrank]
          change ({representation_module}.charts i).1 ≤
            (displacementCharts i).1 + 2
          rcases i with ⟨i, hi⟩
          interval_cases i <;>
            simp [{representation_module}.charts, displacementCharts])

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
