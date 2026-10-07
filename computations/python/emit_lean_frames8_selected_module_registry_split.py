#!/usr/bin/env python3
"""Split one selected frame-module registry into bounded Lean modules.

The join table and the per-state displacement certificates are independent
finite checks.  Keeping them in separate compilation units prevents the
large invariant-state rows from retaining all native proof terms at once.
"""
from __future__ import annotations

import argparse
import importlib.util
import os
from pathlib import Path
import re
import tempfile


MODULE_RE = re.compile(r"[A-Z][A-Za-z0-9_]*\Z")
OUTPUT_LIMIT = 2 * 1024 * 1024


class Refused(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refused(message)


def load_base():
    path = Path(__file__).with_name("emit_lean_frames8_selected_module_registry.py")
    spec = importlib.util.spec_from_file_location("frames8_registry_base", path)
    require(spec is not None and spec.loader is not None, "cannot load registry emitter")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def write_atomic(path: Path, payload: str, force: bool) -> None:
    raw = payload.encode()
    require(len(raw) <= OUTPUT_LIMIT, f"Lean output ceiling reached: {path.name}")
    require(force or not path.exists(), f"output exists: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("wb", delete=False, dir=path.parent,
                                     prefix=path.name + ".",
                                     suffix=".partial") as stream:
        temporary = Path(stream.name)
        stream.write(raw)
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def local_header(imports: list[str], namespace: str, representation_module: str,
                 top_module: str, description: str) -> str:
    return "\n".join(f"import SymmetricSubgroupAsymptotics.{x}" for x in imports) + f"""

/-! {description} -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.{namespace}

abbrev Source := {representation_module}.Source
local instance sourceGroup : Group Source := {top_module}.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩
abbrev ModelModule := {representation_module}.ModelModule

"""


def dependent_header(imports: list[str], namespace: str, top_module: str,
                     tag: str, description: str) -> str:
    """Header for a chunk importing the central data module.

    `Source` and `ModelModule` are already declared by that module.  Every
    compilation unit still needs active group/inhabited instances, whose
    declaration names must be distinct when the chunks are later imported
    together by the assembly module.
    """
    return "\n".join(f"import SymmetricSubgroupAsymptotics.{x}" for x in imports) + f"""

/-! {description} -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.{namespace}

local instance sourceGroup{tag} : Group Source := {top_module}.group
local instance sourceInhabited{tag} : Inhabited Source := ⟨1⟩

"""


def executable_header(imports: list[str], namespace: str, description: str) -> str:
    """Header for a raw finite-data module used by native decision proofs."""
    return "\n".join(f"import SymmetricSubgroupAsymptotics.{x}" for x in imports) + f"""

/-! {description} -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.{namespace}

"""


def split_source(base, data: dict, full: str, namespace: str, representation_module: str,
                 orbits_module: str, top_module: str,
                 state_count: int, cyclic_count: int, chunk_size: int):
    starts = [full.index(f"namespace D{i}\n") for i in range(state_count)]
    assembly_start = full.index("noncomputable def displacementCharts")
    join_proof_start = full.index("private theorem old_mem_child")
    join_assembly_start = full.index("private theorem bottom_eq")
    joins_module = namespace + "Joins"
    join_data_module = namespace + "JoinData"
    child_table_module = namespace + "ChildTableData"
    chunks = []
    join_chunks = []
    outputs = {}
    child_table_start = full.index("private def childTable")
    old_table_start = full.index("private def childOldTable")

    outputs[child_table_module] = executable_header(
        [representation_module], child_table_module,
        "Executable selected invariant-state child table.") + \
        full[child_table_start:old_table_start] + f"""def child
    (i : Fin {state_count}) (c : Fin {cyclic_count}) : Fin {state_count} :=
  (childTable[i.val]!)[c.val]!

end SymmetricSubgroupAsymptotics.{child_table_module}
"""
    outputs[join_data_module] = local_header(
        [orbits_module, "PrimitiveAffineEightFrameDisplacementImporter",
         "BinaryInvariantCyclicOrbitStabilizerRegistry", child_table_module], namespace,
        representation_module, top_module,
        "Selected invariant-state executable table accessors.") + f"""def child
    (i : Fin {state_count}) (c : Fin {cyclic_count}) : Fin {state_count} :=
  SymmetricSubgroupAsymptotics.{child_table_module}.child i c

end SymmetricSubgroupAsymptotics.{namespace}

end
"""
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
    word_dictionary_expr = "#[" + ",".join(
        base.lean_word(word, orbits_module, data["generator_count"])
        for word in word_dictionary) + "]"
    for start in range(0, state_count, chunk_size):
        stop = min(state_count, start + chunk_size)
        size = stop - start
        module = namespace + f"Join{start}"
        old_module = namespace + f"OldTableData{start}"
        orbit_module = namespace + f"OrbitTableData{start}"
        old_table = "#[" + ",".join(
            "#[" + ",".join(base.lean_nat_array(entry) for entry in row) + "]"
            for row in old_rows[start:stop]) + "]"
        orbit_table = "#[" + ",".join(
            "#[" + ",".join(
                "#[" + ",".join("[" + ",".join(map(str, indices)) + "]"
                                    for indices in entry) + "]"
                for entry in row) + "]"
            for row in word_index_rows[start:stop]) + "]"
        outputs[old_module] = executable_header(
            [representation_module], old_module,
            f"Executable old-coordinate table for states {start}–{stop - 1}.") + f"""private def childOldTable : Array (Array (Array ℕ)) :=
  {old_table}

def childOldMasks (i : Fin {size}) (c : Fin {cyclic_count}) : Array ℕ :=
  (childOldTable[i.val]!)[c.val]!

end SymmetricSubgroupAsymptotics.{old_module}
"""
        outputs[orbit_module] = executable_header(
            [orbits_module], orbit_module,
            f"Executable orbit-word table for states {start}–{stop - 1}.") + f"""abbrev Source := {representation_module}.Source
local instance sourceGroup : Group Source := {top_module}.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩

private def wordDictionary : Array Source :=
  {word_dictionary_expr}

private def childOrbitTable : Array (Array (Array (List ℕ))) :=
  {orbit_table}

def childOrbitRows (i : Fin {size}) (c : Fin {cyclic_count}) : Array (List Source) :=
  ((childOrbitTable[i.val]!)[c.val]!).map
    (fun row ↦ row.map (fun k ↦ wordDictionary[k]!))

end SymmetricSubgroupAsymptotics.{orbit_module}
"""
        join_chunks.append((module, start, stop))
        outputs[module] = dependent_header(
            [join_data_module, old_module, orbit_module], namespace, top_module, f"Join{start}",
            f"Selected invariant-state cyclic joins {start}–{stop - 1}.") + f"""namespace JoinChunk{start}

def embed (i : Fin {size}) : Fin {state_count} :=
  ⟨{start} + i.val, by omega⟩

private def childOldCoordinates (i : Fin {size})
    (c : Fin {cyclic_count})
    (j : Fin ({representation_module}.charts (child (embed i) c)).1) :
    Fin ({representation_module}.charts (embed i)).1 → ZMod 2 :=
  binaryVectorOfMask ({representation_module}.charts (embed i)).1
    ((SymmetricSubgroupAsymptotics.{old_module}.childOldMasks i c)[j.val]!)

private def childOrbitWords (i : Fin {size})
    (c : Fin {cyclic_count})
    (j : Fin ({representation_module}.charts (child (embed i) c)).1) : List Source :=
  (SymmetricSubgroupAsymptotics.{orbit_module}.childOrbitRows i c)[j.val]!

private theorem old_mem_child : ∀ i : Fin {size}, ∀ c j,
    ({representation_module}.charts (embed i)).2.inclusion (Pi.single j 1) ∈
      ({representation_module}.charts (child (embed i) c)).2.space := by
  intro i c
  refine fun j ↦ (({representation_module}.charts
    (child (embed i) c)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i : Fin {size}, ∀ c,
    {orbits_module}.cyclicRepresentative c ∈
      ({representation_module}.charts (child (embed i) c)).2.space := by
  intro i c
  apply (({representation_module}.charts
    (child (embed i) c)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases c <;> native_decide +revert

private theorem child_basis_eq : ∀ i : Fin {size}, ∀ c j,
    ({representation_module}.charts (child (embed i) c)).2.inclusion
        (Pi.single j 1) =
      ({representation_module}.charts (embed i)).2.inclusion
          (childOldCoordinates i c j) +
        ((childOrbitWords i c j).map (fun g ↦
          {representation_module}.representation g
            ({orbits_module}.cyclicRepresentative c))).sum := by
  intro i c
  fin_cases i <;> fin_cases c <;>
    simp only [childOldCoordinates, childOrbitWords] <;>
    native_decide +revert

theorem child_eq (i : Fin {size}) (c : Fin {cyclic_count}) :
    ({representation_module}.states (child (embed i) c)).toSubmodule =
      ({representation_module}.states (embed i)).toSubmodule ⊔
        binaryOrbitSpan {representation_module}.representation
          ({orbits_module}.cyclicRepresentative c) := by
  rw [{representation_module}.states_space,
    {representation_module}.states_space]
  exact binaryCoordinate_orbit_join_eq
    ({representation_module}.charts (embed i)).2
    ({representation_module}.charts (child (embed i) c)).2
    {representation_module}.representation
    ({representation_module}.states (child (embed i) c))
    ({representation_module}.states_space (child (embed i) c))
    ({orbits_module}.cyclicRepresentative c)
    (old_mem_child i c) (cyclic_mem_child i c)
    (childOldCoordinates i c) (childOrbitWords i c)
    (child_basis_eq i c)

end JoinChunk{start}

end SymmetricSubgroupAsymptotics.{namespace}

end
"""
    dispatch_lines = []
    for module, start, stop in join_chunks:
        size = stop - start
        dispatch_lines += [
            f"  by_cases h{start} : i.val < {stop}",
            f"  · let j : Fin {size} := ⟨i.val - {start}, by omega⟩",
            f"    have hj : JoinChunk{start}.embed j = i := by",
            "      apply Fin.ext",
            (f"      simp [JoinChunk{start}.embed, j]"
             if start == 0 else
             f"      simp [JoinChunk{start}.embed, j]\n      omega"),
            "    rw [← hj]",
            f"    exact JoinChunk{start}.child_eq j c"]
    dispatch_lines.append("  omega")
    join_tail = full[join_assembly_start:starts[0]]
    outputs[joins_module] = dependent_header(
        [join_data_module] + [x[0] for x in join_chunks],
        namespace, top_module, "Joins",
        "Assembly of the bounded invariant-state cyclic-join chunks.") + f"""theorem child_eq
    (i : Fin {state_count}) (c : Fin {cyclic_count}) :
    ({representation_module}.states (child i c)).toSubmodule =
      ({representation_module}.states i).toSubmodule ⊔
        binaryOrbitSpan {representation_module}.representation
          ({orbits_module}.cyclicRepresentative c) := by
{chr(10).join(dispatch_lines)}

""" + join_tail + f"""end SymmetricSubgroupAsymptotics.{namespace}

end
"""
    for start in range(0, state_count, chunk_size):
        stop = min(state_count, start + chunk_size)
        module = namespace + f"Displacement{start}"
        chunks.append(module)
        body_start = starts[start]
        body_stop = starts[stop] if stop < state_count else assembly_start
        outputs[module] = dependent_header(
            [join_data_module], namespace, top_module, f"Displacement{start}",
            f"Selected invariant-state displacement certificates {start}–{stop - 1}.") + \
            full[body_start:body_stop] + f"""end SymmetricSubgroupAsymptotics.{namespace}

end
"""
    suffix = full[assembly_start:]
    outputs[namespace] = dependent_header(
        [joins_module] + chunks,
        namespace, top_module, "Assembly",
        "Assembly of the checked cyclic joins and displacement chunks.") + suffix
    return outputs, joins_module, chunks


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--module", required=True)
    parser.add_argument("--representation-module", required=True)
    parser.add_argument("--orbits-module", required=True)
    parser.add_argument("--top-module", required=True)
    parser.add_argument("--chunk-size", type=int, default=16)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    for name in (args.module, args.representation_module,
                 args.orbits_module, args.top_module):
        require(MODULE_RE.fullmatch(name) is not None, "invalid module name")
    require(4 <= args.chunk_size <= 32, "chunk size outside 4..32")
    base = load_base()
    data = base.read_input(args.input)
    full = base.emit(args.module, args.representation_module,
                     args.orbits_module, args.top_module, data,
                     args.input.name)
    outputs, _joins, chunks = split_source(
        base, data, full, args.module, args.representation_module, args.orbits_module,
        args.top_module,
        data["state_count"], data["cyclic_count"], args.chunk_size)
    for module, payload in outputs.items():
        write_atomic(args.output_dir / f"{module}.lean", payload, args.force)
    print(f"{args.module}: {data['state_count']} states in {len(chunks)} chunks; "
          + ", ".join(f"{name}={len(payload.encode())}"
                      for name, payload in outputs.items()))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, KeyError, TypeError, Refused, ValueError) as error:
        raise SystemExit(f"refused: {error}")
