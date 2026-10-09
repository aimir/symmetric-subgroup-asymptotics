#!/usr/bin/env python3
"""Emit one checked natural pair-top module registry and generator theorem.

The selected certificate is produced by
``prepare_pair_top_selected_module_generators.py``.  The referenced top
module must expose the standard generated-top API: ``Source``, ``group``,
``generators``, ``originalEquiv``, ``ambient``, ``ambient_full``, and
``source_card``.  This is already the API of the shared degree-eight and
degree-six Cayley certificates, and is the target API for the count-12/16
normal-word importer.

The generated Lean file checks coordinate charts, vector-orbit coverage,
cyclic span rebasing, every child join, and every padded generator path.  It
exports a concrete uniform generator theorem for the natural permutation
module.  This renderer accepts one selected row only.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import tempfile


SCHEMA = "pair-top-selected-module-generators-v1"
INPUT_LIMIT = 16 * 1024 * 1024
OUTPUT_LIMIT = 8 * 1024 * 1024
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


def finite_checks(n: int, leaf: str = "(by native_decide)") -> str:
    require(n >= 1, "empty finite check")
    if n <= 12:
        return leaf
    left = n // 2
    return (f"(Fin.addCases (m := {left}) (n := {n - left}) "
            f"{finite_checks(left, leaf)} {finite_checks(n - left, leaf)})")


def lean_nat_array(values: list[int]) -> str:
    return "#[" + ",".join(map(str, values)) + "]"


def lean_word(word: list[int], generator_count: int) -> str:
    require(all(type(x) is int and 0 <= x < generator_count for x in word),
            "invalid generator word")
    return "topWord [" + ",".join(map(str, word)) + "]"


def lean_word_list(words: list[list[int]], generator_count: int) -> str:
    return "[" + ",".join(lean_word(word, generator_count) for word in words) + "]"


def read_input(path: Path) -> dict:
    require(path.is_file() and not path.is_symlink(),
            "missing or redirected prepared certificate")
    raw = path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, "prepared certificate ceiling reached")
    value = json.loads(raw)
    require(isinstance(value, dict) and value.get("schema") == SCHEMA,
            "unexpected prepared certificate schema")
    n = value.get("degree")
    states = value.get("states")
    duals = value.get("state_coordinate_masks")
    reps = value.get("orbit_representatives")
    stabilizers = value.get("orbit_stabilizer_orders")
    orbit_cyclic = value.get("orbit_cyclic_index")
    orbit_words = value.get("orbit_cyclic_basis_words")
    cyclic_reps = value.get("cyclic_representatives")
    cyclic_first = value.get("cyclic_first_orbit")
    cyclic_state = value.get("cyclic_state_index")
    children = value.get("children")
    old = value.get("child_old_coordinates")
    words = value.get("child_orbit_words")
    paths = value.get("generator_paths")
    state_count = value.get("state_count")
    cyclic_count = value.get("cyclic_count")
    orbit_count = value.get("orbit_count")
    cap = value.get("section_cap")
    generator_count = value.get("generator_count")
    require(type(n) is int and n in (6, 8, 12, 16) and
            type(state_count) is int and 1 <= state_count <= 256 and
            type(cyclic_count) is int and 1 <= cyclic_count <= 256 and
            type(orbit_count) is int and 1 <= orbit_count <= 65536 and
            type(cap) is int and 1 <= cap <= 4 and
            type(generator_count) is int and 1 <= generator_count <= 16,
            "invalid selected module dimensions")
    require(isinstance(states, list) and len(states) == state_count and
            isinstance(duals, list) and len(duals) == state_count and
            isinstance(reps, list) and len(reps) == orbit_count and
            isinstance(stabilizers, list) and len(stabilizers) == orbit_count and
            isinstance(orbit_cyclic, list) and len(orbit_cyclic) == orbit_count and
            isinstance(orbit_words, list) and len(orbit_words) == orbit_count and
            isinstance(cyclic_reps, list) and len(cyclic_reps) == cyclic_count and
            isinstance(cyclic_first, list) and len(cyclic_first) == cyclic_count and
            isinstance(cyclic_state, list) and len(cyclic_state) == cyclic_count and
            isinstance(children, list) and len(children) == state_count and
            isinstance(old, list) and len(old) == state_count and
            isinstance(words, list) and len(words) == state_count and
            isinstance(paths, list) and len(paths) == state_count,
            "invalid selected module table shapes")
    dimensions = [len(row) for row in states]
    require(dimensions[0] == 0 and dimensions[-1] == n and
            all(len(duals[i]) == dimensions[i] for i in range(state_count)),
            "invalid coordinate charts")
    require(all(len(children[i]) == len(old[i]) == len(words[i]) == cyclic_count
                for i in range(state_count)) and
            all(len(paths[i]) == cap for i in range(state_count)),
            "invalid child/generator table shapes")
    relations = []
    for orbit in range(orbit_count):
        cyclic = orbit_cyclic[orbit]
        state = cyclic_state[cyclic]
        target = cyclic_reps[cyclic]
        coordinates = [((target & mask).bit_count() & 1)
                       for mask in duals[state]]
        require(len(coordinates) == len(orbit_words[orbit]),
                "orbit cyclic basis width mismatch")
        relation = []
        for bit, basis_words in zip(coordinates, orbit_words[orbit]):
            if bit:
                relation.extend(basis_words)
        relations.append(relation)
    canonical_words = [orbit_words[first] for first in cyclic_first]
    require(all(reps[first] == cyclic_reps[index]
                for index, first in enumerate(cyclic_first)),
            "canonical orbit representative mismatch")
    return {**value, "dimensions": dimensions,
            "canonical_words": canonical_words, "relations": relations}


def emit(module_name: str, top_module: str, data: dict, input_name: str) -> str:
    n = data["degree"]
    s = data["state_count"]
    c = data["cyclic_count"]
    o = data["orbit_count"]
    h = data["section_cap"]
    g = data["generator_count"]
    top = top_module
    text = f"""import SymmetricSubgroupAsymptotics.{top_module}
import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicGeneratorBound
import SymmetricSubgroupAsymptotics.BinaryCoordinateOrbitSpanCertificate
import SymmetricSubgroupAsymptotics.BinaryOrbitSpanRebase
import SymmetricSubgroupAsymptotics.FiniteLinearOrbitMinimalStabilizerCover
import SymmetricSubgroupAsymptotics.PermutationFunctionSelfDual

/-!
# Natural pair-top module certificate for {data['source_id']}

Generated by `emit_lean_pair_top_selected_module_generators.py` from
`{input_name}`.  Lean checks the literal natural permutation module, all
{s} invariant states, {o} vector orbits, {c} cyclic spans, and the padded
{h}-generator paths.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.{module_name}

abbrev Source := {top}.Source
local instance sourceGroup : Group Source := {top}.group
local instance sourceInhabited : Inhabited Source := ⟨1⟩
abbrev Top : Subgroup (Equiv.Perm (Fin {n})) :=
  Subgroup.closure (Set.range {top}.generators)
abbrev ModelModule := Fin {n} → ZMod 2

def actionEquiv : Source ≃* Top := {top}.originalEquiv

def topAmbient (i : Fin {g}) : Top := actionEquiv ({top}.ambient i)

private theorem topAmbient_full :
    Subgroup.closure (Set.range topAmbient) = ⊤ := by
  apply top_unique
  intro y _hy
  obtain ⟨x, rfl⟩ := actionEquiv.surjective y
  have hx : x ∈ Subgroup.closure (Set.range {top}.ambient) := by
    rw [{top}.ambient_full]
    exact Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Subgroup.subset_closure ⟨i, rfl⟩
  | one => exact Subgroup.one_mem _
  | mul x y _ _ hx hy => exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => exact Subgroup.inv_mem _ hx

def representation : Representation (ZMod 2) Top ModelModule :=
  permutationFunctionRepresentation (ZMod 2) Top (Fin {n})

def sourceRepresentation : Representation (ZMod 2) Source ModelModule :=
  representation.comp actionEquiv.toMonoidHom

def sourceWord (word : List (Fin {g})) : Source :=
  (word.reverse.map {top}.ambient).prod

def topWord (word : List (Fin {g})) : Top := actionEquiv (sourceWord word)

"""
    state_names, chart_names = [], []
    for index, (basis, dual) in enumerate(zip(
            data["states"], data["state_coordinate_masks"])):
        d = len(basis)
        basis_expr = lookup([str(x) for x in basis], "j.val") if basis else "0"
        dual_expr = lookup([str(x) for x in dual], "j.val") if dual else "0"
        text += f"""private def basis{index} (j : Fin {d}) : ℕ := {basis_expr}

private def dual{index} (j : Fin {d}) : ℕ := {dual_expr}

def chart{index} : BinaryCoordinateSpace {n} {d} :=
  binaryCoordinateSpaceOfMasks {n} {d} basis{index} dual{index}
    (by native_decide)

private theorem positive{index} : ∀ q j,
    representation (topAmbient q)
      (chart{index}.inclusion (Pi.single j 1)) ∈ chart{index}.space := by
  native_decide

private theorem negative{index} : ∀ q j,
    representation (topAmbient q)⁻¹
      (chart{index}.inclusion (Pi.single j 1)) ∈ chart{index}.space := by
  native_decide

def state{index} : Subrepresentation representation :=
  chart{index}.subrepresentationOfGenerators representation
    topAmbient topAmbient_full positive{index} negative{index}

"""
        state_names.append(f"state{index}")
        chart_names.append(f"⟨{d}, chart{index}⟩")
    text += f"""def states (i : Fin {s}) : Subrepresentation representation :=
  {lookup(state_names)}

def charts (i : Fin {s}) : Σ d, BinaryCoordinateSpace {n} d :=
  {lookup(chart_names)}

theorem states_space (i : Fin {s}) :
    (states i).toSubmodule = (charts i).2.space := by
  fin_cases i <;> rfl

def orbitRepresentative (i : Fin {o}) : ModelModule :=
  binaryVectorOfMask {n} ({lookup([str(x) for x in data['orbit_representatives']])})

def stabilizerCard (i : Fin {o}) : ℕ :=
  {lookup([str(x) for x in data['orbit_stabilizer_orders']])}

private theorem representativeCode_injective :
    Function.Injective
      (fun i ↦ binaryVectorMask (orbitRepresentative i)) := by native_decide

private theorem representative_minimal : ∀ i q,
    binaryVectorMask (orbitRepresentative i) ≤
      binaryVectorMask
        (sourceRepresentation q (orbitRepresentative i)) :=
  {finite_checks(o)}

private theorem stabilizer_card : ∀ i,
    Nat.card (representationVectorStabilizer sourceRepresentation
      (orbitRepresentative i)) = stabilizerCard i := by
  intro i
  letI : DecidablePred (fun q : Source ↦
      q ∈ representationVectorStabilizer sourceRepresentation
        (orbitRepresentative i)) :=
    fun q ↦ decidable_of_iff
      (sourceRepresentation q (orbitRepresentative i) = orbitRepresentative i)
      Iff.rfl
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  fin_cases i <;> native_decide

private theorem orbit_card_sum :
    (∑ i : Fin {o}, Nat.card Source / stabilizerCard i) =
      Nat.card ModelModule := by
  rw [{top}.source_card, Nat.card_eq_fintype_card]
  native_decide

noncomputable def sourceOrbitCover :
    FiniteLinearOrbitMinimalStabilizerCover sourceRepresentation
      orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := orbit_card_sum

private theorem orbitRepresentative_complete (v : ModelModule) :
    ∃ i q, representation q (orbitRepresentative i) = v := by
  obtain ⟨i, q, hq⟩ := sourceOrbitCover.covers v
  exact ⟨i, actionEquiv q, hq⟩

def orbitCyclic (i : Fin {o}) : Fin {c} :=
  {lookup([str(x) for x in data['orbit_cyclic_index']])}

def cyclicRepresentative (i : Fin {c}) : ModelModule :=
  binaryVectorOfMask {n}
    ({lookup([str(x) for x in data['cyclic_representatives']])})

def cyclicState (i : Fin {c}) : Fin {s} :=
  {lookup([str(x) for x in data['cyclic_state_index']])}

"""
    canonical_names = []
    for index, (state, basis_words) in enumerate(zip(
            data["cyclic_state_index"], data["canonical_words"])):
        d = data["dimensions"][state]
        require(len(basis_words) == d, "canonical basis-word width mismatch")
        words_expr = (lookup([lean_word_list(row, g) for row in basis_words],
                             "j.val") if basis_words else "[]")
        canonical_names.append(f"C{index}.span_eq")
        text += f"""namespace C{index}

private def words (j : Fin {d}) : List Top := {words_expr}

private theorem representative_mem :
    cyclicRepresentative {index} ∈ (charts {state}).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (charts {state}).2.inclusion (Pi.single j 1) =
      ((words j).map (fun q ↦
        representation q (cyclicRepresentative {index}))).sum := by
  native_decide

theorem span_eq :
    (states {state}).toSubmodule =
      binaryOrbitSpan representation (cyclicRepresentative {index}) := by
  rw [states_space]
  exact binaryCoordinate_eq_orbitSpan (charts {state}).2
    representation (states {state}) (states_space {state})
    (cyclicRepresentative {index}) representative_mem words basis_eq

end C{index}

"""
    canonical_cases = "\n".join(
        f"  · exact C{index}.span_eq" for index in range(c))
    relation_lookup = lookup([
        lean_word_list(row, g) for row in data["relations"]])
    text += f"""private theorem canonical_span (i : Fin {c}) :
    (states (cyclicState i)).toSubmodule =
      binaryOrbitSpan representation (cyclicRepresentative i) := by
  fin_cases i
{canonical_cases}

private def relationWords (i : Fin {o}) : List Top :=
  {relation_lookup}

private theorem orbit_mem_chart : ∀ i,
    (charts (cyclicState (orbitCyclic i))).2.inclusion
        ((charts (cyclicState (orbitCyclic i))).2.coordinates
          (orbitRepresentative i)) = orbitRepresentative i :=
  {finite_checks(o)}

private theorem orbit_mem_state (i : Fin {o}) :
    orbitRepresentative i ∈
      (states (cyclicState (orbitCyclic i))).toSubmodule := by
  rw [states_space]
  exact ((charts (cyclicState (orbitCyclic i))).2.mem_iff
    (orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem relation_eq : ∀ i,
    cyclicRepresentative (orbitCyclic i) =
      ((relationWords i).map
        (fun q ↦ representation q (orbitRepresentative i))).sum :=
  {finite_checks(o)}

private theorem canonical_mem_orbit_span (i : Fin {o}) :
    cyclicRepresentative (orbitCyclic i) ∈
      binaryOrbitSpan representation (orbitRepresentative i) := by
  rw [relation_eq i]
  apply (binaryOrbitSpan representation (orbitRepresentative i)).list_sum_mem
  intro x hx
  obtain ⟨q, _hq, rfl⟩ := List.mem_map.mp hx
  exact Submodule.subset_span ⟨q, rfl⟩

theorem orbit_span_eq (i : Fin {o}) :
    binaryOrbitSpan representation (orbitRepresentative i) =
      binaryOrbitSpan representation
        (cyclicRepresentative (orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical representation
    (states (cyclicState (orbitCyclic i)))
    (canonical_span (orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

"""
    word_dictionary: list[list[int]] = []
    word_index: dict[tuple[int, ...], int] = {}
    word_index_rows = []
    for state_row in data["child_orbit_words"]:
        cyclic_rows = []
        for child_entry in state_row:
            basis_rows = []
            for word_list in child_entry:
                indices = []
                for word in word_list:
                    key = tuple(word)
                    if key not in word_index:
                        word_index[key] = len(word_dictionary)
                        word_dictionary.append(word)
                    indices.append(word_index[key])
                basis_rows.append(indices)
            cyclic_rows.append(basis_rows)
        word_index_rows.append(cyclic_rows)
    child_table = "#[" + ",".join(
        lean_nat_array(row) for row in data["children"]) + "]"
    old_table = "#[" + ",".join(
        "#[" + ",".join(lean_nat_array(entry) for entry in row) + "]"
        for row in data["child_old_coordinates"]) + "]"
    word_table = "#[" + ",".join(
        "#[" + ",".join(
            "#[" + ",".join(
                "[" + ",".join(map(str, indices)) + "]" for indices in entry
            ) + "]" for entry in row
        ) + "]" for row in word_index_rows
    ) + "]"
    dictionary = "#[" + ",".join(
        lean_word(word, g) for word in word_dictionary) + "]"
    path_table = "#[" + ",".join(
        lean_nat_array(row) for row in data["generator_paths"]) + "]"
    text += f"""private def childTable : Array (Array (Fin {s})) :=
  {child_table}

private def childOldTable : Array (Array (Array ℕ)) :=
  {old_table}

private def wordDictionary : Array Top := {dictionary}

private def childOrbitTable : Array (Array (Array (List ℕ))) :=
  {word_table}

def child (i : Fin {s}) (q : Fin {c}) : Fin {s} :=
  (childTable[i.val]!)[q.val]!

private def childOldMasks (i : Fin {s}) (q : Fin {c}) : Array ℕ :=
  (childOldTable[i.val]!)[q.val]!

private def childOrbitRows (i : Fin {s}) (q : Fin {c}) :
    Array (List Top) :=
  ((childOrbitTable[i.val]!)[q.val]!).map
    (fun row ↦ row.map (fun index ↦ wordDictionary[index]!))

def childOldCoordinates (i : Fin {s}) (q : Fin {c})
    (j : Fin (charts (child i q)).1) : Fin (charts i).1 → ZMod 2 :=
  binaryVectorOfMask (charts i).1 ((childOldMasks i q)[j.val]!)

def childOrbitWords (i : Fin {s}) (q : Fin {c})
    (j : Fin (charts (child i q)).1) : List Top :=
  (childOrbitRows i q)[j.val]!

private theorem old_mem_child : ∀ i q j,
    (charts i).2.inclusion (Pi.single j 1) ∈
      (charts (child i q)).2.space := by
  intro i q
  refine fun j ↦ ((charts (child i q)).2.mem_iff _).mpr ?_
  fin_cases i <;> fin_cases q <;> native_decide +revert

private theorem cyclic_mem_child : ∀ i q,
    cyclicRepresentative q ∈ (charts (child i q)).2.space := by
  intro i q
  apply ((charts (child i q)).2.mem_iff _).mpr
  fin_cases i <;> fin_cases q <;> native_decide +revert

private theorem child_basis_eq : ∀ i q j,
    (charts (child i q)).2.inclusion (Pi.single j 1) =
      (charts i).2.inclusion (childOldCoordinates i q j) +
        ((childOrbitWords i q j).map (fun x ↦
          representation x (cyclicRepresentative q))).sum := by
  intro i q
  fin_cases i <;> fin_cases q <;> native_decide +revert

theorem child_eq (i : Fin {s}) (q : Fin {c}) :
    (states (child i q)).toSubmodule =
      (states i).toSubmodule ⊔
        binaryOrbitSpan representation (cyclicRepresentative q) := by
  rw [states_space, states_space]
  exact binaryCoordinate_orbit_join_eq
    (charts i).2 (charts (child i q)).2 representation
    (states (child i q)) (states_space (child i q))
    (cyclicRepresentative q) (old_mem_child i q) (cyclic_mem_child i q)
    (childOldCoordinates i q) (childOrbitWords i q) (child_basis_eq i q)

private theorem bottom_eq : (states (0 : Fin {s})).toSubmodule = ⊥ := by
  rw [states_space]
  apply Submodule.finrank_eq_zero.mp
  exact (charts (0 : Fin {s})).2.finrank

/-- Complete checked invariant-state registry for the literal natural module. -/
noncomputable def registry :
    BinaryInvariantCyclicOrbitRegistry representation states where
  Orbit := Fin {o}
  orbitRepresentative := orbitRepresentative
  orbitRepresentative_complete := orbitRepresentative_complete
  Cyclic := Fin {c}
  cyclicRepresentative := cyclicRepresentative
  orbitCyclic := orbitCyclic
  orbit_span_eq := orbit_span_eq
  bottom := 0
  bottom_eq := bottom_eq
  child := child
  child_eq := child_eq

private def generatorPathTable : Array (Array (Fin {c})) := {path_table}

def generator (i : Fin {s}) (j : Fin {h}) : Fin {c} :=
  (generatorPathTable[i.val]!)[j.val]!

private theorem generatedState_final : ∀ i,
    registry.generatedState (generator i) = i := by
  native_decide

/-- Every invariant subrepresentation of the natural module is generated by
the stored row capacity. -/
noncomputable def generatorBound :
    BinaryInvariantCyclicGeneratorBound registry {h} :=
  registry.generatorBoundOfGeneratedState {h} generator generatedState_final

theorem uniform :
    UniformSubrepresentationGeneratorBound representation {h} :=
  generatorBound.uniform

theorem dualUniform :
    UniformSubrepresentationGeneratorBound representation.dual {h} :=
  permutationFunctionRepresentation_dual_uniform uniform

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
    parser.add_argument("--top-module", required=True)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    for name in (args.module, args.top_module):
        require(MODULE_RE.fullmatch(name) is not None, "invalid Lean module")
    data = read_input(args.input)
    payload = emit(args.module, args.top_module, data, args.input.name).encode()
    write_atomic(args.output, payload, args.force)
    print(args.output, len(payload), "bytes", data["source_id"])
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, KeyError, TypeError, json.JSONDecodeError, Refused) as error:
        raise SystemExit(f"refused: {error}")
