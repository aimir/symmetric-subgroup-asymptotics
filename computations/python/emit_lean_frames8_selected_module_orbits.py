#!/usr/bin/env python3
"""Render the vector-orbit and cyclic-span certificate of one frame row.

Only one prepared selected row is accepted.  The renderer compresses each
noncanonical cyclic-span witness to a single relation expressing the chosen
canonical generator as an orbit sum.  Lean combines that relation with the
stable coordinate chart; the much larger basis-by-basis witness is therefore
not copied into the publication source.
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


def finite_checks(n: int, leaf: str = "(by native_decide)") -> str:
    require(n >= 1, "empty finite check")
    if n <= 12:
        return leaf
    left = n // 2
    return (f"(Fin.addCases (m := {left}) (n := {n-left}) "
            f"{finite_checks(left, leaf)} {finite_checks(n-left, leaf)})")


def lean_word(word: list[int]) -> str:
    require(all(type(x) is int and 0 <= x < 3 for x in word),
            "invalid generator word")
    return "sourceWord [" + ",".join(map(str, word)) + "]"


def lean_word_list(words: list[list[int]]) -> str:
    return "[" + ",".join(lean_word(word) for word in words) + "]"


def read_input(path: Path) -> dict:
    require(path.is_file() and not path.is_symlink(),
            "missing or redirected prepared certificate")
    raw = path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, "prepared certificate ceiling reached")
    value = json.loads(raw)
    require(isinstance(value, dict) and value.get("schema") == SCHEMA,
            "unexpected prepared certificate schema")
    data = value.get("module_certificate")
    require(isinstance(data, dict) and
            data.get("source_row") == value.get("source_row"),
            "module/top mismatch")
    reps = data.get("orbit_representatives")
    stabilizers = data.get("orbit_stabilizer_orders")
    orbit_cyclic = data.get("orbit_cyclic_index")
    basis_words = data.get("orbit_cyclic_basis_words")
    cyclic_reps = data.get("cyclic_representatives")
    cyclic_first = data.get("cyclic_first_orbit")
    cyclic_state = data.get("cyclic_state_index")
    modules = data.get("modules")
    duals = data.get("module_coordinate_masks")
    c = len(reps)
    d = len(cyclic_reps)
    require(1 <= c <= 1024 and d == 5 and
            len(stabilizers) == len(orbit_cyclic) == len(basis_words) == c and
            len(cyclic_first) == len(cyclic_state) == d,
            "invalid orbit/cyclic rows")
    require(all(type(x) is int and 0 <= x < 2**16 for x in reps + cyclic_reps),
            "invalid binary orbit representative")
    require(all(type(x) is int and x > 0 for x in stabilizers) and
            all(type(x) is int and 0 <= x < d for x in orbit_cyclic) and
            all(type(x) is int and 0 <= x < c for x in cyclic_first) and
            all(type(x) is int and 0 <= x < len(modules) for x in cyclic_state),
            "invalid orbit metadata")
    relations = []
    for o in range(c):
        cyclic = orbit_cyclic[o]
        state = cyclic_state[cyclic]
        target = cyclic_reps[cyclic]
        coordinates = [((target & mask).bit_count() & 1) for mask in duals[state]]
        require(len(coordinates) == len(basis_words[o]),
                "orbit basis width mismatch")
        terms = []
        for bit, words in zip(coordinates, basis_words[o]):
            require(isinstance(words, list), "invalid orbit basis word list")
            if bit:
                terms.extend(words)
        relations.append(terms)
    canonical_words = [basis_words[first] for first in cyclic_first]
    require(all(reps[first] == cyclic_reps[i]
                for i, first in enumerate(cyclic_first)),
            "canonical cyclic representative mismatch")
    require(sum(168 // x for x in stabilizers) == 2**16,
            "orbit-stabilizer arithmetic mismatch")
    return {
        "source_row": value["source_row"],
        "orbit_count": c,
        "cyclic_count": d,
        "reps": reps,
        "stabilizers": stabilizers,
        "orbit_cyclic": orbit_cyclic,
        "cyclic_reps": cyclic_reps,
        "cyclic_state": cyclic_state,
        "canonical_words": canonical_words,
        "relations": relations,
        "dimensions": [len(modules[x]) for x in cyclic_state],
    }


def emit(module_name: str, representation_module: str, top_module: str,
         data: dict, input_name: str) -> str:
    c, d = data["orbit_count"], data["cyclic_count"]
    rep_lookup = lookup([str(x) for x in data["reps"]])
    stab_lookup = lookup([str(x) for x in data["stabilizers"]])
    cyclic_lookup = lookup([str(x) for x in data["orbit_cyclic"]])
    cyclic_rep_lookup = lookup([str(x) for x in data["cyclic_reps"]])
    relation_lookup = lookup([lean_word_list(x) for x in data["relations"]])
    text = f"""import SymmetricSubgroupAsymptotics.{representation_module}
import SymmetricSubgroupAsymptotics.BinaryCoordinateOrbitSpanCertificate
import SymmetricSubgroupAsymptotics.BinaryOrbitSpanRebase
import SymmetricSubgroupAsymptotics.FiniteLinearOrbitMinimalStabilizerCover

/-!
# Selected eight-frame row {data['source_row']}: vector and cyclic-module orbits

Generated by `emit_lean_frames8_selected_module_orbits.py` from `{input_name}`.
Lean checks canonical orbit minima, literal stabilizer cardinalities, orbit
exhaustion, five canonical cyclic spans, and one rebase relation per vector
orbit.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.{module_name}

namespace Rep := {representation_module}
abbrev Source := Rep.Source
local instance sourceGroup : Group Source := {top_module}.group
abbrev ModelModule := Rep.ModelModule

def sourceWord (word : List (Fin 3)) : Source :=
  (word.reverse.map {top_module}.ambient).prod

def orbitRepresentative (i : Fin {c}) : ModelModule :=
  binaryVectorOfMask 16 ({rep_lookup})

def stabilizerCard (i : Fin {c}) : ℕ := {stab_lookup}

def orbitCyclic (i : Fin {c}) : Fin {d} := {cyclic_lookup}

def cyclicRepresentative (i : Fin {d}) : ModelModule :=
  binaryVectorOfMask 16 ({cyclic_rep_lookup})

private theorem representativeCode_injective :
    Function.Injective
      (fun i ↦ binaryVectorMask (orbitRepresentative i)) := by native_decide

private theorem representative_minimal : ∀ i g,
    binaryVectorMask (orbitRepresentative i) ≤
      binaryVectorMask (Rep.representation g (orbitRepresentative i)) :=
  {finite_checks(c)}

private theorem stabilizer_card : ∀ i,
    Nat.card (representationVectorStabilizer Rep.representation
      (orbitRepresentative i)) = stabilizerCard i := by
  intro i
  letI : DecidablePred (fun g : Source ↦
      g ∈ representationVectorStabilizer Rep.representation
        (orbitRepresentative i)) :=
    fun g ↦ decidable_of_iff
      (Rep.representation g (orbitRepresentative i) = orbitRepresentative i)
      Iff.rfl
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  fin_cases i <;> native_decide

private theorem orbit_card_sum :
    (∑ i : Fin {c}, Nat.card Source / stabilizerCard i) =
      Nat.card ModelModule := by
  rw [{top_module}.source_card, Nat.card_eq_fintype_card]
  native_decide

/-- Complete literal vector-orbit cover of the sixteen-dimensional module. -/
noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover Rep.representation
      orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := orbit_card_sum

"""
    canonical_names = []
    for i, (dim, state, rows) in enumerate(zip(
            data["dimensions"], data["cyclic_state"], data["canonical_words"])):
        require(len(rows) == dim, "canonical basis-word width mismatch")
        words_expr = lookup([lean_word_list(x) for x in rows], "j.val") if rows else "[]"
        canonical_names.append(f"C{i}.span_eq")
        text += f"""namespace C{i}

private def words (j : Fin {dim}) : List Source := {words_expr}

private theorem representative_mem :
    cyclicRepresentative {i} ∈ (Rep.charts {state}).2.space := by native_decide

private theorem basis_eq : ∀ j,
    (Rep.charts {state}).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦
        Rep.representation g (cyclicRepresentative {i}))).sum := by
  native_decide

theorem span_eq :
    (Rep.states {state}).toSubmodule =
      binaryOrbitSpan Rep.representation (cyclicRepresentative {i}) := by
  rw [Rep.states_space]
  exact binaryCoordinate_eq_orbitSpan (Rep.charts {state}).2
    Rep.representation (Rep.states {state}) (Rep.states_space {state})
    (cyclicRepresentative {i}) representative_mem words basis_eq

end C{i}

"""
    text += f"""private theorem canonical_span (i : Fin {d}) :
    (Rep.states i).toSubmodule =
      binaryOrbitSpan Rep.representation (cyclicRepresentative i) := by
  fin_cases i
  · exact C0.span_eq
  · exact C1.span_eq
  · exact C2.span_eq
  · exact C3.span_eq
  · exact C4.span_eq

private def relationWords (i : Fin {c}) : List Source :=
  {relation_lookup}

private theorem orbit_mem_chart : ∀ i,
    (Rep.charts (orbitCyclic i)).2.inclusion
        ((Rep.charts (orbitCyclic i)).2.coordinates (orbitRepresentative i)) =
      orbitRepresentative i :=
  {finite_checks(c)}

private theorem orbit_mem_state (i : Fin {c}) :
    orbitRepresentative i ∈ (Rep.states (orbitCyclic i)).toSubmodule := by
  rw [Rep.states_space]
  exact ((Rep.charts (orbitCyclic i)).2.mem_iff
    (orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem relation_eq : ∀ i,
    cyclicRepresentative (orbitCyclic i) =
      ((relationWords i).map
        (fun g ↦ Rep.representation g (orbitRepresentative i))).sum :=
  {finite_checks(c)}

private theorem canonical_mem_orbit_span (i : Fin {c}) :
    cyclicRepresentative (orbitCyclic i) ∈
      binaryOrbitSpan Rep.representation (orbitRepresentative i) := by
  rw [relation_eq i]
  apply (binaryOrbitSpan Rep.representation (orbitRepresentative i)).list_sum_mem
  intro x hx
  obtain ⟨g, _hg, rfl⟩ := List.mem_map.mp hx
  exact Submodule.subset_span ⟨g, rfl⟩

theorem orbit_span_eq (i : Fin {c}) :
    binaryOrbitSpan Rep.representation (orbitRepresentative i) =
      binaryOrbitSpan Rep.representation
        (cyclicRepresentative (orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical Rep.representation
    (Rep.states (orbitCyclic i)) (canonical_span (orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

end SymmetricSubgroupAsymptotics.{module_name}

end
"""
    text = text.replace(f"namespace Rep := {representation_module}\n", "")
    return text.replace("Rep.", f"{representation_module}.")


def write_atomic(path: Path, payload: bytes, force: bool) -> None:
    require(force or not path.exists(), "output exists; use --force")
    require(len(payload) <= OUTPUT_LIMIT, "Lean output byte ceiling reached")
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("wb", delete=False, dir=path.parent,
                                     prefix=path.name + ".", suffix=".partial") as stream:
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
    parser.add_argument("--top-module", required=True)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    for name in (args.module, args.representation_module, args.top_module):
        require(MODULE_RE.fullmatch(name) is not None, "invalid Lean module")
    data = read_input(args.input)
    payload = emit(args.module, args.representation_module, args.top_module,
                   data, args.input.name).encode()
    write_atomic(args.output, payload, args.force)
    print(f"{args.output}: {len(payload)} bytes; {data['orbit_count']} orbits")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, KeyError, TypeError, json.JSONDecodeError, Refused) as error:
        raise SystemExit(f"refused: {error}")
