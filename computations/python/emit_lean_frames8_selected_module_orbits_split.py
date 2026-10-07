#!/usr/bin/env python3
"""Emit one selected module-orbit certificate in bounded Lean chunks.

The monolithic pilot expands thousands of orbit checks in one elaboration
unit.  This renderer keeps the public theorem unchanged while putting at
most ``--chunk-size`` vector orbits in any worker module.  It is a bounded
single-input producer and invokes no subprocess.
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
    path = Path(__file__).with_name("emit_lean_frames8_selected_module_orbits.py")
    spec = importlib.util.spec_from_file_location("frames8_orbits_base", path)
    require(spec is not None and spec.loader is not None, "cannot load orbit reader")
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


def header(imports: list[str], namespace: str, description: str) -> str:
    return "\n".join(f"import SymmetricSubgroupAsymptotics.{x}" for x in imports) + f"""

/-! {description} -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.{namespace}

"""


def emit_data(base, namespace: str, representation_module: str,
              top_module: str, data: dict, input_name: str) -> str:
    c, d = data["orbit_count"], data["cyclic_count"]
    text = header(
        [representation_module,
         "BinaryCoordinateOrbitSpanCertificate",
         "BinaryOrbitSpanRebase",
         "FiniteLinearOrbitMinimalStabilizerCover"],
        namespace,
        f"Selected row {data['source_row']} orbit data, generated from `{input_name}`.")
    text += f"""abbrev Source := {representation_module}.Source
local instance sourceGroup : Group Source := {top_module}.group
abbrev ModelModule := {representation_module}.ModelModule

def sourceWord (word : List (Fin {data['generator_count']})) : Source :=
  (word.reverse.map {top_module}.ambient).prod

def orbitRepresentative (i : Fin {c}) : ModelModule :=
  binaryVectorOfMask 16 ({base.lookup([str(x) for x in data['reps']])})

def stabilizerCard (i : Fin {c}) : ℕ :=
  {base.lookup([str(x) for x in data['stabilizers']])}

def orbitCyclic (i : Fin {c}) : Fin {d} :=
  {base.lookup([str(x) for x in data['orbit_cyclic']])}

def cyclicRepresentative (i : Fin {d}) : ModelModule :=
  binaryVectorOfMask 16 ({base.lookup([str(x) for x in data['cyclic_reps']])})

def cyclicState (i : Fin {d}) : Fin {data['state_count']} :=
  {base.lookup([str(x) for x in data['cyclic_state']])}

theorem representativeCode_injective :
    Function.Injective
      (fun i ↦ binaryVectorMask (orbitRepresentative i)) := by native_decide

theorem orbit_card_sum :
    (∑ i : Fin {c}, Nat.card Source / stabilizerCard i) =
      Nat.card ModelModule := by
  rw [{top_module}.source_card, Nat.card_eq_fintype_card]
  native_decide

end SymmetricSubgroupAsymptotics.{namespace}

end
"""
    return text


def emit_canonical(base, namespace: str, data_module: str,
                   representation_module: str, top_module: str,
                   data: dict) -> str:
    d = data["cyclic_count"]
    text = header([data_module], namespace,
                  f"Selected row {data['source_row']} canonical cyclic spans.")
    text += f"""namespace D := {data_module}
abbrev Source := D.Source
local instance sourceGroup : Group Source := {top_module}.group

"""
    for i, (dim, state, rows) in enumerate(zip(
            data["dimensions"], data["cyclic_state"], data["canonical_words"])):
        require(len(rows) == dim, "canonical basis-word width mismatch")
        words = base.lookup([
            base.lean_word_list(x, data["generator_count"]) for x in rows],
            "j.val") if rows else "[]"
        words = words.replace("sourceWord", "D.sourceWord")
        text += f"""namespace C{i}

private def words (j : Fin {dim}) : List Source := {words}

private theorem representative_mem :
    D.cyclicRepresentative {i} ∈
      ({representation_module}.charts {state}).2.space := by native_decide

private theorem basis_eq : ∀ j,
    ({representation_module}.charts {state}).2.inclusion (Pi.single j 1) =
      ((words j).map (fun g ↦ {representation_module}.representation g
        (D.cyclicRepresentative {i}))).sum := by
  native_decide

theorem span_eq :
    ({representation_module}.states {state}).toSubmodule =
      binaryOrbitSpan {representation_module}.representation
        (D.cyclicRepresentative {i}) := by
  rw [{representation_module}.states_space]
  exact binaryCoordinate_eq_orbitSpan
    ({representation_module}.charts {state}).2
    {representation_module}.representation
    ({representation_module}.states {state})
    ({representation_module}.states_space {state})
    (D.cyclicRepresentative {i}) representative_mem words basis_eq

end C{i}

"""
    cases = "\n".join(f"  · exact C{i}.span_eq" for i in range(d))
    text += f"""theorem canonical_span (i : Fin {d}) :
    ({representation_module}.states (D.cyclicState i)).toSubmodule =
      binaryOrbitSpan {representation_module}.representation
        (D.cyclicRepresentative i) := by
  fin_cases i
{cases}

end SymmetricSubgroupAsymptotics.{namespace}

end
"""
    return text.replace(f"namespace D := {data_module}\n", "").replace(
        "D.", f"{data_module}.")


def emit_chunk(base, namespace: str, data_module: str,
               representation_module: str, top_module: str,
               data: dict, start: int, stop: int) -> str:
    size = stop - start
    c = data["orbit_count"]
    relation_values = [
        base.lean_word_list(x, data["generator_count"])
        for x in data["relations"][start:stop]]
    relation_expr = base.lookup(relation_values, "i.val").replace(
        "sourceWord", "D.sourceWord")
    text = header([data_module], namespace,
                  f"Selected row {data['source_row']} vector orbits {start}–{stop - 1}.")
    text += f"""namespace D := {data_module}
abbrev Source := D.Source
local instance sourceGroup : Group Source := {top_module}.group

def embed (i : Fin {size}) : Fin {c} :=
  ⟨{start} + i.val, by omega⟩

theorem minimal : ∀ i : Fin {size}, ∀ g,
    binaryVectorMask (D.orbitRepresentative (embed i)) ≤
      binaryVectorMask ({representation_module}.representation g
        (D.orbitRepresentative (embed i))) :=
  {base.finite_checks(size)}

theorem stabilizer_card : ∀ i : Fin {size},
    Nat.card (representationVectorStabilizer
      {representation_module}.representation
      (D.orbitRepresentative (embed i))) =
        D.stabilizerCard (embed i) := by
  intro i
  letI : DecidablePred (fun g : Source ↦
      g ∈ representationVectorStabilizer
        {representation_module}.representation
        (D.orbitRepresentative (embed i))) :=
    fun g ↦ decidable_of_iff
      ({representation_module}.representation g
        (D.orbitRepresentative (embed i)) = D.orbitRepresentative (embed i))
      Iff.rfl
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  fin_cases i <;> native_decide

private def relationWords (i : Fin {size}) : List Source :=
  {relation_expr}

theorem orbit_mem_chart : ∀ i : Fin {size},
    ({representation_module}.charts
      (D.cyclicState (D.orbitCyclic (embed i)))).2.inclusion
        (({representation_module}.charts
          (D.cyclicState (D.orbitCyclic (embed i)))).2.coordinates
          (D.orbitRepresentative (embed i))) =
      D.orbitRepresentative (embed i) :=
  {base.finite_checks(size)}

theorem relation_eq : ∀ i : Fin {size},
    D.cyclicRepresentative (D.orbitCyclic (embed i)) =
      ((relationWords i).map (fun g ↦
        {representation_module}.representation g
          (D.orbitRepresentative (embed i)))).sum :=
  {base.finite_checks(size)}

theorem canonical_mem_orbit_span (i : Fin {size}) :
    D.cyclicRepresentative (D.orbitCyclic (embed i)) ∈
      binaryOrbitSpan {representation_module}.representation
        (D.orbitRepresentative (embed i)) := by
  rw [relation_eq i]
  apply (binaryOrbitSpan {representation_module}.representation
    (D.orbitRepresentative (embed i))).list_sum_mem
  intro x hx
  obtain ⟨g, _hg, rfl⟩ := List.mem_map.mp hx
  exact Submodule.subset_span ⟨g, rfl⟩

end SymmetricSubgroupAsymptotics.{namespace}

end
"""
    return text.replace(f"namespace D := {data_module}\n", "").replace(
        "D.", f"{data_module}.")


def dispatch(chunks: list[tuple[str, int, int]], theorem: str,
             extra: str = "") -> str:
    lines = []
    for module, start, stop in chunks:
        size = stop - start
        lines += [f"  by_cases h{start} : i.val < {stop}",
                  f"  · let j : Fin {size} := ⟨i.val - {start}, by omega⟩",
                  f"    have hj : {module}.embed j = i := by",
                  "      apply Fin.ext",
                  (f"      simp [{module}.embed, j]"
                   if start == 0 else
                   f"      simp [{module}.embed, j]\n      omega"),
                  "    rw [← hj]",
                  f"    exact {module}.{theorem} j{extra}"]
    lines.append("  omega")
    return "\n".join(lines)


def emit_assembly(namespace: str, data_module: str, canonical_module: str,
                  chunk_modules: list[tuple[str, int, int]],
                  representation_module: str, top_module: str,
                  data: dict) -> str:
    c, d = data["orbit_count"], data["cyclic_count"]
    text = header([canonical_module] + [x[0] for x in chunk_modules], namespace,
                  f"Selected row {data['source_row']} complete bounded orbit cover.")
    text += f"""namespace D := {data_module}
abbrev Source := D.Source
local instance sourceGroup : Group Source := {top_module}.group
abbrev ModelModule := {representation_module}.ModelModule

private theorem representative_minimal (i : Fin {c}) (g : Source) :
    binaryVectorMask (D.orbitRepresentative i) ≤
      binaryVectorMask ({representation_module}.representation g
        (D.orbitRepresentative i)) := by
{dispatch(chunk_modules, 'minimal', ' g')}

private theorem stabilizer_card (i : Fin {c}) :
    Nat.card (representationVectorStabilizer
      {representation_module}.representation (D.orbitRepresentative i)) =
        D.stabilizerCard i := by
{dispatch(chunk_modules, 'stabilizer_card')}

noncomputable def orbitCover :
    FiniteLinearOrbitMinimalStabilizerCover
      {representation_module}.representation D.orbitRepresentative where
  code := binaryVectorMask
  representativeCode_injective := D.representativeCode_injective
  minimal := representative_minimal
  stabilizerCard := D.stabilizerCard
  stabilizer_card := stabilizer_card
  orbit_card_sum := D.orbit_card_sum

private theorem orbit_mem_chart (i : Fin {c}) :
    ({representation_module}.charts
      (D.cyclicState (D.orbitCyclic i))).2.inclusion
        (({representation_module}.charts
          (D.cyclicState (D.orbitCyclic i))).2.coordinates
          (D.orbitRepresentative i)) = D.orbitRepresentative i := by
{dispatch(chunk_modules, 'orbit_mem_chart')}

private theorem orbit_mem_state (i : Fin {c}) :
    D.orbitRepresentative i ∈
      ({representation_module}.states
        (D.cyclicState (D.orbitCyclic i))).toSubmodule := by
  rw [{representation_module}.states_space]
  exact (({representation_module}.charts
    (D.cyclicState (D.orbitCyclic i))).2.mem_iff
      (D.orbitRepresentative i)).mpr (orbit_mem_chart i)

private theorem canonical_mem_orbit_span (i : Fin {c}) :
    D.cyclicRepresentative (D.orbitCyclic i) ∈
      binaryOrbitSpan {representation_module}.representation
        (D.orbitRepresentative i) := by
{dispatch(chunk_modules, 'canonical_mem_orbit_span')}

theorem orbit_span_eq (i : Fin {c}) :
    binaryOrbitSpan {representation_module}.representation
        (D.orbitRepresentative i) =
      binaryOrbitSpan {representation_module}.representation
        (D.cyclicRepresentative (D.orbitCyclic i)) :=
  binaryOrbitSpan_eq_of_canonical {representation_module}.representation
    ({representation_module}.states (D.cyclicState (D.orbitCyclic i)))
    ({canonical_module}.canonical_span (D.orbitCyclic i))
    (orbit_mem_state i) (canonical_mem_orbit_span i)

abbrev sourceWord := D.sourceWord
abbrev orbitRepresentative := D.orbitRepresentative
abbrev stabilizerCard := D.stabilizerCard
abbrev orbitCyclic := D.orbitCyclic
abbrev cyclicRepresentative := D.cyclicRepresentative
abbrev cyclicState := D.cyclicState

end SymmetricSubgroupAsymptotics.{namespace}

end
"""
    return text.replace(f"namespace D := {data_module}\n", "").replace(
        "D.", f"{data_module}.")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--module", required=True,
                        help="Final assembly module name")
    parser.add_argument("--representation-module", required=True)
    parser.add_argument("--top-module", required=True)
    parser.add_argument("--chunk-size", type=int, default=256)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    for name in (args.module, args.representation_module, args.top_module):
        require(MODULE_RE.fullmatch(name) is not None, "invalid module name")
    require(32 <= args.chunk_size <= 512, "chunk size outside 32..512")
    base = load_base()
    data = base.read_input(args.input)
    data_module = args.module + "Data"
    canonical_module = args.module + "Canonical"
    chunks = []
    for start in range(0, data["orbit_count"], args.chunk_size):
        stop = min(data["orbit_count"], start + args.chunk_size)
        chunks.append((args.module + f"Chunk{start}", start, stop))
    outputs = {
        data_module: emit_data(base, data_module, args.representation_module,
                               args.top_module, data, args.input.name),
        canonical_module: emit_canonical(
            base, canonical_module, data_module, args.representation_module,
            args.top_module, data),
        args.module: emit_assembly(
            args.module, data_module, canonical_module, chunks,
            args.representation_module, args.top_module, data),
    }
    for module, start, stop in chunks:
        outputs[module] = emit_chunk(
            base, module, data_module, args.representation_module,
            args.top_module, data, start, stop)
    for module, payload in outputs.items():
        write_atomic(args.output_dir / f"{module}.lean", payload, args.force)
    print(f"{args.module}: {data['orbit_count']} orbits in {len(chunks)} chunks; "
          + ", ".join(f"{name}={len(payload.encode())}" for name, payload in outputs.items()))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, KeyError, TypeError, Refused, ValueError) as error:
        raise SystemExit(f"refused: {error}")
