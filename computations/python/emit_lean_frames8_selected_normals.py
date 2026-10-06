#!/usr/bin/env python3
"""Render one prepared eight-frame normal registry as checked Lean source.

This is a selected-row renderer.  It accepts one bounded prepared certificate,
does not scan directories, and never invokes Lean or another subprocess.  The
generated module replays every normality and normal-join word in the executable
Cayley group emitted by ``emit_lean_frames8_selected_top.py``.
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


def fin_cases_chain(values: list[str]) -> str:
    result = "(fun i => Fin.elim0 i)"
    for value in reversed(values):
        result = f"(Fin.cases ({value}) {result})"
    return result


def lean_generator_word(word: object) -> str:
    require(isinstance(word, dict), "generator word is not an object")
    tag = word.get("tag")
    if tag == "one":
        return "FiniteGeneratorWord.one"
    if tag == "generator":
        return f"FiniteGeneratorWord.generator {word['index']}"
    if tag == "inv":
        return f"FiniteGeneratorWord.inv ({lean_generator_word(word['word'])})"
    if tag == "mul":
        return (f"FiniteGeneratorWord.mul ({lean_generator_word(word['left'])}) "
                f"({lean_generator_word(word['right'])})")
    raise Refused(f"unsupported generator-word tag {tag!r}")


def lean_join_word(word: object) -> str:
    require(isinstance(word, dict), "join word is not an object")
    tag = word.get("tag")
    if tag == "one":
        return "FiniteNormalJoinWord.one"
    if tag == "parent":
        return f"FiniteNormalJoinWord.parent {word['index']}"
    if tag == "conjugate":
        return ("FiniteNormalJoinWord.conjugate "
                f"(({lean_generator_word(word['conjugator'])}).eval topAmbient)")
    if tag == "inv":
        return f"FiniteNormalJoinWord.inv ({lean_join_word(word['word'])})"
    if tag == "mul":
        return (f"FiniteNormalJoinWord.mul ({lean_join_word(word['left'])}) "
                f"({lean_join_word(word['right'])})")
    raise Refused(f"unsupported join-word tag {tag!r}")


def permutation(value: object, width: int = 8) -> tuple[int, ...]:
    require(isinstance(value, list) and len(value) == width,
            "invalid permutation width")
    require(all(type(x) is int for x in value),
            "nonintegral permutation image")
    row = tuple(x - 1 for x in value)
    require(sorted(row) == list(range(width)), "invalid permutation row")
    return row


def read_and_validate(path: Path) -> dict:
    require(path.is_file() and not path.is_symlink(),
            "missing or redirected prepared certificate")
    raw = path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, "prepared certificate ceiling reached")
    value = json.loads(raw)
    require(isinstance(value, dict) and value.get("schema") == SCHEMA,
            "unexpected prepared certificate schema")
    rows = [permutation(x) for x in value["cayley"]["rows"]]
    require(len(rows) == value.get("top_order"), "Cayley order mismatch")
    position = {row: i for i, row in enumerate(rows)}
    require(len(position) == len(rows), "duplicated Cayley row")
    ambient = [permutation(x) for x in value.get("generators", [])]
    states = [[permutation(x) for x in row]
              for row in value.get("normal_generators", [])]
    normality = value.get("normality")
    children = value.get("children")
    transitions = value.get("transitions")
    class_count = len(value.get("class_representatives", []))
    width = value.get("normal_generator_width")
    require(1 <= len(states) <= 256 and type(width) is int and 1 <= width <= 16,
            "invalid normal-state shape")
    require(all(len(row) == width for row in states),
            "normal generator width mismatch")
    require(len(normality) == len(states) == len(children) == len(transitions),
            "normal certificate row mismatch")
    require(all(x in position for row in states for x in row),
            "normal generator escaped Cayley rows")
    require(all(len(row) == class_count for row in children) and
            all(len(row) == class_count for row in transitions),
            "normal transition width mismatch")
    for i in range(len(states)):
        require(set(normality[i]) == {"positive", "negative"},
                "invalid normality object")
        for sign in ("positive", "negative"):
            matrix = normality[i][sign]
            require(len(matrix) == len(ambient) and
                    all(len(row) == width for row in matrix),
                    "normality word matrix mismatch")
        for j in range(class_count):
            child = children[i][j]
            require(type(child) is int and 0 <= child < len(states),
                    "normal child index out of range")
            record = transitions[i][j]
            require(set(record) == {"parent_to_child", "representative_word",
                                    "child_to_join"},
                    "invalid transition object")
            require(len(record["parent_to_child"]) == width and
                    len(record["child_to_join"]) == width,
                    "transition word width mismatch")
    return {
        "source_row": value.get("source_row"),
        "top_index": value.get("top_index"),
        "states": states,
        "state_rows": [[position[x] for x in row] for row in states],
        "normality": normality,
        "children": children,
        "transitions": transitions,
        "ambient_count": len(ambient),
        "normal_count": len(states),
        "class_count": class_count,
        "width": width,
    }


def emit(module: str, top_module: str, data: dict, input_name: str) -> str:
    n = data["normal_count"]
    c = data["class_count"]
    a = data["ambient_count"]
    width = data["width"]
    state_names = [f"state{i}Generators" for i in range(n)]
    text = f"""import SymmetricSubgroupAsymptotics.{top_module}
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry

/-!
# Selected eight-frame row {data['source_row']}: checked normal registry

Generated by `emit_lean_frames8_selected_normals.py` from the explicit selected
input `{input_name}`.  Lean rechecks every normality and normal-join word in
the executable order-{168 if data['source_row'] == 28 else 'N'} Cayley group.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.{module}

abbrev Source := {top_module}.Source
local instance sourceGroup : Group Source := {top_module}.group

def topAmbient : Fin {a} → Source := {top_module}.ambient
def topRepresentative : Fin {c} → Source := {top_module}.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  {top_module}.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  {top_module}.conjugacy

"""
    for i, rows in enumerate(data["state_rows"]):
        text += f"""private def {state_names[i]} : Fin {width} → Source :=
  {fin_cases_chain([f'(⟨{row}⟩ : Source)' for row in rows])}

"""
    text += f"""def stateGenerators : Fin {n} → Fin {width} → Source :=
  {fin_cases_chain(state_names)}

def child : Fin {n} → Fin {c} → Fin {n} :=
  {fin_cases_chain([fin_cases_chain([str(x) for x in row]) for row in data['children']])}

"""
    for i in range(n):
        normal = data["normality"][i]
        pos = [fin_cases_chain([lean_generator_word(w) for w in row])
               for row in normal["positive"]]
        neg = [fin_cases_chain([lean_generator_word(w) for w in row])
               for row in normal["negative"]]
        text += f"""namespace N{i}

private def positiveWords : Fin {a} → Fin {width} →
    FiniteGeneratorWord (Fin {width}) :=
  {fin_cases_chain(pos)}

private def negativeWords : Fin {a} → Fin {width} →
    FiniteGeneratorWord (Fin {width}) :=
  {fin_cases_chain(neg)}

def normality : FiniteNormalityWordCertificate topAmbient (stateGenerators {i}) where
  positiveWords := positiveWords
  positiveEquations := by native_decide
  negativeWords := negativeWords
  negativeEquations := by native_decide

"""
        names = []
        for j in range(c):
            record = data["transitions"][i][j]
            names.append(f"T{j}.certificate")
            text += f"""namespace T{j}

private def parentWords : Fin {width} → FiniteGeneratorWord (Fin {width}) :=
  {fin_cases_chain([lean_generator_word(w) for w in record['parent_to_child']])}

private def childWords : Fin {width} →
    FiniteNormalJoinWord (Fin {width}) Source :=
  {fin_cases_chain([lean_join_word(w) for w in record['child_to_join']])}

private def representativeWord : FiniteGeneratorWord (Fin {width}) :=
  {lean_generator_word(record['representative_word'])}

def certificate : FiniteNormalJoinTransitionCertificate
    (stateGenerators {i}) (topRepresentative {j})
    (stateGenerators (child {i} {j})) where
  parentToChild := {{
    words := parentWords
    equations := by native_decide }}
  representativeWord := representativeWord
  representativeEquation := by native_decide
  childWords := childWords
  childEquations := by native_decide

end T{j}

"""
        text += f"""def transition : ∀ j : Fin {c},
    FiniteNormalJoinTransitionCertificate
      (stateGenerators {i}) (topRepresentative j)
      (stateGenerators (child {i} j)) :=
  {fin_cases_chain(names)}

end N{i}

"""
    text += f"""noncomputable def normality : ∀ i : Fin {n},
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  {fin_cases_chain([f'N{i}.normality' for i in range(n)])}

noncomputable def transition : ∀ i : Fin {n}, ∀ j : Fin {c},
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) :=
  {fin_cases_chain([f'N{i}.transition' for i in range(n)])}

private theorem bottom_eq :
    Subgroup.closure (Set.range (stateGenerators 0)) = ⊥ := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    fin_cases j <;> rfl
  · exact bot_le

/-- Complete checked normal-join registry for the selected row. -/
noncomputable def data : FiniteNormalJoinWordRegistryData
    topConjugacy.toCardinalCover topAmbient stateGenerators where
  ambient_full := topAmbient_full
  normality := normality
  bottom := 0
  bottom_eq := bottom_eq
  child := child
  transition := transition

theorem complete (N : Subgroup Source) [N.Normal] :
    ∃ i, Subgroup.closure (Set.range (stateGenerators i)) = N :=
  data.complete N

end SymmetricSubgroupAsymptotics.{module}

end
"""
    return text


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
    parser.add_argument("--top-module", required=True)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    require(MODULE_RE.fullmatch(args.module) is not None, "invalid Lean module")
    require(MODULE_RE.fullmatch(args.top_module) is not None, "invalid top module")
    data = read_and_validate(args.input)
    payload = emit(args.module, args.top_module, data, args.input.name).encode()
    write_atomic(args.output, payload, args.force)
    print(f"{args.output}: {len(payload)} bytes; {data['normal_count']} normal states")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, KeyError, TypeError, json.JSONDecodeError, Refused) as error:
        raise SystemExit(f"refused: {error}")
