#!/usr/bin/env python3
"""Emit one complete checked normal registry from explicit selected chunks.

Every input path and the output path are mandatory.  The inputs must be the
complete, nonoverlapping ``normals`` chunks for one selected six-pair action.
There is no action range, directory scan or bulk mode.  This script never
invokes Lean, a subprocess or another exporter.

The producer words are validated against the pinned literal permutations.
The emitted Lean module then rechecks every normality and join-word equation
and constructs ``FiniteNormalJoinWordRegistryData``.  A declared normal order
or producer completeness flag is never used as a Lean premise.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile

sys.dont_write_bytecode = True


ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "certificates/data/six_block.json.gz"
DATA_SHA256 = "446f54807b4f31114d559c9459fb529bd0eb83bbdd744e563a799521ddaa43d3"
WIDTH = 12
ACTION_COUNT = 182
INPUT_LIMIT = 256 * 1024
COMPRESSED_DATA_LIMIT = 128 * 1024
DECOMPRESSED_DATA_LIMIT = 2 * 1024 * 1024
OUTPUT_LIMIT = 4 * 1024 * 1024
MODULE_RE = re.compile(r"[A-Z][A-Za-z0-9_]*\Z")


class Refused(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refused(message)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


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


def permutation(value: object) -> tuple[int, ...]:
    require(isinstance(value, list) and len(value) == WIDTH,
            "invalid degree-twelve permutation")
    require(all(type(x) is int for x in value), "nonintegral permutation image")
    row = tuple(x - 1 for x in value)
    require(sorted(row) == list(range(WIDTH)), "invalid permutation row")
    return row


def packed(row: tuple[int, ...]) -> int:
    return sum(x * WIDTH ** i for i, x in enumerate(row))


def enumerate_group(generators: list[tuple[int, ...]]) -> list[tuple[int, ...]]:
    one = tuple(range(WIDTH))
    rows = [one]
    seen = {one}
    cursor = 0
    while cursor < len(rows):
        require(len(rows) <= 46_080, "selected action row ceiling reached")
        x = rows[cursor]
        for g in generators:
            y = compose(x, g)
            if y not in seen:
                seen.add(y)
                rows.append(y)
        cursor += 1
    return sorted(rows, key=packed)


def read_pinned_data() -> dict:
    require(DATA.is_file() and not DATA.is_symlink(), "missing or redirected six-block data")
    compressed = DATA.read_bytes()
    require(len(compressed) <= COMPRESSED_DATA_LIMIT, "compressed data ceiling reached")
    require(digest(compressed) == DATA_SHA256, "six-block data digest changed")
    raw = gzip.decompress(compressed)
    require(len(raw) <= DECOMPRESSED_DATA_LIMIT, "decompressed data ceiling reached")
    data = json.loads(raw)
    require(data.get("schema_version") == 1, "unexpected six-block schema")
    require(len(data.get("actions", [])) == ACTION_COUNT, "action count changed")
    return data


def read_chunk(path: Path) -> dict:
    require(path.is_file() and not path.is_symlink(), f"missing or redirected input {path}")
    raw = path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, "normal input ceiling reached")
    value = json.loads(raw)
    require(isinstance(value, dict), "normal input is not an object")
    require(value.get("schema_version") == 1, "unexpected selected-chunk schema")
    require(value.get("source_sha256") == DATA_SHA256, "selected source digest changed")
    require(value.get("stage") == "normals", "normal emitter accepts normals chunks only")
    return value


def eval_word(word: object, generators: list[tuple[int, ...]], *, depth: int = 0) -> tuple[int, ...]:
    require(depth <= 256, "word depth ceiling reached")
    require(isinstance(word, dict), "word is not an object")
    tag = word.get("tag")
    if tag == "one":
        require(set(word) == {"tag"}, "unexpected one-word field")
        return tuple(range(WIDTH))
    if tag in ("generator", "parent"):
        require(set(word) == {"tag", "index"}, "unexpected indexed-word field")
        index = word["index"]
        require(type(index) is int and 0 <= index < len(generators),
                "word index out of range")
        return generators[index]
    if tag == "inv":
        require(set(word) == {"tag", "word"}, "unexpected inverse-word field")
        return inverse(eval_word(word["word"], generators, depth=depth + 1))
    if tag == "mul":
        require(set(word) == {"tag", "left", "right"}, "unexpected product-word field")
        return compose(eval_word(word["left"], generators, depth=depth + 1),
                       eval_word(word["right"], generators, depth=depth + 1))
    raise Refused("unsupported generator-word tag")


def eval_join_word(word: object, parent: list[tuple[int, ...]],
                   representative: tuple[int, ...],
                   ambient: list[tuple[int, ...]], *, depth: int = 0) -> tuple[int, ...]:
    require(depth <= 256, "join-word depth ceiling reached")
    require(isinstance(word, dict), "join word is not an object")
    tag = word.get("tag")
    if tag == "one":
        require(set(word) == {"tag"}, "unexpected join-one field")
        return tuple(range(WIDTH))
    if tag == "parent":
        require(set(word) == {"tag", "index"}, "unexpected parent-word field")
        index = word["index"]
        require(type(index) is int and 0 <= index < len(parent),
                "parent-word index out of range")
        return parent[index]
    if tag == "conjugate":
        require(set(word) == {"tag", "conjugator"}, "unexpected conjugate-word field")
        g = eval_word(word["conjugator"], ambient, depth=depth + 1)
        return conjugate(g, representative)
    if tag == "inv":
        require(set(word) == {"tag", "word"}, "unexpected join-inverse field")
        return inverse(eval_join_word(word["word"], parent, representative,
                                      ambient, depth=depth + 1))
    if tag == "mul":
        require(set(word) == {"tag", "left", "right"}, "unexpected join-product field")
        return compose(eval_join_word(word["left"], parent, representative,
                                      ambient, depth=depth + 1),
                       eval_join_word(word["right"], parent, representative,
                                      ambient, depth=depth + 1))
    raise Refused("unsupported join-word tag")


def lean_gen_word(word: object) -> str:
    tag = word["tag"]
    if tag == "one":
        return "FiniteGeneratorWord.one"
    if tag in ("generator", "parent"):
        return f"FiniteGeneratorWord.generator {word['index']}"
    if tag == "inv":
        return f"FiniteGeneratorWord.inv ({lean_gen_word(word['word'])})"
    if tag == "mul":
        return (f"FiniteGeneratorWord.mul ({lean_gen_word(word['left'])}) "
                f"({lean_gen_word(word['right'])})")
    raise Refused("unsupported Lean generator-word tag")


def lean_join_word(word: object) -> str:
    tag = word["tag"]
    if tag == "one":
        return "FiniteNormalJoinWord.one"
    if tag == "parent":
        return f"FiniteNormalJoinWord.parent {word['index']}"
    if tag == "conjugate":
        return ("FiniteNormalJoinWord.conjugate "
                f"(({lean_gen_word(word['conjugator'])}).eval ambient)")
    if tag == "inv":
        return f"FiniteNormalJoinWord.inv ({lean_join_word(word['word'])})"
    if tag == "mul":
        return (f"FiniteNormalJoinWord.mul ({lean_join_word(word['left'])}) "
                f"({lean_join_word(word['right'])})")
    raise Refused("unsupported Lean join-word tag")


def fin_cases_chain(values: list[str]) -> str:
    result = "(fun i => Fin.elim0 i)"
    for value in reversed(values):
        result = f"(Fin.cases ({value}) {result})"
    return result


def validate_and_prepare(chunks: list[dict], data: dict) -> dict:
    require(chunks, "no normal chunks supplied")
    action_number = chunks[0].get("action")
    require(type(action_number) is int and 1 <= action_number <= ACTION_COUNT,
            "selected action number out of range")
    require(all(chunk.get("action") == action_number for chunk in chunks),
            "normal chunks belong to different actions")
    action = data["actions"][action_number - 1]
    ambient = [permutation(row) for row in action["generators"]]
    require(1 <= len(ambient) <= 16,
            "selected ambient generator width outside the narrow ceiling")
    group_rows = enumerate_group(ambient)
    position = {row: i for i, row in enumerate(group_rows)}
    require(all(chunk.get("action_order") == len(group_rows) == action["order"]
                for chunk in chunks), "normal action order mismatch")
    require(all(chunk.get("ambient_generator_count") == len(ambient)
                for chunk in chunks), "normal ambient count mismatch")

    records = []
    for chunk in chunks:
        content = chunk.get("content")
        require(isinstance(content, dict) and isinstance(content.get("rows"), list),
                "missing normal rows")
        records.extend(content["rows"])
    records.sort(key=lambda row: row.get("normal_index", 0))
    pinned_normals = action["normals"]
    require(1 <= len(pinned_normals) <= 64,
            "selected normal count outside the narrow ceiling")
    require([row.get("normal_index") for row in records] ==
            list(range(1, len(pinned_normals) + 1)),
            "normal chunks are not a complete exact partition")

    representatives = [permutation(row) for row in action["class_representatives"]]
    require(1 <= len(representatives) <= 128,
            "selected class count outside the narrow ceiling")
    state_generators = []
    for index, (record, pinned) in enumerate(zip(records, pinned_normals)):
        generators = [permutation(row) for row in pinned["generators"]]
        require(all(g in position for g in generators), "normal generator escaped action")
        require(record.get("declared_order") == pinned["order"], "normal order metadata mismatch")
        require(len(generators) <= 16,
                "normal generator width outside the narrow ceiling")
        state_generators.append(generators)

        normality = record.get("normality")
        require(isinstance(normality, dict), "missing normality word data")
        for sign in ("positive", "negative"):
            matrix = normality.get(sign)
            require(isinstance(matrix, list) and len(matrix) == len(ambient),
                    "normality ambient width mismatch")
            require(all(isinstance(row, list) and len(row) == len(generators)
                        for row in matrix), "normality generator width mismatch")
            for a, row in enumerate(matrix):
                for j, word in enumerate(row):
                    actual = eval_word(word, generators)
                    target = (conjugate(ambient[a], generators[j]) if sign == "positive"
                              else conjugate(inverse(ambient[a]), generators[j]))
                    require(actual == target, "normality word equation failed")

        transitions = record.get("transitions")
        require(isinstance(transitions, list) and len(transitions) == len(representatives),
                "normal transition count mismatch")
        pinned_joins = pinned.get("joins")
        full_pinned_join_row = (isinstance(pinned_joins, list) and
                                len(pinned_joins) == len(representatives))
        for class_index, transition in enumerate(transitions):
            require(transition.get("class_index") == class_index + 1,
                    "transition class index mismatch")
            child_index = transition.get("child_index")
            require(type(child_index) is int and
                    1 <= child_index <= len(pinned_normals),
                    "transition child index mismatch")
            if full_pinned_join_row:
                require(child_index == pinned_joins[class_index],
                        "full pinned normal join row disagrees with selected transition")
            words = transition.get("words")
            require(isinstance(words, dict), "missing transition words")
            child = [permutation(row) for row in pinned_normals[child_index - 1]["generators"]]
            parent_to_child = words.get("parent_to_child")
            child_to_join = words.get("child_to_join")
            require(isinstance(parent_to_child, list) and
                    len(parent_to_child) == len(generators),
                    "parent-to-child width mismatch")
            require(isinstance(child_to_join, list) and len(child_to_join) == len(child),
                    "child-to-join width mismatch")
            for j, word in enumerate(parent_to_child):
                require(eval_word(word, child) == generators[j],
                        "parent-to-child equation failed")
            require(eval_word(words.get("representative_word"), child) ==
                    representatives[class_index], "representative word equation failed")
            for j, word in enumerate(child_to_join):
                require(eval_join_word(word, generators, representatives[class_index], ambient) == child[j],
                        "child join-word equation failed")

    one = tuple(range(WIDTH))
    normal_width = max(1, max(len(generators) for generators in state_generators))
    padded_rows = [generators + [one] * (normal_width - len(generators))
                   for generators in state_generators]
    return {
        "action_number": action_number,
        "ambient": ambient,
        "group_rows": group_rows,
        "position": position,
        "records": records,
        "pinned_normals": pinned_normals,
        "ambient_count": len(ambient),
        "normal_width": normal_width,
        "state_rows": [[position[g] for g in row] for row in padded_rows],
        "representatives": representatives,
    }


def emit_module(module: str, class_module: str, prepared: dict,
                input_names: list[str]) -> str:
    records = prepared["records"]
    pinned_normals = prepared["pinned_normals"]
    state_rows = prepared["state_rows"]
    normal_count = len(records)
    class_count = len(prepared["representatives"])
    ambient_count = prepared["ambient_count"]
    normal_width = prepared["normal_width"]
    require(1 <= ambient_count <= 16,
            "selected ambient generator width outside the narrow ceiling")
    require(1 <= normal_width <= 16,
            "selected normal generator width outside the narrow ceiling")
    require(1 <= normal_count <= 64,
            "selected normal count outside the narrow ceiling")
    require(1 <= class_count <= 128,
            "selected class count outside the narrow ceiling")
    prefix = f"SymmetricSubgroupAsymptotics.{class_module}"
    text = f"""import SymmetricSubgroupAsymptotics.{class_module}
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry

/-!
# Selected six-pair action {prepared['action_number']}: checked normal registry

Generated by `emit_lean_six_pair_selected_normals.py` from the explicit inputs
`{', '.join(input_names)}` and the pinned six-block source digest
`{DATA_SHA256}`.  Every compact word is re-evaluated in the committed
executable row group.  The normal-state list is complete by the generic
normal-join registry theorem, not by an asserted producer flag.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.{module}

open {class_module}

local instance selectedSourceGroup : Group Source := group

"""
    state_names = []
    normality_names = []
    for i, (record, rows) in enumerate(zip(records, state_rows)):
        state_name = f"state{i}Generators"
        state_names.append(state_name)
        text += f"""private def {state_name} : Fin {normal_width} → Source :=
  {fin_cases_chain([f'(⟨{row}⟩ : Source)' for row in rows])}

"""
    text += f"""def stateGenerators : Fin {normal_count} → Fin {normal_width} → Source :=
  {fin_cases_chain(state_names)}

"""
    for i, (record, pinned) in enumerate(zip(records, pinned_normals)):
        generator_count = len(pinned["generators"])
        normality = record["normality"]
        positive = []
        negative = []
        for a in range(ambient_count):
            prow = (list(normality["positive"][a]) +
                    ([{"tag": "one"}] * (normal_width - generator_count)))
            nrow = (list(normality["negative"][a]) +
                    ([{"tag": "one"}] * (normal_width - generator_count)))
            positive.append(fin_cases_chain([lean_gen_word(word) for word in prow]))
            negative.append(fin_cases_chain([lean_gen_word(word) for word in nrow]))
        text += f"""namespace N{i}

private def positiveWords : Fin {ambient_count} → Fin {normal_width} →
    FiniteGeneratorWord (Fin {normal_width}) :=
  {fin_cases_chain(positive)}

private def negativeWords : Fin {ambient_count} → Fin {normal_width} →
    FiniteGeneratorWord (Fin {normal_width}) :=
  {fin_cases_chain(negative)}

def normality : FiniteNormalityWordCertificate ambient (stateGenerators {i}) where
  positiveWords := positiveWords
  positiveEquations := by native_decide
  negativeWords := negativeWords
  negativeEquations := by native_decide

"""
        transition_names = []
        for j, transition in enumerate(record["transitions"]):
            child = transition["child_index"] - 1
            child_count = len(pinned_normals[child]["generators"])
            words = transition["words"]
            parent_words = (list(words["parent_to_child"]) +
                            ([{"tag": "one"}] * (normal_width - generator_count)))
            child_words = (list(words["child_to_join"]) +
                           ([{"tag": "one"}] * (normal_width - child_count)))
            transition_names.append(f"T{j}.certificate")
            text += f"""namespace T{j}

private def parentWords : Fin {normal_width} →
    FiniteGeneratorWord (Fin {normal_width}) :=
  {fin_cases_chain([lean_gen_word(word) for word in parent_words])}

private def childWords : Fin {normal_width} →
    FiniteNormalJoinWord (Fin {normal_width}) Source :=
  {fin_cases_chain([lean_join_word(word) for word in child_words])}

private def representativeWord : FiniteGeneratorWord (Fin {normal_width}) :=
  {lean_gen_word(words['representative_word'])}

def certificate : FiniteNormalJoinTransitionCertificate
    (stateGenerators {i}) (representative {j}) (stateGenerators {child}) where
  parentToChild := {{
    words := parentWords
    equations := by native_decide }}
  representativeWord := representativeWord
  representativeEquation := by native_decide
  childWords := childWords
  childEquations := by native_decide

end T{j}

"""
        text += f"""def transition : ∀ j : Fin {class_count},
    FiniteNormalJoinTransitionCertificate
      (stateGenerators {i}) (representative j)
      (stateGenerators (child {i} j)) :=
  {fin_cases_chain(transition_names)}

end N{i}

"""
        normality_names.append(f"N{i}.normality")

    child_rows = []
    for record in records:
        child_rows.append(fin_cases_chain(
            [str(transition["child_index"] - 1) for transition in record["transitions"]]))

    # The transition declarations above refer to `child`; put its definition
    # before them in the final byte stream.
    child_definition = f"""def child : Fin {normal_count} → Fin {class_count} → Fin {normal_count} :=
  {fin_cases_chain(child_rows)}

"""
    marker = (f"def stateGenerators : Fin {normal_count} → "
              f"Fin {normal_width} → Source :=\n")
    insertion = text.index(marker)
    after_state = text.index("\n\n", insertion) + 2
    text = text[:after_state] + child_definition + text[after_state:]

    text += f"""noncomputable def normality : ∀ i : Fin {normal_count},
    FiniteNormalityWordCertificate ambient (stateGenerators i) :=
  {fin_cases_chain(normality_names)}

noncomputable def transition : ∀ i : Fin {normal_count}, ∀ j : Fin {class_count},
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (representative j)
      (stateGenerators (child i j)) :=
  {fin_cases_chain([f'N{i}.transition' for i in range(normal_count)])}

private theorem bottom_eq :
    Subgroup.closure (Set.range (stateGenerators 0)) = ⊥ := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    fin_cases j <;> rfl
  · exact bot_le

/-- Complete checked normal-join registry for the selected row action. -/
noncomputable def normalRegistry : FiniteNormalJoinWordRegistryData
    conjugacyCover ambient stateGenerators where
  ambient_full := ambient_full
  normality := normality
  bottom := 0
  bottom_eq := bottom_eq
  child := child
  transition := transition

/-- Every literal normal subgroup of the executable selected row group occurs
among the emitted generated states. -/
theorem normal_complete (N : Subgroup Source) [N.Normal] :
    ∃ i, Subgroup.closure (Set.range (stateGenerators i)) = N :=
  normalRegistry.complete N

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
    parser.add_argument("--input", required=True, action="append", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--module", required=True)
    parser.add_argument("--class-module", required=True)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    require(MODULE_RE.fullmatch(args.module) is not None, "invalid Lean module name")
    require(MODULE_RE.fullmatch(args.class_module) is not None, "invalid class module name")
    require(len(set(args.input)) == len(args.input), "duplicate normal input")
    chunks = [read_chunk(path) for path in args.input]
    prepared = validate_and_prepare(chunks, read_pinned_data())
    payload = emit_module(args.module, args.class_module, prepared,
                          [path.name for path in args.input]).encode()
    write_atomic(args.output, payload, args.force)
    print(f"{args.output}: {len(payload)} bytes; action {prepared['action_number']}; "
          f"normal states {len(prepared['records'])}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, json.JSONDecodeError, Refused) as error:
        raise SystemExit(f"refused: {error}")
