#!/usr/bin/env python3
"""Emit one kernel-checked Lean class module for a selected degree-16 action.

Every input JSON and the output Lean path are explicit.  The inputs must be
the complete nonoverlapping ``classes`` chunks produced from the pinned
nonbinary datasets.  This emitter has no directory scan, action range, or
bulk mode.  It never invokes Lean, a subprocess, or another exporter.

The output does not trust the producer's class or centralizer assertions.  It
contains an executable Cayley row group, a generator-invariant class code,
and literal reversible row charts for every centralizer kernel and top image.
Lean's kernel rechecks all finite equations.  Normal-subgroup rows are a
separate later dependency and are deliberately outside this emitter.
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
ACTIONS = ROOT / "certificates/data/nonbinary_actions.json"
NORMALS = ROOT / "certificates/data/nonbinary_normals.jsonl.gz"
ACTIONS_SHA256 = "3c40109679d70c5929a1b5cbf7c65c390c18ee41a32e07981bf2190e1facffea"
NORMALS_SHA256 = "bfe1aa3d93e17c21457f618296af0f761f5bc2b906613e9a853ab2cca4144aa3"
WIDTH = 16
ACTION_WIDTH = 16
ACTION_COUNT = 527
INPUT_LIMIT = 1024 * 1024
ACTIONS_INPUT_LIMIT = 1024 * 1024
NORMALS_COMPRESSED_LIMIT = 1024 * 1024
NORMALS_DECOMPRESSED_LIMIT = 8 * 1024 * 1024
OUTPUT_LIMIT = 8 * 1024 * 1024
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


def permutation(value: object, width: int = WIDTH) -> tuple[int, ...]:
    require(isinstance(value, list) and len(value) == width,
            "invalid permutation row width")
    require(all(type(x) is int for x in value), "nonintegral permutation image")
    row = tuple(x - 1 for x in value)
    require(sorted(row) == list(range(width)), "invalid permutation row")
    return row


def packed(row: tuple[int, ...]) -> int:
    n = len(row)
    return sum(x * n ** i for i, x in enumerate(row))


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
    """A dependent Fin eliminator which may safely return data in Type."""
    result = "(fun i => Fin.elim0 i)"
    for value in reversed(values):
        result = f"(Fin.cases {value} {result})"
    return result


def read_pinned_data() -> dict[str, dict]:
    require(ACTIONS.is_file() and not ACTIONS.is_symlink(),
            "missing or redirected nonbinary actions")
    action_raw = ACTIONS.read_bytes()
    require(len(action_raw) <= ACTIONS_INPUT_LIMIT, "action input ceiling reached")
    require(digest(action_raw) == ACTIONS_SHA256, "action input digest changed")
    action_data = json.loads(action_raw)
    actions = action_data.get("actions")
    require(action_data.get("schema_version") == 1 and
            isinstance(actions, list) and len(actions) == ACTION_COUNT,
            "unexpected nonbinary action data")
    require(NORMALS.is_file() and not NORMALS.is_symlink(),
            "missing or redirected nonbinary normals")
    compressed = NORMALS.read_bytes()
    require(len(compressed) <= NORMALS_COMPRESSED_LIMIT,
            "compressed normal input ceiling reached")
    require(digest(compressed) == NORMALS_SHA256, "normal input digest changed")
    normal_raw = gzip.decompress(compressed)
    require(len(normal_raw) <= NORMALS_DECOMPRESSED_LIMIT,
            "decompressed normal input ceiling reached")
    normals = [json.loads(line) for line in normal_raw.splitlines() if line.strip()]
    require(len(normals) == ACTION_COUNT, "normal row count changed")
    by_id = {row.get("action_id"): row for row in normals}
    require(len(by_id) == ACTION_COUNT, "duplicate normal action id")
    result = {}
    for index, action in enumerate(actions):
        action_id = action.get("action_id")
        require(action_id in by_id, f"missing normal row for {action_id}")
        result[action_id] = {**action, **by_id[action_id], "catalogue_index": index}
    return result


def read_chunk(path: Path) -> dict:
    require(path.is_file() and not path.is_symlink(), "missing or redirected input JSON")
    raw = path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, "input JSON ceiling reached")
    value = json.loads(raw)
    require(isinstance(value, dict), "input JSON is not an object")
    require(value.get("schema_version") == 1, "unexpected selected-chunk schema")
    require(value.get("actions_sha256") == ACTIONS_SHA256,
            "selected action source digest changed")
    require(value.get("normals_sha256") == NORMALS_SHA256,
            "selected normal source digest changed")
    require(value.get("stage") == "classes", "emitter accepts classes chunks only")
    return value


def positive_table(generators: list[tuple[int, ...]]) -> dict:
    require(generators, "empty generator tuple")
    one = tuple(range(WIDTH))
    rows = [one]
    position = {one: 0}
    parents = [0]
    letters = [0]
    transitions: list[list[int]] = []
    cursor = 0
    while cursor < len(rows):
        require(len(rows) <= 46_080, "selected action row ceiling reached")
        current = rows[cursor]
        edges = []
        for letter, generator in enumerate(generators):
            target = compose(current, generator)
            if target not in position:
                position[target] = len(rows)
                rows.append(target)
                parents.append(cursor)
                letters.append(letter)
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
        "parent": [remap[parents[i]] for i in order],
        "letter": [letters[i] for i in order],
        "identity": remap[0],
        "next": nxt,
        "prev": prev,
    }


def evaluate_word(word: object, generators: list[tuple[int, ...]], *, depth: int = 0) -> tuple[int, ...]:
    require(depth <= 128, "selected word depth ceiling reached")
    require(isinstance(word, dict), "word is not an object")
    tag = word.get("tag")
    if tag == "one":
        require(set(word) == {"tag"}, "unexpected one-word field")
        return tuple(range(WIDTH))
    if tag == "generator":
        require(set(word) == {"tag", "index"}, "unexpected generator-word field")
        index = word["index"]
        require(type(index) is int and 0 <= index < len(generators),
                "generator-word index out of range")
        return generators[index]
    if tag == "inv":
        require(set(word) == {"tag", "word"}, "unexpected inverse-word field")
        return inverse(evaluate_word(word["word"], generators, depth=depth + 1))
    if tag == "mul":
        require(set(word) == {"tag", "left", "right"}, "unexpected product-word field")
        return compose(evaluate_word(word["left"], generators, depth=depth + 1),
                       evaluate_word(word["right"], generators, depth=depth + 1))
    raise Refused("unsupported selected word tag")


def validate_and_prepare(chunks: list[dict], data: dict[str, dict]) -> dict:
    require(chunks, "no selected class chunks")
    action_id = chunks[0].get("action_id")
    require(isinstance(action_id, str) and action_id in data,
            "selected action id is unknown")
    require(all(chunk.get("action_id") == action_id for chunk in chunks),
            "selected chunks belong to different actions")
    action = data[action_id]
    generators = [permutation(row) for row in action["generators"]]
    require(1 <= len(generators) <= 16,
            "selected ambient generator width outside the narrow ceiling")
    require(all(chunk.get("ambient_generator_count") == len(generators)
                for chunk in chunks),
            "ambient generator count mismatch")
    table = positive_table(generators)
    require(all(chunk.get("action_order") == len(table["rows"])
                for chunk in chunks) and len(table["rows"]) == action["order"],
            "action order mismatch")
    selected_rows = []
    for chunk in chunks:
        content = chunk.get("content")
        require(isinstance(content, dict) and isinstance(content.get("rows"), list),
                "missing class content")
        selected_rows.extend(content["rows"])
    selected_rows.sort(key=lambda row: row.get("class_index", 0))
    all_representatives = [permutation(row["representative"])
                           for row in action["classes"]]
    require(1 <= len(all_representatives) <= 128,
            "selected class count outside the narrow ceiling")
    require(len(selected_rows) == len(all_representatives),
            "selected class row count mismatch")

    conjugacy_classes = []
    row_class: dict[tuple[int, ...], int] = {}
    prepared_rows = []
    class_card_sum = 0
    for index, (record, representative) in enumerate(zip(selected_rows, all_representatives)):
        require(isinstance(record, dict), "invalid selected class record")
        require(record.get("class_index") == index + 1, "class index mismatch")
        require(permutation(record.get("representative")) == representative,
                "class representative mismatch")
        require(representative in table["position"], "representative escaped action")
        centralizer = [g for g in table["rows"]
                       if compose(g, representative) == compose(representative, g)]
        conjugacy_class = {conjugate(g, representative) for g in table["rows"]}
        require(len(centralizer) == record.get("centralizer_card"),
                "centralizer cardinality mismatch")
        require(len(conjugacy_class) == record.get("class_card"),
                "class cardinality mismatch")
        require(len(table["rows"]) == len(centralizer) * len(conjugacy_class),
                "orbit-centralizer product mismatch")
        require(all(conjugacy_class.isdisjoint(old) for old in conjugacy_classes),
                "selected representatives are conjugate")
        conjugacy_classes.append(conjugacy_class)
        for row in conjugacy_class:
            require(row not in row_class, "class code collision")
            row_class[row] = index
        class_card_sum += len(conjugacy_class)

        require(evaluate_word(record.get("representative_word"), generators) == representative,
                "representative word equation failed")
        chart_words = record.get("faithful_centralizer_chart")
        require(isinstance(chart_words, list) and chart_words,
                "empty faithful centralizer chart")
        chart_rows = [evaluate_word(word, generators) for word in chart_words]
        require(set(chart_rows) == set(centralizer) and
                len(chart_rows) == len(centralizer),
                "faithful centralizer chart is not reversible")
        prepared_rows.append({
            "representative_index": table["position"][representative],
            "kernel_indices": [table["identity"]],
            "top_indices": [table["position"][row] for row in chart_rows],
            "centralizer_card": len(centralizer),
        })

    require(class_card_sum == len(table["rows"]),
            "selected classes do not exhaust action")
    require(all(chunk["content"].get("class_card_sum") == class_card_sum
                for chunk in chunks), "class-card sum metadata mismatch")
    require(set(row_class) == set(table["rows"]), "class code is incomplete")
    return {
        "action_id": action_id,
        "generators": generators,
        "table": table,
        "class_code": [row_class[row] for row in table["rows"]],
        "classes": prepared_rows,
    }


def permutation_def(name: str, row: tuple[int, ...], width: int) -> str:
    inv = inverse(row)
    return f"""private def {name} : Equiv.Perm (Fin {width}) where
  toFun x := ({lean_array(row)} : Array (Fin {width}))[x.val]!
  invFun x := ({lean_array(inv)} : Array (Fin {width}))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

"""


def emit_module(module: str, prepared: dict, input_names: list[str]) -> str:
    action_id = prepared["action_id"]
    generators = prepared["generators"]
    table = prepared["table"]
    classes = prepared["classes"]
    n = len(table["rows"])
    d = len(generators)
    c = len(classes)
    require(2 <= n <= 46_080, "selected action order outside the narrow ceiling")
    require(1 <= d <= 16, "selected ambient generator width outside the narrow ceiling")
    require(1 <= c <= 128, "selected class count outside the narrow ceiling")

    next_expr = f"({lookup([lean_array(row) for row in table['next']])} : Array (Fin {n}))[j.val]!"
    prev_expr = f"({lookup([lean_array(row) for row in table['prev']])} : Array (Fin {n}))[j.val]!"
    action_rows = table["rows"]

    text = f"""import SymmetricSubgroupAsymptotics.BinaryNormalGeneratorChecks
import SymmetricSubgroupAsymptotics.FiniteCentralizerRowCoordinates
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Selected nonbinary degree-16 action {action_id}: checked conjugacy classes

Generated by `emit_lean_nonbinary_selected_class_pilot.py` from the explicit
selected inputs `{', '.join(input_names)}` and the pinned nonbinary source
digests `{ACTIONS_SHA256}` and `{NORMALS_SHA256}`.  The source JSON is not a
proof premise: the Cayley rows,
class invariant, centralizer membership, kernel chart and top-image chart are
all rechecked by Lean's kernel.  This module proves the complete conjugacy
cover for this one action.  Normal-subgroup coverage remains a separate
selected-witness dependency.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.{module}

"""
    for j, generator in enumerate(generators):
        text += permutation_def(f"generator{j}", generator, WIDTH)
    text += f"""def generators (j : Fin {d}) : Equiv.Perm (Fin {WIDTH}) :=
  {lookup([f'generator{j}' for j in range(d)], 'j.val')}

private def codes (i : Fin {n}) : Fin ({WIDTH}^{WIDTH}) :=
  {lookup(table['codes'])}

private def ranks (i : Fin {n}) : ℕ :=
  {lookup(table['rank'])}

private def parents (i : Fin {n}) : Fin {n} :=
  {lookup(table['parent'])}

private def letters (i : Fin {n}) : Fin {d} :=
  {lookup(table['letter'])}

private def nextRow (i : Fin {n}) (j : Fin {d}) : Fin {n} :=
  {next_expr}

private def prevRow (i : Fin {n}) (j : Fin {d}) : Fin {n} :=
  {prev_expr}

private theorem parent_lt_checked : ∀ i : Fin {n},
    i ≠ {table['identity']} → ranks (parents i) < ranks i := {finite_checks(n)}

private theorem parent_next_checked : ∀ i : Fin {n},
    i ≠ {table['identity']} → nextRow (parents i) (letters i) = i := {finite_checks(n)}

def certificate : EncodedCayleyCertificate
    (permutationGeneratorEncoding generators) {n} where
  rows := codes
  identity := {table['identity']}
  identity_eq := by decide +kernel
  next := nextRow
  next_eq := {finite_checks(n)}
  rank := ranks
  parent i _ := parents i
  letter i _ := letters i
  parent_lt := parent_lt_checked
  parent_next := parent_next_checked

private theorem codes_strict : StrictMono codes :=
  Fin.strictMono_iff_lt_succ.mpr {finite_checks(n - 1)}

theorem rows_injective : Function.Injective certificate.rows :=
  codes_strict.injective

theorem exact_card :
    Nat.card (Subgroup.closure (Set.range generators)) = {n} :=
  certificate.card_closure rows_injective

private theorem prev_checked : ∀ i j,
    certificate.next (prevRow i j) j = i := {finite_checks(n)}

@[reducible] def group : Group (FiniteGroupRow {n}) :=
  certificate.rowGroup rows_injective prevRow prev_checked

def originalEquiv : letI := group
    FiniteGroupRow {n} ≃* Subgroup.closure (Set.range generators) :=
  certificate.rowEquiv rows_injective prevRow prev_checked

abbrev Source := FiniteGroupRow {n}

local instance selectedSourceGroup : Group Source := group

def ambient (j : Fin {d}) : Source :=
  ⟨certificate.next certificate.identity j⟩

theorem ambient_full : Subgroup.closure (Set.range ambient) = ⊤ :=
  certificate.row_generators_full rows_injective prevRow prev_checked

theorem source_card : Nat.card Source = {n} := by
  rw [Nat.card_eq_fintype_card]
  rfl

"""
    for i, action_row in enumerate(action_rows):
        text += permutation_def(f"actionRow{i}", action_row, ACTION_WIDTH)
    text += f"""private def actionRows (i : Fin {n}) : Equiv.Perm (Fin {ACTION_WIDTH}) :=
  {lookup([f'actionRow{i}' for i in range(n)])}

/-- The original faithful degree-sixteen action of the literal row group. -/
def faithfulAction : Source →* Equiv.Perm (Fin {ACTION_WIDTH}) where
  toFun x := actionRows x.index
  map_one' := by decide +kernel
  map_mul' := by
    rintro ⟨i⟩ ⟨j⟩
    apply Equiv.ext
    intro p
    fin_cases i <;> fin_cases j <;> fin_cases p <;> decide +kernel

private def representativeRows (i : Fin {c}) : Fin {n} :=
  {lookup([row['representative_index'] for row in classes])}

def representative (i : Fin {c}) : Source := ⟨representativeRows i⟩

private def classCodeRows (i : Fin {n}) : Fin {c} :=
  {lookup(prepared['class_code'])}

private def classCode (x : Source) : Fin {c} := classCodeRows x.index

def classInvariant : FiniteConjugacyGeneratorInvariant ambient representative where
  Code := Fin {c}
  code := classCode
  generator_invariant := by
    intro i x
    rcases x with ⟨j⟩
    fin_cases i <;> fin_cases j <;> decide +kernel
  representative_injective := by decide +kernel

"""
    for index, row in enumerate(classes):
        k = len(row["kernel_indices"])
        t = len(row["top_indices"])
        card = row["centralizer_card"]
        text += f"""namespace C{index}

private def kernelRows (j : Fin {k}) : Fin {n} :=
  {lookup(row['kernel_indices'], 'j.val')}

private def topRows (j : Fin {t}) : Fin {n} :=
  {lookup(row['top_indices'], 'j.val')}

private theorem kernelCompleteChecked : ∀ i : Fin {n},
    (⟨i⟩ : Source) * representative {index} =
      representative {index} * (⟨i⟩ : Source) →
    faithfulAction (⟨i⟩ : Source) = 1 → ∃ j, kernelRows j = i := by
  native_decide

private theorem topCompleteChecked : ∀ i : Fin {n},
    (⟨i⟩ : Source) * representative {index} =
      representative {index} * (⟨i⟩ : Source) →
    ∃ j, faithfulAction (⟨i⟩ : Source) =
      faithfulAction (⟨topRows j⟩ : Source) := by
  native_decide

def coordinates : FiniteCentralizerRowCoordinates
    faithfulAction (representative {index}) {k} {t} where
  kernelRows := kernelRows
  kernel_centralizes := by
    intro j
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    fin_cases j <;> decide +kernel
  kernel_mem := by decide +kernel
  kernelRows_injective := by decide +kernel
  kernel_complete := by
    intro i hi htop
    exact kernelCompleteChecked i
      (Subgroup.mem_centralizer_singleton_iff.mp hi) htop
  topRows := topRows
  top_centralizes := by
    intro j
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    fin_cases j <;> decide +kernel
  topImages_injective := by decide +kernel
  top_complete := by
    intro i hi
    exact topCompleteChecked i
      (Subgroup.mem_centralizer_singleton_iff.mp hi)

noncomputable def centralizer :
    FinitePairCentralizerCoordinateCertificate
      (Subgroup.centralizer ({{representative {index}}} : Set Source)) {ACTION_WIDTH} :=
  coordinates.toCoordinateCertificate {card} (by norm_num)

end C{index}

"""
    claimed_values = [row["centralizer_card"] for row in classes]
    centralizer_chain = fin_cases_chain(
        [f"C{i}.centralizer" for i in range(c)])
    text += f"""noncomputable def centralizer : ∀ i : Fin {c},
    FinitePairCentralizerCoordinateCertificate
      (Subgroup.centralizer ({{representative i}} : Set Source)) {ACTION_WIDTH} :=
  {centralizer_chain}

private def claimedCardRows (i : Fin {c}) : ℕ :=
  {lookup(claimed_values)}

private theorem centralizer_claimedCard : ∀ i : Fin {c},
    (centralizer i).claimedCard = claimedCardRows i :=
  {fin_cases_chain(['(by rfl)' for _ in range(c)])}

private theorem claimed_class_sum :
    (∑ i : Fin {c}, Nat.card Source / (centralizer i).claimedCard) =
      Nat.card Source := by
  rw [source_card]
  simp_rw [centralizer_claimedCard]
  norm_num [claimedCardRows, Fin.sum_univ_succ]

/-- Kernel-checked complete conjugacy-class chunk for the selected action. -/
noncomputable def conjugacyChunk :
    FiniteConjugacyCentralizerCoordinateChunk representative {ACTION_WIDTH} :=
  finiteConjugacyCentralizerCoordinateChunk_ofInvariant
    ambient representative ambient_full classInvariant centralizer
      claimed_class_sum

/-- Complete class cover derived from the checked invariant and coordinate
charts, without a producer coverage assertion. -/
noncomputable def conjugacyCover :
    FiniteConjugacyCardinalCover representative :=
  conjugacyChunk.toCardinalCover

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
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    require(MODULE_RE.fullmatch(args.module) is not None, "invalid Lean module name")
    require(len(set(args.input)) == len(args.input), "duplicate selected input")
    chunks = [read_chunk(path) for path in args.input]
    prepared = validate_and_prepare(chunks, read_pinned_data())
    payload = emit_module(args.module, prepared,
                          [path.name for path in args.input]).encode()
    write_atomic(args.output, payload, args.force)
    print(f"{args.output}: {len(payload)} bytes; action {prepared['action_id']}; "
          f"order {len(prepared['table']['rows'])}; classes {len(prepared['classes'])}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, json.JSONDecodeError, Refused) as error:
        raise SystemExit(f"refused: {error}")
