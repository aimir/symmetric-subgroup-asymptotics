#!/usr/bin/env python3
"""Emit one kernel-checked Lean class chunk for one selected six-pair action.

Both the input JSON and output Lean path are mandatory.  The input must be a
single ``classes`` chunk produced from the pinned six-block dataset.  This
emitter has no directory scan, no action range and no bulk mode.  It never
invokes Lean, a subprocess or another exporter.

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
DATA = ROOT / "certificates/data/six_block.json.gz"
DATA_SHA256 = "446f54807b4f31114d559c9459fb529bd0eb83bbdd744e563a799521ddaa43d3"
WIDTH = 12
PAIR_COUNT = 6
ACTION_COUNT = 182
INPUT_LIMIT = 256 * 1024
COMPRESSED_DATA_LIMIT = 128 * 1024
DECOMPRESSED_DATA_LIMIT = 2 * 1024 * 1024
OUTPUT_LIMIT = 2 * 1024 * 1024
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


def pair_top(row: tuple[int, ...]) -> tuple[int, ...]:
    result = []
    for i in range(PAIR_COUNT):
        a, b = row[2 * i], row[2 * i + 1]
        require(a // 2 == b // 2, "row does not preserve the standard pairs")
        result.append(a // 2)
    require(sorted(result) == list(range(PAIR_COUNT)), "invalid pair-top row")
    return tuple(result)


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
    require(path.is_file() and not path.is_symlink(), "missing or redirected input JSON")
    raw = path.read_bytes()
    require(len(raw) <= INPUT_LIMIT, "input JSON ceiling reached")
    value = json.loads(raw)
    require(isinstance(value, dict), "input JSON is not an object")
    require(value.get("schema_version") == 1, "unexpected selected-chunk schema")
    require(value.get("source_sha256") == DATA_SHA256, "selected source digest changed")
    require(value.get("stage") == "classes", "emitter accepts one classes chunk only")
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


def validate_and_prepare(chunk: dict, data: dict) -> dict:
    action_number = chunk.get("action")
    require(type(action_number) is int and 1 <= action_number <= ACTION_COUNT,
            "selected action number out of range")
    action = data["actions"][action_number - 1]
    generators = [permutation(row) for row in action["generators"]]
    require(chunk.get("ambient_generator_count") == len(generators),
            "ambient generator count mismatch")
    table = positive_table(generators)
    require(chunk.get("action_order") == len(table["rows"]) == action["order"],
            "action order mismatch")

    content = chunk.get("content")
    require(isinstance(content, dict), "missing class content")
    selected_rows = content.get("rows")
    require(isinstance(selected_rows, list) and selected_rows,
            "empty selected class rows")
    all_representatives = [permutation(row) for row in action["class_representatives"]]
    require(chunk.get("range") == [1, len(all_representatives)],
            "pilot emitter requires one full selected class chunk")
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

        kernel_words = record.get("kernel_chart")
        top_records = record.get("top_chart")
        require(isinstance(kernel_words, list) and kernel_words,
                "empty centralizer kernel chart")
        require(isinstance(top_records, list) and top_records,
                "empty centralizer top chart")
        kernel_rows = [evaluate_word(word, generators) for word in kernel_words]
        top_rows = []
        stated_tops = []
        for top_record in top_records:
            require(isinstance(top_record, dict) and set(top_record) == {"top", "preimage"},
                    "invalid top-chart record")
            row = evaluate_word(top_record["preimage"], generators)
            stated = permutation(top_record["top"], PAIR_COUNT)
            require(pair_top(row) == stated, "top-chart preimage mismatch")
            top_rows.append(row)
            stated_tops.append(stated)
        actual_kernel = {g for g in centralizer if pair_top(g) == tuple(range(PAIR_COUNT))}
        actual_top = {pair_top(g) for g in centralizer}
        require(set(kernel_rows) == actual_kernel and len(kernel_rows) == len(actual_kernel),
                "kernel chart is not reversible")
        require(set(stated_tops) == actual_top and len(stated_tops) == len(actual_top),
                "top chart is not reversible")
        require(all(row in centralizer for row in top_rows),
                "top-chart preimage escaped centralizer")
        require(len(kernel_rows) * len(top_rows) == len(centralizer),
                "centralizer coordinate product mismatch")
        prepared_rows.append({
            "representative_index": table["position"][representative],
            "kernel_indices": [table["position"][row] for row in kernel_rows],
            "top_indices": [table["position"][row] for row in top_rows],
            "centralizer_card": len(centralizer),
        })

    require(class_card_sum == len(table["rows"]) == content.get("class_card_sum"),
            "selected classes do not exhaust action")
    require(set(row_class) == set(table["rows"]), "class code is incomplete")
    return {
        "action_number": action_number,
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


def emit_module(module: str, prepared: dict, input_name: str) -> str:
    action_number = prepared["action_number"]
    generators = prepared["generators"]
    table = prepared["table"]
    classes = prepared["classes"]
    n = len(table["rows"])
    d = len(generators)
    c = len(classes)
    require(n == 12 and c == 6, "current pilot module is the order-twelve six-class slice")

    next_expr = f"({lookup([lean_array(row) for row in table['next']])} : Array (Fin {n}))[j.val]!"
    prev_expr = f"({lookup([lean_array(row) for row in table['prev']])} : Array (Fin {n}))[j.val]!"
    top_rows = [pair_top(row) for row in table["rows"]]

    text = f"""import SymmetricSubgroupAsymptotics.BinaryNormalGeneratorChecks
import SymmetricSubgroupAsymptotics.FiniteCentralizerRowCoordinates
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action {action_number}: checked conjugacy-class pilot

Generated by `emit_lean_six_pair_selected_class_pilot.py` from the explicit
selected input `{input_name}` and the pinned six-block source digest
`{DATA_SHA256}`.  The source JSON is not a proof premise: the Cayley rows,
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
    for i, top_row in enumerate(top_rows):
        text += permutation_def(f"topRow{i}", top_row, PAIR_COUNT)
    text += f"""private def topRows (i : Fin {n}) : Equiv.Perm (Fin {PAIR_COUNT}) :=
  {lookup([f'topRow{i}' for i in range(n)])}

/-- The executable six-block action of the literal row group. -/
def pairTop : Source →* Equiv.Perm (Fin {PAIR_COUNT}) where
  toFun x := topRows x.index
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
    pairTop (⟨i⟩ : Source) = 1 → ∃ j, kernelRows j = i := by
  native_decide

private theorem topCompleteChecked : ∀ i : Fin {n},
    (⟨i⟩ : Source) * representative {index} =
      representative {index} * (⟨i⟩ : Source) →
    ∃ j, pairTop (⟨i⟩ : Source) = pairTop (⟨topRows j⟩ : Source) := by
  native_decide

def coordinates : FiniteCentralizerRowCoordinates
    pairTop (representative {index}) {k} {t} where
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
      (Subgroup.centralizer ({{representative {index}}} : Set Source)) {PAIR_COUNT} :=
  coordinates.toCoordinateCertificate {card} (by norm_num)

end C{index}

"""
    claimed_values = [row["centralizer_card"] for row in classes]
    centralizer_chain = fin_cases_chain(
        [f"C{i}.centralizer" for i in range(c)])
    text += f"""noncomputable def centralizer : ∀ i : Fin {c},
    FinitePairCentralizerCoordinateCertificate
      (Subgroup.centralizer ({{representative i}} : Set Source)) {PAIR_COUNT} :=
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
    FiniteConjugacyCentralizerCoordinateChunk representative {PAIR_COUNT} :=
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
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--module", required=True)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    require(MODULE_RE.fullmatch(args.module) is not None, "invalid Lean module name")
    chunk = read_chunk(args.input)
    prepared = validate_and_prepare(chunk, read_pinned_data())
    payload = emit_module(args.module, prepared, args.input.name).encode()
    write_atomic(args.output, payload, args.force)
    print(f"{args.output}: {len(payload)} bytes; action {prepared['action_number']}; "
          f"order {len(prepared['table']['rows'])}; classes {len(prepared['classes'])}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, json.JSONDecodeError, Refused) as error:
        raise SystemExit(f"refused: {error}")
