#!/usr/bin/env python3
"""Emit ONE bounded prime-index composition witness for an original action.

The required --degree and --index select the first matching primitive action
row in the committed primitive_rank.jsonl.gz stream. Only that candidate row
is JSON-decoded; no catalogue/menu is loaded and no coverage claim is made.
The literal source tuple and the entire recorded composition chain survive.

All computations are certificate production, not proof: Lean checks original
permutation images, word membership, sparse right-generator transitions,
strictly ordered row codes, inclusion/conjugation words, prime cardinality
ratios, and both endpoints. No JSON order, rank, simplicity or primitivity
assertion is used as a theorem premise. Non-prime edges are rejected; this
producer does not certify nonsoluble composition factors.

There is no default selection, batch option, compiler subprocess, quotient
multiplication table, or unbounded search. --check recomputes the same bounded
selected witness and compares bytes without writing. Kernel checks belong to
the primary agent's separate serial scripts/check_lean.py queue.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import gzip
import hashlib
import json
import math
import os
from pathlib import Path
import re
import sys
import tempfile
import time
from typing import Any, Callable

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "certificates/data/primitive_rank.jsonl.gz"
OUT = ROOT / "formal/SymmetricSubgroupAsymptotics/GeneratedPrimeComposition"

# CLI limits remain finite and at most these absolute producer ceilings.
# Defaults accommodate small 3P2 and 9P6 pilots; do not bulk this tool.
LIMIT_SPECS = {
    "compressed_bytes": (8 * 1024**2, 16 * 1024**2),
    "decompressed_bytes": (16 * 1024**2, 64 * 1024**2),
    "line_bytes": (2 * 1024**2, 4 * 1024**2),
    "lines": (12000, 100000),
    "degree": (32, 64),
    "order": (512, 4096),
    "levels": (16, 32),
    "generators": (16, 32),
    "total_rows": (4096, 20000),
    "operations": (50000, 500000),
    "word_length": (128, 512),
    "word_letters": (200000, 2000000),
    "output_bytes": (4 * 1024**2, 16 * 1024**2),
}

Perm = tuple[int, ...]
Word = tuple[int, ...]


class CertificateError(ValueError):
    """A bounded selected row cannot supply the stated literal certificate."""


def require(condition: bool, explanation: str) -> None:
    if not condition:
        raise CertificateError(explanation)


@dataclass
class Budget:
    limits: dict[str, int]
    seconds: float
    started: float
    rows: int = 0
    operations: int = 0
    word_letters: int = 0
    max_word_length: int = 0

    def time_check(self) -> None:
        require(time.monotonic() - self.started <= self.seconds,
                f"selected production exceeded {self.seconds:g}s wall budget")

    def operation(self, count: int = 1) -> None:
        self.operations += count
        require(self.operations <= self.limits["operations"],
                "sparse transition/word lookup operation limit reached")
        self.time_check()

    def row(self) -> None:
        self.rows += 1
        require(self.rows <= self.limits["total_rows"],
                "cumulative source/chain row limit reached")
        self.time_check()

    def word(self, word: Word) -> Word:
        require(len(word) <= self.limits["word_length"],
                "positive generator word-length limit reached")
        self.word_letters += len(word)
        self.max_word_length = max(self.max_word_length, len(word))
        require(self.word_letters <= self.limits["word_letters"],
                "cumulative stored/emitted word-letter limit reached")
        self.time_check()
        return word


def bounded_file_hash(path: Path, budget: Budget) -> str:
    cap = budget.limits["compressed_bytes"]
    require(path.stat().st_size <= cap, "compressed committed dataset exceeds byte limit")
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as stream:
        while chunk := stream.read(65536):
            size += len(chunk)
            require(size <= cap, "compressed dataset grew beyond byte limit")
            digest.update(chunk)
            budget.time_check()
    return digest.hexdigest()


def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON object key: {key}")
        result[key] = value
    return result


@dataclass
class SelectedRow:
    degree: int
    index: int
    line: int
    line_sha256: str
    data_sha256: str
    decompressed_bytes: int
    value: dict[str, Any]


def read_selected(degree: int, index: int, budget: Budget,
                  expected_sha256: str | None) -> SelectedRow:
    data_hash = bounded_file_hash(DATA, budget)
    # Avoid JSON materialization of unrelated normal lists. Check the selected
    # candidate's TOP-LEVEL locator after parsing, not just its text matches.
    needles = (
        re.compile(rb'"catalogue"\s*:\s*"primitive"'),
        re.compile(rb'"degree"\s*:\s*' + str(degree).encode() + rb'\s*[,}]'),
        re.compile(rb'"index"\s*:\s*' + str(index).encode() + rb'\s*[,}]'),
    )
    used = 0
    with gzip.open(DATA, "rb") as stream:
        for line_number in range(1, budget.limits["lines"] + 1):
            remaining = budget.limits["decompressed_bytes"] - used
            require(remaining > 0, "decompressed stream byte limit reached before selection")
            raw = stream.readline(min(budget.limits["line_bytes"], remaining) + 1)
            if not raw:
                break
            used += len(raw)
            require(used <= budget.limits["decompressed_bytes"],
                    "decompressed stream byte limit reached before selection")
            require(len(raw) <= budget.limits["line_bytes"],
                    "single JSONL record exceeds bounded line size")
            budget.time_check()
            if not all(needle.search(raw) for needle in needles):
                continue
            row = json.loads(raw, object_pairs_hook=unique_object)
            if (not isinstance(row, dict) or row.get("kind") != "action"
                    or row.get("catalogue") != "primitive"
                    or type(row.get("degree")) is not int
                    or type(row.get("index")) is not int
                    or row["degree"] != degree or row["index"] != index):
                continue
            line_hash = hashlib.sha256(raw).hexdigest()
            require(expected_sha256 is None or line_hash == expected_sha256,
                    "selected raw JSONL line does not match --expect-row-sha256")
            return SelectedRow(degree, index, line_number, line_hash, data_hash, used, row)
    raise CertificateError("selected primitive locator absent within bounded stream; "
                           "no completeness or missing-catalogue conclusion follows")


def permutations(value: Any, degree: int, name: str, budget: Budget) -> list[Perm]:
    require(isinstance(value, list) and 1 <= len(value) <= budget.limits["generators"],
            f"{name}: expected nonempty bounded literal generator list")
    result = []
    for images in value:
        require(isinstance(images, list) and len(images) == degree,
                f"{name}: permutation has wrong degree")
        require(all(type(x) is int for x in images)
                and sorted(images) == list(range(1, degree + 1)),
                f"{name}: expected a permutation in one-based image notation")
        result.append(tuple(x - 1 for x in images))
    return result


def compose(left: Perm, right: Perm) -> Perm:
    """Lean's actual product: (left * right)(x) = left(right(x))."""
    return tuple(left[x] for x in right)


def inverse(value: Perm) -> Perm:
    result = [0] * len(value)
    for i, x in enumerate(value):
        result[x] = i
    return tuple(result)


def permutation_code(value: Perm) -> int:
    degree = len(value)
    return sum(x * degree**i for i, x in enumerate(value))


@dataclass
class SparseTable:
    generators: list[Perm]
    rows: list[Perm]
    words: list[Word]
    indices: dict[Perm, int]
    transitions: list[list[int]]
    identity: int
    ranks: list[int]
    parents: list[int]
    letters: list[int]


def sparse_table(generators: list[Perm], degree: int, name: str,
                 budget: Budget) -> SparseTable:
    """Positive-word BFS with ONLY right-generator edges, under explicit caps."""
    identity = tuple(range(degree))
    rows = [identity]
    words: list[Word] = [budget.word(())]
    indices = {identity: 0}
    transitions: list[list[int]] = []
    parents, letters = [0], [0]
    budget.row()
    for i, current in enumerate(rows):
        edges = []
        for letter, generator in enumerate(generators):
            budget.operation()
            product = compose(current, generator)
            if product not in indices:
                require(len(rows) < budget.limits["order"],
                        f"{name}: actual closure exceeds per-group order cap; no output written")
                word = budget.word(words[i] + (letter,))
                budget.row()
                indices[product] = len(rows)
                rows.append(product)
                words.append(word)
                parents.append(i)
                letters.append(letter)
            edges.append(indices[product])
        transitions.append(edges)
    # Strict image-code ordering proves injectivity with O(rows) adjacent
    # comparisons, without an O(rows^2) pairwise equality table.
    order = sorted(range(len(rows)), key=lambda i: permutation_code(rows[i]))
    remap = {old: new for new, old in enumerate(order)}
    sorted_rows = [rows[i] for i in order]
    return SparseTable(generators, sorted_rows, [words[i] for i in order],
                       {p: i for i, p in enumerate(sorted_rows)},
                       [[remap[j] for j in transitions[i]] for i in order],
                       remap[0], order, [remap[parents[i]] for i in order],
                       [letters[i] for i in order])


def word_for(table: SparseTable, value: Perm, name: str, budget: Budget) -> Word:
    budget.operation()
    require(value in table.indices, f"{name}: actual generator/conjugate is outside required closure")
    return budget.word(table.words[table.indices[value]])


def prime(value: int) -> bool:
    return value >= 2 and all(value % d for d in range(2, math.isqrt(value) + 1))


@dataclass
class Witness:
    selected: SelectedRow
    source: list[Perm]
    chain: list[list[Perm]]  # Ascending, exactly reversed from committed row.
    source_words: list[list[Word]]
    tables: list[SparseTable]
    inclusions: list[list[Word]]
    conjugates: list[list[Word]]  # Upper-generator first, lower second.
    original_in_top: list[Word]
    edges: list[int]


def prepare(selected: SelectedRow, budget: Budget) -> Witness:
    n = selected.degree
    source = permutations(selected.value.get("generators"), n, "original source", budget)
    recorded = selected.value.get("composition")
    require(isinstance(recorded, list) and 1 <= len(recorded) <= budget.limits["levels"],
            "selected primitive row has no bounded literal composition chain")
    # Never deduplicate/reorder tuples or replace the recorded top generators.
    chain = [permutations(level, n, f"ascending chain level {i}", budget)
             for i, level in enumerate(reversed(recorded))]
    source_table = sparse_table(source, n, "original source", budget)
    source_words = [[word_for(source_table, g, f"chain level {i} original membership", budget)
                     for g in generators] for i, generators in enumerate(chain)]
    tables = [sparse_table(generators, n, f"chain level {i}", budget)
              for i, generators in enumerate(chain)]
    require(len(tables[0].rows) == 1, "recorded chain bottom is not the actual trivial subgroup")
    original_in_top = [word_for(tables[-1], g, "original source in recorded top", budget)
                       for g in source]
    edges = []
    inclusions = []
    conjugates = []
    for i, (lower, upper) in enumerate(zip(tables, tables[1:])):
        inclusions.append([word_for(upper, g, f"edge {i} inclusion", budget)
                           for g in lower.generators])
        lower_order, upper_order = len(lower.rows), len(upper.rows)
        require(upper_order % lower_order == 0,
                f"edge {i}: actual adjacent cardinalities do not have an integer ratio")
        ratio = upper_order // lower_order
        require(prime(ratio), f"edge {i}: actual ratio {ratio} is not prime; "
                "nonsoluble/simple-nonprime or repeated edges are unsupported")
        edges.append(ratio)
        checked = []
        for upper_generator in upper.generators:
            upper_inverse = inverse(upper_generator)
            for lower_generator in lower.generators:
                budget.operation(2)
                conjugate = compose(compose(upper_generator, lower_generator), upper_inverse)
                checked.append(word_for(lower, conjugate, f"edge {i} normal conjugate", budget))
        conjugates.append(checked)
    # JSON order/ranks/normals/primitive/socle metadata deliberately unused.
    return Witness(selected, source, chain, source_words, tables,
                   inclusions, conjugates, original_in_top, edges)


def array(values: list[Any]) -> str:
    return "#[" + ", ".join(map(str, values)) + "]"


def word_literal(word: Word) -> str:
    return "[" + ", ".join(map(str, word)) + "]"


def word_array(words: list[Word]) -> str:
    return array([word_literal(word) for word in words])


def image_matrix(generators: list[Perm]) -> str:
    return array([array([x + 1 for x in generator]) for generator in generators])


def finite_cases(branches: list[str]) -> str:
    """Dependent elimination into Type is intentional: never tactic fin_cases."""
    tail = "(fun i => Fin.elim0 i)"
    for branch in reversed(branches):
        tail = f"(Fin.cases {branch} {tail})"
    return tail


class LeanText:
    def __init__(self, budget: Budget):
        self.budget = budget
        self.parts: list[str] = []
        self.size = 0

    def add(self, text: str) -> None:
        self.size += len(text.encode("utf-8"))
        require(self.size <= self.budget.limits["output_bytes"],
                "generated Lean output exceeds byte budget; no output written")
        self.budget.time_check()
        self.parts.append(text)

    def finish(self) -> bytes:
        return "".join(self.parts).encode("utf-8")


def named_finite_check(text: LeanText, name: str, size: int,
                       proposition: Callable[[str], str]) -> None:
    """Separate declarations reset proof budgets; leaves contain at most8 rows.

    Embeddings are exactly the casts used by Fin.addCases, so assembly uses
    the named lemmas without recomputing a finite decision or modular cast.
    Array data and every added declaration count toward the output-byte cap;
    parent/rank/letter array sizes are bounded by cumulative row caps.
    """
    serial = 0

    def branch(amount: int, embed: Callable[[str], str]) -> str:
        nonlocal serial
        if amount <= 8:
            leaf = f"{name}_chunk{serial:03d}"
            serial += 1
            text.add(f"private theorem {leaf} : ∀ i : Fin {amount},\n"
                     f"    {proposition(embed('i'))} := by\n  decide +kernel\n\n")
            return leaf
        left = amount // 2
        right = amount - left
        lhs = branch(left, lambda i: embed(f"(Fin.castAdd {right} {i})"))
        rhs = branch(right, lambda i: embed(f"(Fin.natAdd {left} {i})"))
        return f"(Fin.addCases (m := {left}) (n := {right}) {lhs} {rhs})"

    assembled = branch(size, lambda i: i)
    text.add(f"private theorem {name} : ∀ i : Fin {size},\n"
             f"    {proposition('i')} :=\n  {assembled}\n\n")


def emit(witness: Witness, budget: Budget) -> tuple[Path, bytes]:
    selected = witness.selected
    n, index = selected.degree, selected.index
    label = f"Primitive{n}P{index}"
    namespace = f"SymmetricSubgroupAsymptotics.GeneratedPrimeComposition.{label}"
    d = len(witness.source)
    levels = len(witness.chain)
    length = levels - 1
    text = LeanText(budget)
    text.add(f'''import SymmetricSubgroupAsymptotics.FiniteGeneratorCompositionWitness
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Fin.Basic

/-! Selected literal original-action prime-index composition certificate.
Generated deterministically by computations/python/export_lean_prime_composition.py.
Locator only: primitive degree {n}, index {index}; JSONL line {selected.line}.
Committed gzip SHA256: {selected.data_sha256}
Raw selected line SHA256, including newline: {selected.line_sha256}

The original source generator order and every recorded chain tuple are
preserved. The descending JSON chain is reversed exactly once. All words
use Lean's permutation product, not unverified GAP word conventions.
Sparse numeric transitions and decreasing BFS parents construct actual
row words via the checked reflection theorem. Original-source membership
of each literal chain generator is checked once, not re-expanded per edge.
Row transitions, parents and code ordering use separately named
at-most-eight-row kernel lemmas.
JSON order/rank/normality/simplicity/primitive labels are not assumptions.
This source proves a bound for this literal subgroup and every chosen
actual chief series. It does not prove catalogue recognition/completeness,
primitivity, normal-rank values, or a global asymptotic theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace {namespace}

''')
    for j, generator in enumerate(witness.source):
        text.add(f'''private def sourcePerm{j} : Equiv.Perm (Fin {n}) where
  toFun x := ({array(list(generator))} : Array (Fin {n}))[x.val]!
  invFun x := ({array(list(inverse(generator)))} : Array (Fin {n}))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

''')
    text.add(f'''/-- The literal committed source tuple, with its original order. -/
def sourceGenerators (j : Fin {d}) : Equiv.Perm (Fin {n}) :=
  ({array([f'sourcePerm{j}' for j in range(d)])} : Array (Equiv.Perm (Fin {n})))[j.val]!

abbrev Original := Subgroup.closure (Set.range sourceGenerators)
private instance originalInhabited : Inhabited Original := ⟨1⟩

def originalGenerators (j : Fin {d}) : Original :=
  ⟨sourceGenerators j, Subgroup.subset_closure (Set.mem_range_self j)⟩

theorem originalGenerators_full : Subgroup.closure (Set.range originalGenerators) = ⊤ :=
  binaryNormal_full_generators_of_equiv sourceGenerators originalGenerators
    (MulEquiv.refl _) (fun _ => rfl)

private def originalWord (w : List (Fin {d})) : Original :=
  (w.map originalGenerators).prod

private def originalEncoding {{ι : Type}} (generators : ι → Original) :
    GeneratorEncoding generators (Fin ({n}^{n})) where
  encode g := permutationCode (g : Equiv.Perm (Fin {n}))
  injective := fun _ _ h => Subtype.ext ((permutationCode_injective {n}) h)
  one := permutationCode (1 : Equiv.Perm (Fin {n}))
  encode_one := rfl
  step := (permutationGeneratorEncoding
    (fun j => (generators j : Equiv.Perm (Fin {n})))).step
  encode_step g j := (permutationGeneratorEncoding
    (fun j => (generators j : Equiv.Perm (Fin {n})))).encode_step
      (g : Equiv.Perm (Fin {n})) j

''')
    for i, (generators, source_words, table) in enumerate(zip(
            witness.chain, witness.source_words, witness.tables)):
        k, order = len(generators), len(table.rows)
        for j, generator in enumerate(generators):
            text.add(f'''private def level{i}Perm{j} : Equiv.Perm (Fin {n}) where
  toFun x := ({array(list(generator))} : Array (Fin {n}))[x.val]!
  invFun x := ({array(list(inverse(generator)))} : Array (Fin {n}))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

''')
        codes_expr = array([permutation_code(row) for row in table.rows])
        next_expr = array([array(row) for row in table.transitions])
        text.add(f'''private def level{i}LiteralGenerators (j : Fin {k}) : Equiv.Perm (Fin {n}) :=
  ({array([f'level{i}Perm{j}' for j in range(k)])} :
    Array (Equiv.Perm (Fin {n})))[j.val]!

private def level{i}SourceWords (j : Fin {k}) : List (Fin {d}) :=
  ({word_array(source_words)} : Array (List (Fin {d})))[j.val]!

private theorem level{i}_source_words_eq : ∀ j : Fin {k},
    (originalWord (level{i}SourceWords j) : Equiv.Perm (Fin {n})) =
      level{i}LiteralGenerators j := by
  decide +kernel

/-- The value is the literal recorded permutation; its original source
membership is bound once by the checked word theorem above. -/
private def level{i}Generators (j : Fin {k}) : Original :=
  ⟨level{i}LiteralGenerators j, by
    rw [← level{i}_source_words_eq j]
    exact (originalWord (level{i}SourceWords j)).property⟩

private def level{i}Codes (i : Fin {order}) : Fin ({n}^{n}) :=
  ({codes_expr} : Array (Fin ({n}^{n})))[i.val]!

private def level{i}Next (i : Fin {order}) (j : Fin {k}) : Fin {order} :=
  (({next_expr} : Array (Array (Fin {order})))[i.val]!)[j.val]!

private def level{i}Ranks (i : Fin {order}) : ℕ :=
  ({array(table.ranks)} : Array ℕ)[i.val]!

private def level{i}Parents (i : Fin {order}) : Fin {order} :=
  ({array(table.parents)} : Array (Fin {order}))[i.val]!

private def level{i}Letters (i : Fin {order}) : Fin {k} :=
  ({array(table.letters)} : Array (Fin {k}))[i.val]!

''')
        named_finite_check(text, f"level{i}_next_checked", order,
                           lambda x: f"∀ j : Fin {k}, level{i}Codes (level{i}Next {x} j) =\n"
                           f"      (originalEncoding level{i}Generators).step (level{i}Codes {x}) j")
        named_finite_check(text, f"level{i}_parent_lt_checked", order,
                           lambda x: f"{x} ≠ ({table.identity} : Fin {order}) →\n"
                           f"      level{i}Ranks (level{i}Parents {x}) < level{i}Ranks {x}")
        named_finite_check(text, f"level{i}_parent_next_checked", order,
                           lambda x: f"{x} ≠ ({table.identity} : Fin {order}) →\n"
                           f"      level{i}Next (level{i}Parents {x}) (level{i}Letters {x}) = {x}")
        named_finite_check(text, f"level{i}_codes_adjacent", order - 1,
                           lambda x: f"level{i}Codes ({x}).castSucc < level{i}Codes ({x}).succ")
        text.add(f'''private def level{i}Encoded :
    EncodedCayleyCertificate (originalEncoding level{i}Generators) {order} where
  rows := level{i}Codes
  identity := {table.identity}
  identity_eq := by decide +kernel
  next := level{i}Next
  next_eq := level{i}_next_checked
  rank := level{i}Ranks
  parent i _ := level{i}Parents i
  letter i _ := level{i}Letters i
  parent_lt := level{i}_parent_lt_checked
  parent_next := level{i}_parent_next_checked

/-- Reflection constructs certified words and the same literal Cayley
certificate. No finite check recomputes products along every row word. -/
private def level{i}Cayley : FiniteCayleyCertificate level{i}Generators {order} :=
  level{i}Encoded.toCayley

private theorem level{i}_codes_strict : StrictMono level{i}Codes :=
  Fin.strictMono_iff_lt_succ.mpr level{i}_codes_adjacent

private theorem level{i}_rows_injective : Function.Injective level{i}Cayley.elements := by
  intro i j h
  apply level{i}_codes_strict.injective
  calc
    level{i}Codes i = (originalEncoding level{i}Generators).encode
        (level{i}Cayley.elements i) := (level{i}Encoded.encode_elements i).symm
    _ = (originalEncoding level{i}Generators).encode (level{i}Cayley.elements j) :=
      congrArg (originalEncoding level{i}Generators).encode h
    _ = level{i}Codes j := level{i}Encoded.encode_elements j

''')
    for i, (inclusions, conjugates) in enumerate(zip(witness.inclusions, witness.conjugates)):
        lower, upper = len(witness.chain[i]), len(witness.chain[i+1])
        text.add(f'''private def inclusion{i} : BinaryNormalGeneratorWords
    level{i}Generators level{i+1}Generators where
  words j := ({word_array(inclusions)} : Array (List (Fin {upper})))[j.val]!
  equations := by decide +kernel

private def conjugates{i} : BinaryNormalGeneratorWords
    (fun jk : Fin {upper} × Fin {lower} => level{i+1}Generators jk.1 *
      level{i}Generators jk.2 * (level{i+1}Generators jk.1)⁻¹) level{i}Generators where
  words jk := ({word_array(conjugates)} : Array (List (Fin {lower})))[jk.1.val * {lower} + jk.2.val]!
  equations := by decide +kernel

''')
    top = levels - 1
    text.add(f'''private def originalInTop : BinaryNormalGeneratorWords
    originalGenerators level{top}Generators where
  words j := ({word_array(witness.original_in_top)} :
    Array (List (Fin {len(witness.chain[-1])})))[j.val]!
  equations := by decide +kernel

private theorem level0_generators_eq_one : ∀ j, level0Generators j = 1 := by
  decide +kernel

private theorem bottom_eq : Subgroup.closure (Set.range level0Generators) = ⊥ := by
  apply le_antisymm _ bot_le
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  rw [level0_generators_eq_one]
  exact Subgroup.one_mem _

private theorem top_eq : Subgroup.closure (Set.range level{top}Generators) = ⊤ := by
  apply top_unique
  rw [← originalGenerators_full]
  exact originalInTop.closure_le

private def generatorCount : Fin {levels} → ℕ :=
  {finite_cases([str(len(g)) for g in witness.chain])}

def levelGenerators : (i : Fin {levels}) → Fin (generatorCount i) → Original :=
  {finite_cases([f'level{i}Generators' for i in range(levels)])}

private def rowCount : Fin {levels} → ℕ :=
  {finite_cases([str(len(t.rows)) for t in witness.tables])}

private def levelCayley : ∀ i : Fin {levels},
    FiniteCayleyCertificate (levelGenerators i) (rowCount i) :=
  {finite_cases([f'level{i}Cayley' for i in range(levels)])}

/-- Every field is evidence in the original literal permutation subgroup. -/
def certificate : SparsePrimeCompositionCertificate Original where
  length := {length}
  generatorCount := generatorCount
  generators := levelGenerators
  rowCount := rowCount
  cayley := levelCayley
  rows_injective :=
    {finite_cases([f'level{i}_rows_injective' for i in range(levels)])}
  inclusionWords :=
    {finite_cases([f'inclusion{i}' for i in range(length)])}
  conjugateWords :=
    {finite_cases([f'conjugates{i}' for i in range(length)])}
  edgeOrder := {finite_cases([str(q) for q in witness.edges])}
  edgePrime := by decide +kernel
  cardRatio := by decide +kernel
  head := bottom_eq
  last := top_eq

/-- Exact one-based image lists bind the original source tuple. -/
theorem sourceGenerator_images : ∀ j : Fin {d}, ∀ x : Fin {n},
    (sourceGenerators j x).val + 1 =
      (({image_matrix(witness.source)} : Array (Array ℕ))[j.val]!)[x.val]! := by
  decide +kernel

/-- Exact ascending image lists bind every recorded composition tuple. -/
theorem compositionGenerator_images : ∀ i : Fin {levels},
    ∀ j : Fin (generatorCount i), ∀ x : Fin {n},
    ((levelGenerators i j : Equiv.Perm (Fin {n})) x).val + 1 =
      ((({array([image_matrix(g) for g in witness.chain])} :
        Array (Array (Array ℕ)))[i.val]!)[j.val]!)[x.val]! :=
  {finite_cases(['(by decide +kernel)' for _ in range(levels)])}

theorem original_card : Nat.card Original = {len(witness.tables[-1].rows)} := by
  have h := certificate.subgroup_card (Fin.last {length})
  change Nat.card (Subgroup.closure (Set.range level{top}Generators)) =
    {len(witness.tables[-1].rows)} at h
  rw [top_eq, Subgroup.card_top] at h
  exact h

theorem ternaryCount_eq : certificate.ternaryCount = {witness.edges.count(3)} := by
  decide +kernel

theorem chosen_chief_weight_le (c : ActualChiefSeries Original) :
    actualChiefSeriesTernaryWeight c ≤ {witness.edges.count(3)} := by
  simpa only [ternaryCount_eq] using certificate.chiefWeight_le c

theorem exists_chief_weight_le :
    ∃ c : ActualChiefSeries Original,
      actualChiefSeriesTernaryWeight c ≤ {witness.edges.count(3)} := by
  simpa only [ternaryCount_eq] using certificate.exists_chiefSeries_le

''')
    if witness.edges.count(3) <= n // 3:
        text.add(f'''/-- Numeric consequence of the checked actual factor count only. -/
theorem chosen_chief_weight_le_degree_third (c : ActualChiefSeries Original) :
    actualChiefSeriesTernaryWeight c ≤ Nat.card (Fin {n}) / 3 := by
  simpa only [Nat.card_fin] using (chosen_chief_weight_le c).trans
    (by decide +kernel : {witness.edges.count(3)} ≤ {n} / 3)

''')
    text.add(f"end {namespace}\n")
    return OUT / f"{label}.lean", text.finish()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, required=True)
    parser.add_argument("--index", type=int, required=True)
    parser.add_argument("--expect-row-sha256", help="Optional exact raw JSONL line hash pin.")
    parser.add_argument("--check", action="store_true", help="Compare bytes; do not write/create paths.")
    parser.add_argument("--max-seconds", type=float, default=60.0,
                        help="Producer wall budget, positive and at most 300 seconds.")
    for name, (default, ceiling) in LIMIT_SPECS.items():
        parser.add_argument("--max-" + name.replace("_", "-"), type=int, default=default,
                            help=f"Finite cap (default {default}, absolute ceiling {ceiling}).")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    limits = {name: getattr(args, "max_" + name) for name in LIMIT_SPECS}
    for name, value in limits.items():
        require(1 <= value <= LIMIT_SPECS[name][1], f"invalid --max-{name.replace('_', '-')} cap")
    require(math.isfinite(args.max_seconds) and 0 < args.max_seconds <= 300,
            "--max-seconds must be finite, positive and at most 300")
    require(1 <= args.degree <= limits["degree"], "selected degree is outside the bounded degree cap")
    require(1 <= args.index <= 1000000, "selected catalogue index is out of range")
    if args.expect_row_sha256 is not None:
        require(re.fullmatch(r"[0-9a-f]{64}", args.expect_row_sha256) is not None,
                "--expect-row-sha256 must be a lowercase SHA256 digest")
    budget = Budget(limits, args.max_seconds, time.monotonic())
    selected = read_selected(args.degree, args.index, budget, args.expect_row_sha256)
    witness = prepare(selected, budget)
    path, content = emit(witness, budget)
    require(bounded_file_hash(DATA, budget) == selected.data_sha256,
            "committed input changed during selected production; no output written")
    budget.time_check()
    if args.check:
        require(path.is_file() and path.stat().st_size == len(content)
                and path.read_bytes() == content, f"generated selected witness is missing/stale: {path}")
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        same = (path.is_file() and path.stat().st_size == len(content)
                and path.read_bytes() == content)
        if not same:
            temporary_path: Path | None = None
            try:
                with tempfile.NamedTemporaryFile(dir=path.parent, prefix=path.name + ".",
                                                 suffix=".tmp", delete=False) as stream:
                    temporary_path = Path(stream.name)
                    stream.write(content)
                os.replace(temporary_path, path)
            finally:
                if temporary_path is not None and temporary_path.exists():
                    temporary_path.unlink()
    print(json.dumps({"path": str(path.relative_to(ROOT)), "checked": args.check,
                      "source_sha256": hashlib.sha256(content).hexdigest(),
                      "selected_line": selected.line, "row_sha256": selected.line_sha256,
                      "decompressed_bytes": selected.decompressed_bytes,
                      "chain_orders": [len(t.rows) for t in witness.tables],
                      "prime_edges": witness.edges, "ternary_count": witness.edges.count(3),
                      "cumulative_bfs_rows": budget.rows, "operations": budget.operations,
                      "reflected_parent_rows": sum(len(t.rows) for t in witness.tables),
                      "word_letters": budget.word_letters,
                      "max_word_length": budget.max_word_length,
                      "output_bytes": len(content)}, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (CertificateError, OSError, EOFError, RecursionError, json.JSONDecodeError) as error:
        print(f"selected prime composition: {error}", file=sys.stderr)
        raise SystemExit(2)
