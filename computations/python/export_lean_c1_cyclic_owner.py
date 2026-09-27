#!/usr/bin/env python3
"""Emit one intrinsic cyclic-module owner witness for 12T20/85/164.

The selected literal action certificate must already exist.  This producer
recomputes the actual ambient, binary-base and ternary-complement closures
under a 576-row ceiling.  It rejects non-elementary factors, nonunique
factorization, failed complement normalization, or a noncyclic retained
vector.  Lean then checks the emitted subgroup laws, cardinalities,
factorization, normality, exponents and every cyclic conjugate word.

The producer makes no degree-twelve catalogue-coverage claim. ``--check``
is a read-only byte replay; Lean compilation remains a separate serialized
primary-agent operation.
"""
from __future__ import annotations

import argparse
from collections import deque
import hashlib
import json
import math
import os
from pathlib import Path
import re
import sys
import tempfile
import time

sys.dont_write_bytecode = True

from export_lean_menu_cayley import ROOT, compose, packed_lookup, table
from export_lean_prime_composition import (
    Budget,
    CertificateError,
    DATA,
    LIMIT_SPECS,
    bounded_file_hash,
    read_selected,
    require,
)

ALLOWED = {20, 85, 164}
ROW_CEILING = 576
OUTPUT_LIMIT = 4 * 1024 * 1024


def parse_permutations(value: object, degree: int, name: str) -> list[tuple[int, ...]]:
    require(isinstance(value, list) and value, f"{name}: missing generator list")
    result = []
    for images in value:
        require(isinstance(images, list) and len(images) == degree,
                f"{name}: wrong permutation degree")
        require(all(type(x) is int for x in images)
                and sorted(images) == list(range(1, degree + 1)),
                f"{name}: malformed one-based permutation")
        result.append(tuple(x - 1 for x in images))
    return result


def inverse(value: tuple[int, ...]) -> tuple[int, ...]:
    result = [0] * len(value)
    for i, x in enumerate(value):
        result[x] = i
    return tuple(result)


def power(value: tuple[int, ...], exponent: int) -> tuple[int, ...]:
    result = tuple(range(len(value)))
    for _ in range(exponent):
        result = compose(result, value)
    return result


def bit_mask(indices: list[int]) -> int:
    return sum(1 << i for i in indices)


def exact_power_exponent(value: int, prime: int) -> int:
    exponent, current = 0, 1
    while current < value:
        current *= prime
        exponent += 1
    require(current == value, f"{value} is not a power of {prime}")
    return exponent


def lean_checks(n: int) -> str:
    if n <= 16:
        return "(by decide +kernel)"
    k = n // 2
    return (f"(Fin.addCases (m := {k}) (n := {n-k}) "
            f"{lean_checks(k)} {lean_checks(n-k)})")


def build_owner_text(index: int, row: dict[str, object], source: dict[str, object],
                     selected_line: int, row_hash: str) -> tuple[Path, str, dict[str, int]]:
    degree = 12
    source_generators = parse_permutations(row["generators"], degree, "source")
    ambient = table(source_generators, degree, max_rows=ROW_CEILING)
    rows = ambient["elements"]
    n = len(rows)
    row_index = {value: i for i, value in enumerate(rows)}
    require(len(row_index) == n, "ambient sorted rows are not injective")

    owner = row.get("owner")
    require(isinstance(owner, dict) and owner.get("kind") == "cyclic_module",
            "selected row has no cyclic-module owner")
    module = owner.get("module")
    require(isinstance(module, dict), "cyclic-module owner lost its module record")
    base_table = table(parse_permutations(module.get("base"), degree, "base"),
                       degree, max_rows=ROW_CEILING)
    complement_table = table(
        parse_permutations(module.get("complement"), degree, "complement"),
        degree, max_rows=ROW_CEILING)
    base_set = set(base_table["elements"])
    complement_set = set(complement_table["elements"])
    require(base_set <= set(rows) and complement_set <= set(rows),
            "retained owner subgroup is not contained in the actual source closure")
    identity = tuple(range(degree))
    require(all(power(x, 2) == identity for x in base_set),
            "retained base is not elementary binary")
    require(all(power(x, 3) == identity for x in complement_set),
            "retained complement is not elementary ternary")
    require(base_set.intersection(complement_set) == {identity},
            "retained base and complement do not intersect trivially")
    require(all(compose(compose(c, b), inverse(c)) in base_set
                for c in complement_set for b in base_set),
            "retained complement does not normalize the base")

    factor_base: list[int] = []
    factor_complement: list[int] = []
    for g in rows:
        factorizations = [(b, c) for b in base_set for c in complement_set
                          if compose(b, c) == g]
        require(len(factorizations) == 1,
                "retained base/complement do not give unique full factorization")
        b, c = factorizations[0]
        factor_base.append(row_index[b])
        factor_complement.append(row_index[c])

    vector_rows = parse_permutations([module.get("vector")], degree, "vector")
    vector = vector_rows[0]
    require(vector in base_set, "retained cyclic vector is outside the binary base")
    complement_rows = sorted(complement_set, key=row_index.get)
    complement_rows.remove(identity)
    complement_rows.insert(0, identity)
    conjugates = [compose(compose(c, vector), inverse(c)) for c in complement_rows]
    words: dict[tuple[int, ...], list[int]] = {identity: []}
    queue = deque([identity])
    while queue:
        current = queue.popleft()
        for letter, conjugate in enumerate(conjugates):
            product = compose(current, conjugate)
            if product not in words:
                require(product in base_set, "cyclic conjugate word escaped the base")
                words[product] = words[current] + [letter]
                queue.append(product)
    require(set(words) == base_set, "retained vector is not cyclic under the complement")

    base_indices = sorted(row_index[x] for x in base_set)
    complement_indices = sorted(row_index[x] for x in complement_set)
    complement_enum = [row_index[x] for x in complement_rows]
    lengths = [len(words[x]) if x in base_set else 0 for x in rows]
    max_length = max(lengths)
    require(max_length > 0, "nontrivial base unexpectedly has no cyclic letters")
    letters = []
    for x in rows:
        word = words[x] if x in base_set else []
        letters.extend(word + [0] * (max_length - len(word)))

    base_power = exact_power_exponent(len(base_set), 2)
    complement_power = exact_power_exponent(len(complement_set), 3)

    module_name = f"TernaryOwnerWitness12T{index}"
    cayley_name = f"TernaryOwnerCayley12T{index}"
    path = ROOT / f"formal/SymmetricSubgroupAsymptotics/{module_name}.lean"
    factor_base_expr = packed_lookup(factor_base, "x.index.val")
    factor_complement_expr = packed_lookup(factor_complement, "x.index.val")
    complement_expr = packed_lookup(complement_enum, "j.val")
    base_rows_expr = packed_lookup(base_indices, "j.val")
    complement_rows_expr = packed_lookup(complement_indices, "j.val")
    base_rank_values = [0] * n
    for rank, value in enumerate(base_indices):
        base_rank_values[value] = rank
    complement_rank_values = [0] * n
    for rank, value in enumerate(complement_indices):
        complement_rank_values[value] = rank
    base_rank_expr = packed_lookup(base_rank_values, "i.val")
    complement_rank_expr = packed_lookup(complement_rank_values, "i.val")
    length_expr = packed_lookup(lengths, "i.val")
    letter_expr = packed_lookup(letters, f"i.val * {max_length} + j")
    base_mask = bit_mask(base_indices)
    complement_mask = bit_mask(complement_indices)
    vector_index = row_index[vector]
    source_hash = source["source_sha256"]

    text = f'''import SymmetricSubgroupAsymptotics.C1FiniteOwnerWitness
import SymmetricSubgroupAsymptotics.{cayley_name}

/-!
# Intrinsic cyclic binary-module owner witness for 12T{index}

Generated by export_lean_c1_cyclic_owner.py from selected transitive row
{selected_line} (raw-line SHA256 {row_hash}).  The imported literal action
source has SHA256 {source_hash}.  Lean checks the actual subgroups,
factorization and cyclic conjugate words; the catalogue owner label is not a
theorem premise.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.{module_name}

open {cayley_name}

local instance rowGroup : Group (FiniteGroupRow {n}) := group

private def baseMask (i : Fin {n}) : Prop :=
  ({base_mask} / 2 ^ i.val) % 2 = 1

private def complementMask (i : Fin {n}) : Prop :=
  ({complement_mask} / 2 ^ i.val) % 2 = 1

private instance baseMaskDecidable (i : Fin {n}) : Decidable (baseMask i) := by
  unfold baseMask
  infer_instance

private instance complementMaskDecidable (i : Fin {n}) : Decidable (complementMask i) := by
  unfold complementMask
  infer_instance

private def baseRow (j : Fin {len(base_set)}) : Fin {n} :=
  Fin.ofNat {n} ({base_rows_expr})

private def baseRank (i : Fin {n}) : Fin {len(base_set)} :=
  Fin.ofNat {len(base_set)} ({base_rank_expr})

private theorem base_decode : ∀ i : Fin {n}, baseMask i → baseRow (baseRank i) = i :=
  {lean_checks(n)}

private theorem base_mul_checked : ∀ i : Fin {len(base_set)}, ∀ j : Fin {len(base_set)},
    baseMask (((⟨baseRow i⟩ : FiniteGroupRow {n}) *
      (⟨baseRow j⟩ : FiniteGroupRow {n})).index) :=
  {lean_checks(len(base_set))}

private theorem base_inv_checked : ∀ i : Fin {len(base_set)},
    baseMask ((⟨baseRow i⟩ : FiniteGroupRow {n})⁻¹).index :=
  {lean_checks(len(base_set))}

private def complementRow (j : Fin {len(complement_set)}) : Fin {n} :=
  Fin.ofNat {n} ({complement_rows_expr})

private def complementRank (i : Fin {n}) : Fin {len(complement_set)} :=
  Fin.ofNat {len(complement_set)} ({complement_rank_expr})

private theorem complement_decode : ∀ i : Fin {n},
    complementMask i → complementRow (complementRank i) = i :=
  {lean_checks(n)}

private theorem complement_mul_checked : ∀ i : Fin {len(complement_set)},
    ∀ j : Fin {len(complement_set)},
    complementMask (((⟨complementRow i⟩ : FiniteGroupRow {n}) *
      (⟨complementRow j⟩ : FiniteGroupRow {n})).index) := by
  decide +kernel

private theorem complement_inv_checked : ∀ i : Fin {len(complement_set)},
    complementMask ((⟨complementRow i⟩ : FiniteGroupRow {n})⁻¹).index := by
  decide +kernel

def base : Subgroup (FiniteGroupRow {n}) where
  carrier := {{x | baseMask x.index}}
  one_mem' := by decide +kernel
  mul_mem' := by
    rintro ⟨i⟩ ⟨j⟩ hi hj
    rw [← base_decode i hi, ← base_decode j hj]
    exact base_mul_checked _ _
  inv_mem' := by
    rintro ⟨i⟩ hi
    rw [← base_decode i hi]
    exact base_inv_checked _

def complement : Subgroup (FiniteGroupRow {n}) where
  carrier := {{x | complementMask x.index}}
  one_mem' := by decide +kernel
  mul_mem' := by
    rintro ⟨i⟩ ⟨j⟩ hi hj
    rw [← complement_decode i hi, ← complement_decode j hj]
    exact complement_mul_checked _ _
  inv_mem' := by
    rintro ⟨i⟩ hi
    rw [← complement_decode i hi]
    exact complement_inv_checked _

private instance baseMembership : DecidablePred (fun x => x ∈ base) :=
  fun x => by change Decidable (baseMask x.index); infer_instance

private instance complementMembership : DecidablePred (fun x => x ∈ complement) :=
  fun x => by change Decidable (complementMask x.index); infer_instance

theorem base_card : Nat.card base = {len(base_set)} := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem complement_card : Nat.card complement = {len(complement_set)} := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

def factorBase (x : FiniteGroupRow {n}) : base :=
  ⟨⟨Fin.ofNat {n} ({factor_base_expr})⟩, by decide +kernel +revert⟩

def factorComplement (x : FiniteGroupRow {n}) : complement :=
  ⟨⟨Fin.ofNat {n} ({factor_complement_expr})⟩, by decide +kernel +revert⟩

theorem factorization : ∀ x : FiniteGroupRow {n},
    (factorBase x : FiniteGroupRow {n}) *
      (factorComplement x : FiniteGroupRow {n}) = x := by
  rintro ⟨i⟩
  revert i
  exact {lean_checks(n)}

theorem complement_normalizes : ∀ c : complement, ∀ x : base,
    (c : FiniteGroupRow {n}) * (x : FiniteGroupRow {n}) *
      (c : FiniteGroupRow {n})⁻¹ ∈ base := by
  decide +kernel

theorem base_normal : base.Normal := by
  constructor
  intro x hx g
  rw [← factorization g]
  have hc := complement_normalizes (factorComplement g) (⟨x, hx⟩ : base)
  have hb := base.mul_mem (factorBase g).property
    (base.mul_mem hc (base.inv_mem (factorBase g).property))
  simpa only [mul_inv_rev, mul_assoc] using hb

theorem base_isPGroup : IsPGroup 2 base :=
  IsPGroup.of_card (n := {base_power}) (by simpa using base_card)

theorem complement_isPGroup : IsPGroup 3 complement :=
  IsPGroup.of_card (n := {complement_power}) (by simpa using complement_card)

theorem base_exponent_two : ∀ x : base, x ^ 2 = 1 := by
  decide +kernel

theorem complement_exponent_three : ∀ x : complement, x ^ 3 = 1 := by
  decide +kernel

theorem intersection_trivial : ∀ x : FiniteGroupRow {n},
    x ∈ base → x ∈ complement → x = 1 := by
  decide +kernel

def vector : base := ⟨⟨{vector_index}⟩, by decide +kernel⟩

private def complementElement (j : Fin {len(complement_rows)}) : complement :=
  ⟨⟨Fin.ofNat {n} ({complement_expr})⟩, by decide +kernel +revert⟩

private def cyclicLength (i : Fin {n}) : ℕ :=
  {length_expr}

private def cyclicLetter (i : Fin {n}) (j : ℕ) : Fin {len(complement_rows)} :=
  Fin.ofNat {len(complement_rows)} ({letter_expr})

def cyclicWord (x : base) : List complement :=
  List.ofFn fun j : Fin (cyclicLength x.1.index) =>
    complementElement (cyclicLetter x.1.index j.val)

theorem cyclic_word_eq : ∀ x : base,
    ((cyclicWord x).map fun c : complement =>
      normalConjugate base base_normal vector (c : FiniteGroupRow {n})).prod = x := by
  decide +kernel +revert

def earlierOwner : C1CyclicBinaryModuleOwnerWitness (FiniteGroupRow {n}) where
  base := base
  complement := complement
  base_normal := base_normal
  basePGroup := base_isPGroup
  complementPGroup := complement_isPGroup
  base_exponent_two := base_exponent_two
  complement_exponent_three := complement_exponent_three
  intersection_trivial := intersection_trivial
  factorBase := factorBase
  factorComplement := factorComplement
  factorization := factorization
  vector := vector
  cyclicWord := cyclicWord
  cyclic_word_eq := cyclic_word_eq

end SymmetricSubgroupAsymptotics.{module_name}
'''
    return path, text, {
        "ambient_rows": n,
        "base_rows": len(base_set),
        "complement_rows": len(complement_set),
        "max_cyclic_word": max_length,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--index", type=int, required=True, choices=sorted(ALLOWED))
    parser.add_argument("--expect-row-sha256", help="Optional exact raw JSONL line hash pin.")
    parser.add_argument("--check", action="store_true",
                        help="Compare the selected output bytes; do not write.")
    parser.add_argument("--max-seconds", type=float, default=30.0)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    require(math.isfinite(args.max_seconds) and 0 < args.max_seconds <= 120,
            "--max-seconds must be finite, positive and at most 120")
    if args.expect_row_sha256 is not None:
        require(re.fullmatch(r"[0-9a-f]{64}", args.expect_row_sha256) is not None,
                "--expect-row-sha256 must be a lowercase SHA256 digest")
    limits = {name: default for name, (default, _ceiling) in LIMIT_SPECS.items()}
    budget = Budget(limits, args.max_seconds, time.monotonic())
    selected = read_selected(12, args.index, budget, args.expect_row_sha256,
                             catalogue="transitive")
    source_path = ROOT / f"formal/SymmetricSubgroupAsymptotics/TernaryOwnerCayley12T{args.index}.lean"
    require(source_path.is_file(), "checked literal action source is absent")
    source = {"source_sha256": hashlib.sha256(source_path.read_bytes()).hexdigest()}
    path, text, stats = build_owner_text(args.index, selected.value, source,
                                         selected.line, selected.line_sha256)
    content = text.encode("utf-8")
    require(len(content) <= OUTPUT_LIMIT, "selected owner output exceeds the fixed byte cap")
    require(bounded_file_hash(DATA, budget) == selected.data_sha256,
            "committed input changed during selected production; no output written")
    budget.time_check()
    if args.check:
        require(path.is_file() and path.read_bytes() == content,
                f"generated selected witness is missing/stale: {path.relative_to(ROOT)}")
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.is_file() or path.read_bytes() != content:
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
    print(json.dumps({
        "path": str(path.relative_to(ROOT)),
        "checked": args.check,
        "source_sha256": hashlib.sha256(content).hexdigest(),
        "selected_line": selected.line,
        "row_sha256": selected.line_sha256,
        "output_bytes": len(content),
        **stats,
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (CertificateError, OSError, EOFError, RecursionError, ValueError,
            json.JSONDecodeError) as error:
        print(f"selected c=1 cyclic owner: {error}", file=sys.stderr)
        raise SystemExit(2)
