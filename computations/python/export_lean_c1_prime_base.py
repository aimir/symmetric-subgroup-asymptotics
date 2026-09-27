#!/usr/bin/env python3
"""Emit the sparse original-action prime-base certificate for 12T194.

The full action has order 972, but the certificate enumerates only its
81-element ternary base, its 12-element lifted block complement, and the
12-element four-point top.  Literal words prove the semidirect factorization;
the action-level supplement proves the four actual triples, all eight local
translations, and the exact faithful order-twelve block action.  No ambient
Cayley table or catalogue identifier is emitted as a theorem premise.
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

from export_lean_menu_cayley import (
    ROOT, array, checks, compose, finite_lookup, lookup, packed, packed_lookup, table,
)
from export_lean_prime_composition import (
    Budget, CertificateError, DATA, LIMIT_SPECS, bounded_file_hash,
    read_selected, require,
)

INDEX = 194
AMBIENT_CEILING = 972
WORD_LENGTH_CEILING = 256
OUTPUT_LIMIT = 4 * 1024 * 1024


def permutations(value: object, degree: int, name: str) -> list[tuple[int, ...]]:
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


def positive_words(generators: list[tuple[int, ...]], ceiling: int,
                   budget: Budget, name: str) -> dict[tuple[int, ...], tuple[int, ...]]:
    require(generators, f"{name}: empty generator list")
    identity = tuple(range(len(generators[0])))
    words = {identity: ()}
    queue = deque([identity])
    while queue:
        current = queue.popleft()
        for letter, generator in enumerate(generators):
            budget.operation()
            product = compose(current, generator)
            if product in words:
                continue
            require(len(words) < ceiling, f"{name}: closure exceeded its row ceiling")
            word = words[current] + (letter,)
            require(len(word) <= WORD_LENGTH_CEILING,
                    f"{name}: positive word exceeded its length ceiling")
            words[product] = word
            queue.append(product)
    return words


def lean_word(word: tuple[int, ...]) -> str:
    return "[" + ",".join(str(x) for x in word) + "]"


def permutation_def(name: str, value: tuple[int, ...], degree: int) -> str:
    inv = inverse(value)
    return f'''private def {name} : Equiv.Perm (Fin {degree}) where
  toFun x := ({array(value)} : Array (Fin {degree}))[x.val]!
  invFun x := ({array(inv)} : Array (Fin {degree}))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

'''


def generator_family(prefix: str, values: list[tuple[int, ...]], degree: int) -> str:
    text = "".join(permutation_def(f"{prefix}Generator{i}", value, degree)
                   for i, value in enumerate(values))
    names = [f"{prefix}Generator{i}" for i in range(len(values))]
    return text + f'''def {prefix}Generators (j : Fin {len(values)}) : Equiv.Perm (Fin {degree}) :=
  {lookup(names, "j.val")}

'''


def cayley_block(prefix: str, generators: list[tuple[int, ...]], degree: int,
                 ceiling: int) -> tuple[str, int]:
    data = table(generators, degree, max_rows=ceiling)
    n, d = len(data["codes"]), len(generators)
    code_expr = finite_lookup(data["codes"], degree**degree, packed=True)
    rank_expr = packed_lookup(data["rank"])
    parent_expr = finite_lookup(data["parent"], n, packed=True)
    letter_expr = finite_lookup(data["letter"], d, packed=True)
    next_expr = finite_lookup([x for row in data["next"] for x in row], n,
                              f"i.val * {d} + j.val", True)
    text = f'''private def {prefix}Codes (i : Fin {n}) : Fin ({degree}^{degree}) :=
  {code_expr}
private def {prefix}Ranks (i : Fin {n}) : ℕ :=
  {rank_expr}
private def {prefix}Parents (i : Fin {n}) : Fin {n} :=
  {parent_expr}
private def {prefix}Letters (i : Fin {n}) : Fin {d} :=
  {letter_expr}
private def {prefix}Next (i : Fin {n}) (j : Fin {d}) : Fin {n} :=
  {next_expr}

private theorem {prefix}_parent_lt : ∀ i : Fin {n},
    i ≠ {data["identity"]} → {prefix}Ranks ({prefix}Parents i) < {prefix}Ranks i := {checks(n)}
private theorem {prefix}_parent_next : ∀ i : Fin {n},
    i ≠ {data["identity"]} →
      {prefix}Next ({prefix}Parents i) ({prefix}Letters i) = i := {checks(n)}

def {prefix}Encoded : EncodedCayleyCertificate
    (permutationGeneratorEncoding {prefix}Generators) {n} where
  rows := {prefix}Codes
  identity := {data["identity"]}
  identity_eq := by decide +kernel
  next := {prefix}Next
  next_eq := {checks(n)}
  rank := {prefix}Ranks
  parent i _ := {prefix}Parents i
  letter i _ := {prefix}Letters i
  parent_lt := {prefix}_parent_lt
  parent_next := {prefix}_parent_next

private theorem {prefix}_codes_strict : StrictMono {prefix}Codes :=
  Fin.strictMono_iff_lt_succ.mpr {checks(n - 1)}

theorem {prefix}RowsInjective : Function.Injective {prefix}Encoded.toCayley.elements :=
  {prefix}Encoded.elements_injective {prefix}_codes_strict.injective

'''
    return text, n


def word_function(name: str, domain: str, codomain_count: int,
                  words: list[tuple[int, ...]], index: str = "i.val") -> str:
    return f'''private def {name} (i : {domain}) : List (Fin {codomain_count}) :=
  {lookup([lean_word(word) for word in words], index)}

'''


def build(row: dict[str, object], selected_line: int, row_hash: str,
          budget: Budget) -> tuple[Path, str, dict[str, int]]:
    source = permutations(row.get("generators"), 12, "source")
    owner = row.get("owner")
    require(isinstance(owner, dict) and owner.get("kind") == "prime_base",
            "selected row has no prime-base owner")
    base = permutations(owner.get("base"), 12, "base")
    top_images = permutations(owner.get("top_images"), 4, "top images")
    require(len(top_images) == len(source), "source/top generator counts differ")
    identity4 = tuple(range(4))
    complement_indices = [i for i, image in enumerate(top_images) if image != identity4]
    require(complement_indices, "prime-base owner has no lifted top generators")
    complement = [source[i] for i in complement_indices]
    top = [top_images[i] for i in complement_indices]

    source_words = positive_words(source, AMBIENT_CEILING, budget, "source")
    base_words = positive_words(base, 81, budget, "base")
    complement_words = positive_words(complement, 12, budget, "complement")
    top_words = positive_words(top, 12, budget, "top")
    require(len(source_words) == 972, "prime-base source does not have order 972")
    require(len(base_words) == 81, "prime base does not have order 81")
    require(len(complement_words) == 12, "lifted block complement does not have order 12")
    require(len(top_words) == 12, "four-point top does not have order 12")
    require(set(base_words) <= set(source_words)
            and set(complement_words) <= set(source_words),
            "retained factor escaped the actual source closure")

    base_in_source = [source_words[x] for x in base]
    complement_in_source = [source_words[x] for x in complement]
    source_base_words: list[tuple[int, ...]] = []
    source_complement_words: list[tuple[int, ...]] = []
    for generator in source:
        choices = [(b, c) for b in base_words for c in complement_words
                   if compose(b, c) == generator]
        require(len(choices) == 1, "source generator lacks unique base/complement factor")
        b, c = choices[0]
        source_base_words.append(base_words[b])
        source_complement_words.append(complement_words[c])

    conjugate_words = []
    for s in source:
        for b in base:
            conjugate = compose(compose(s, b), inverse(s))
            require(conjugate in base_words, "source generator does not normalize the base")
            conjugate_words.append(base_words[conjugate])

    blocks_value = owner.get("blocks")
    require(isinstance(blocks_value, list) and len(blocks_value) == 4,
            "prime-base owner lost its four literal blocks")
    blocks: list[set[int]] = []
    for block in blocks_value:
        require(isinstance(block, list) and len(block) == 3
                and all(type(x) is int and 1 <= x <= 12 for x in block),
                "malformed literal three-point block")
        blocks.append({x - 1 for x in block})
    require(set().union(*blocks) == set(range(12))
            and sum(map(len, blocks)) == 12, "literal blocks do not partition the points")
    point_block = {}
    for i, block in enumerate(blocks):
        for x in block:
            require(x not in point_block, "literal blocks overlap")
            point_block[x] = i

    identity12 = tuple(range(12))
    local: list[tuple[int, ...]] = []
    for block in blocks:
        entries = [x for x in base_words if x != identity12
                   and {p for p in range(12) if x[p] != p} == block]
        require(len(entries) == 2, "a literal block does not carry exactly two translations")
        local.extend(sorted(entries, key=packed))
    require(len(set(local)) == 8, "local translations are not distinct")
    local_in_base = [base_words[x] for x in local]
    local_words = positive_words(local, 81, budget, "local translations")
    require(set(local_words) == set(base_words), "local translations do not generate the base")
    base_in_local = [local_words[x] for x in base]
    require(all(compose(compose(x, x), x) == identity12 for x in base_words),
            "ternary base is not elementary")

    for c, t in zip(complement, top):
        for x in range(12):
            require(point_block[c[x]] == t[point_block[x]],
                    "lifted complement action disagrees with the four-point top")
    transitive_words: list[tuple[int, ...]] = []
    for target in range(4):
        choices = [(len(word), word) for action, word in top_words.items()
                   if action[0] == target]
        require(choices, "four-point top is not transitive")
        transitive_words.append(min(choices)[1])

    module_name = "TernaryPrimeBase12T194"
    text = f'''import SymmetricSubgroupAsymptotics.C1PrimeBaseGeometryCertificate
import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Sparse full prime-base certificate for 12T194

Generated by export_lean_c1_prime_base.py from selected transitive row
{selected_line} (raw-line SHA256 {row_hash}).  Only the 81-row ternary base,
the 12-row lifted complement and its 12-row four-point image are enumerated.
Literal words prove the original action factorization and all block geometry;
no ambient Cayley table or catalogue group identifier is used as a theorem
premise.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.{module_name}

'''
    text += generator_family("source", source, 12)
    text += generator_family("base", base, 12)
    text += generator_family("complement", complement, 12)
    text += generator_family("local", local, 12)
    text += generator_family("top", top, 4)
    base_block, base_order = cayley_block("base", base, 12, 81)
    complement_block, complement_order = cayley_block("complement", complement, 12, 12)
    top_block, top_order = cayley_block("top", top, 4, 12)
    text += base_block + complement_block + top_block
    text += f'''private theorem baseRowsExponentThree : ∀ i : Fin {base_order},
    (baseEncoded.toCayley.elements i) ^ 3 = 1 :=
  {checks(base_order)}

private theorem factorIntersectionRows : ∀ i : Fin {base_order},
    ∀ j : Fin {complement_order},
      baseEncoded.toCayley.elements i = complementEncoded.toCayley.elements j →
        baseEncoded.toCayley.elements i = 1 :=
  {checks(base_order)}

'''
    text += word_function("baseInSourceWord", f"Fin {len(base)}", len(source),
                          base_in_source)
    text += word_function("complementInSourceWord", f"Fin {len(complement)}", len(source),
                          complement_in_source)
    text += word_function("sourceBaseWord", f"Fin {len(source)}", len(base),
                          source_base_words)
    text += word_function("sourceComplementWord", f"Fin {len(source)}", len(complement),
                          source_complement_words)
    text += word_function("conjugateWord", f"Fin {len(source)} × Fin {len(base)}",
                          len(base), conjugate_words,
                          f"i.1.val * {len(base)} + i.2.val")
    text += word_function("localInBaseWord", "Fin 8", len(base), local_in_base)
    text += word_function("baseInLocalWord", f"Fin {len(base)}", 8, base_in_local)
    text += word_function("transitiveWord", "Fin 4", len(complement), transitive_words)
    point_block_expr = lookup([str(point_block[x]) for x in range(12)], "x.val")
    text += f'''private def baseInSource : BinaryNormalGeneratorWords
    baseGenerators sourceGenerators where
  words := baseInSourceWord
  equations := by decide +kernel

private def complementInSource : BinaryNormalGeneratorWords
    complementGenerators sourceGenerators where
  words := complementInSourceWord
  equations := by decide +kernel

private def conjugates : BinaryNormalGeneratorWords
    (fun ij : Fin {len(source)} × Fin {len(base)} =>
      sourceGenerators ij.1 * baseGenerators ij.2 * (sourceGenerators ij.1)⁻¹)
    baseGenerators where
  words := conjugateWord
  equations := by decide +kernel

def certificate : C1SparseSemidirectCertificate (Equiv.Perm (Fin 12)) where
  sourceCount := {len(source)}
  baseGeneratorCount := {len(base)}
  complementGeneratorCount := {len(complement)}
  sourceGenerators := sourceGenerators
  baseGenerators := baseGenerators
  complementGenerators := complementGenerators
  baseOrder := {base_order}
  complementOrder := {complement_order}
  baseCayley := baseEncoded.toCayley
  complementCayley := complementEncoded.toCayley
  baseRowsInjective := baseRowsInjective
  complementRowsInjective := complementRowsInjective
  baseInSource := baseInSource
  complementInSource := complementInSource
  sourceBaseWords := sourceBaseWord
  sourceComplementWords := sourceComplementWord
  sourceFactorization := by decide +kernel
  conjugateWords := conjugates

theorem base_card : Nat.card certificate.base = {base_order} :=
  certificate.base_card

theorem complement_card : Nat.card certificate.complement = {complement_order} :=
  certificate.complement_card

theorem base_normal_in_action :
    (certificate.base.subgroupOf certificate.action).Normal :=
  certificate.base_normal_in_action

theorem action_join :
    certificate.actionBase ⊔ certificate.actionComplement = ⊤ :=
  certificate.action_join

private def blocks (b : Fin 4) : Finset (Fin 12) :=
  {lookup([f"({{{','.join(map(str, sorted(block)))}}} : Finset (Fin 12))" for block in blocks], "b.val")}

private def pointBlock (x : Fin 12) : Fin 4 :=
  Fin.ofNat 4 ({point_block_expr})

private def coordinate (i : Fin 8) : Fin 4 :=
  Fin.ofNat 4 (i.val / 2)

private def localInBase : BinaryNormalGeneratorWords
    localGenerators baseGenerators where
  words := localInBaseWord
  equations := by decide +kernel

private def baseInLocal : BinaryNormalGeneratorWords
    baseGenerators localGenerators where
  words := baseInLocalWord
  equations := by decide +kernel

def geometry : C1PrimeBaseGeometryCertificate certificate where
  blocks := blocks
  block_card := by decide +kernel
  pointBlock := pointBlock
  block_membership := by decide +kernel
  coordinate := coordinate
  coordinate_card := by decide +kernel
  localTranslations := localGenerators
  local_ne_one := by decide +kernel
  local_injective := by decide +kernel
  local_support := by decide +kernel
  local_inverse := by decide +kernel
  localInBase := localInBase
  baseInLocal := baseInLocal
  rows_exponent_three := baseRowsExponentThree
  factor_intersection_rows := factorIntersectionRows
  topGenerators := topGenerators
  topCayley := topEncoded.toCayley
  topRowsInjective := topRowsInjective
  block_action := by decide +kernel
  transitiveWord := transitiveWord
  transitive_from_zero := by decide +kernel

theorem base_exponent_three : ∀ x : certificate.base, x ^ 3 = 1 :=
  geometry.base_exponent_three

theorem factor_intersection_trivial (x : Equiv.Perm (Fin 12))
    (hxBase : x ∈ certificate.base) (hxComplement : x ∈ certificate.complement) : x = 1 :=
  geometry.factor_intersection_trivial x hxBase hxComplement

theorem factors_disjoint : Disjoint certificate.base certificate.complement :=
  geometry.factors_disjoint

theorem localClosure_eq_base :
    Subgroup.closure (Set.range localGenerators) = certificate.base :=
  geometry.localClosure_eq_base

theorem top_card : Nat.card geometry.top = {top_order} :=
  geometry.top_card

end SymmetricSubgroupAsymptotics.{module_name}
'''
    path = ROOT / f"formal/SymmetricSubgroupAsymptotics/{module_name}.lean"
    return path, text, {
        "ambient_search_rows": len(source_words),
        "base_rows": base_order,
        "complement_rows": complement_order,
        "top_rows": top_order,
        "max_word_length": max(map(len, base_in_source + complement_in_source
                                   + source_base_words + source_complement_words
                                   + conjugate_words + local_in_base + base_in_local
                                   + transitive_words)),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--expect-row-sha256")
    parser.add_argument("--max-seconds", type=float, default=60.0)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    require(math.isfinite(args.max_seconds) and 0 < args.max_seconds <= 120,
            "--max-seconds must be finite, positive and at most 120")
    if args.expect_row_sha256 is not None:
        require(re.fullmatch(r"[0-9a-f]{64}", args.expect_row_sha256) is not None,
                "--expect-row-sha256 must be a lowercase SHA256 digest")
    limits = {name: ceiling for name, (_default, ceiling) in LIMIT_SPECS.items()}
    limits["operations"] = max(limits["operations"], 500000)
    budget = Budget(limits, args.max_seconds, time.monotonic())
    selected = read_selected(12, INDEX, budget, args.expect_row_sha256,
                             catalogue="transitive")
    path, text, stats = build(selected.value, selected.line,
                              selected.line_sha256, budget)
    content = text.encode("utf-8")
    require(len(content) <= OUTPUT_LIMIT, "selected sparse output exceeds byte cap")
    require(bounded_file_hash(DATA, budget) == selected.data_sha256,
            "committed input changed during production")
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
        "path": str(path.relative_to(ROOT)), "checked": args.check,
        "source_sha256": hashlib.sha256(content).hexdigest(),
        "selected_line": selected.line, "row_sha256": selected.line_sha256,
        "output_bytes": len(content), **stats,
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (CertificateError, OSError, EOFError, RecursionError, ValueError,
            json.JSONDecodeError) as error:
        print(f"selected c=1 prime-base owner: {error}", file=sys.stderr)
        raise SystemExit(2)
