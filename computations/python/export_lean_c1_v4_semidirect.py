#!/usr/bin/env python3
"""Emit one sparse semidirect certificate for 12T228/229/265.

Only the retained binary base (64 rows) and ternary complement (27 or 81
rows) receive Cayley certificates.  A bounded positive-word search in the
selected original source supplies inclusion, source factorization and
conjugation words; no ambient multiplication table is emitted.  Lean checks
all literal permutation equations and derives generation and normality via
``C1SparseSemidirectCertificate``.
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
    ROOT, array, checks, compose, finite_lookup, lookup, packed_lookup, table,
)
from export_lean_prime_composition import (
    Budget, CertificateError, DATA, LIMIT_SPECS, bounded_file_hash,
    read_selected, require,
)

ALLOWED = {228, 229, 265}
AMBIENT_CEILING = 5184
WORD_LENGTH_CEILING = 256
OUTPUT_LIMIT = 4 * 1024 * 1024


def permutations(value: object, name: str) -> list[tuple[int, ...]]:
    require(isinstance(value, list) and value, f"{name}: missing generator list")
    result = []
    for images in value:
        require(isinstance(images, list) and len(images) == 12,
                f"{name}: wrong permutation degree")
        require(all(type(x) is int for x in images)
                and sorted(images) == list(range(1, 13)),
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
    identity = tuple(range(12))
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


def permutation_def(name: str, value: tuple[int, ...]) -> str:
    inv = inverse(value)
    return f'''private def {name} : Equiv.Perm (Fin 12) where
  toFun x := ({array(value)} : Array (Fin 12))[x.val]!
  invFun x := ({array(inv)} : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

'''


def generator_family(prefix: str, values: list[tuple[int, ...]]) -> str:
    text = "".join(permutation_def(f"{prefix}Generator{i}", value)
                   for i, value in enumerate(values))
    names = [f"{prefix}Generator{i}" for i in range(len(values))]
    return text + f'''def {prefix}Generators (j : Fin {len(values)}) : Equiv.Perm (Fin 12) :=
  {lookup(names, "j.val")}

'''


def cayley_block(prefix: str, generators: list[tuple[int, ...]], ceiling: int) -> tuple[str, int]:
    data = table(generators, 12, max_rows=ceiling)
    n, d = len(data["codes"]), len(generators)
    code_expr = finite_lookup(data["codes"], 12**12, packed=True)
    rank_expr = packed_lookup(data["rank"])
    parent_expr = finite_lookup(data["parent"], n, packed=True)
    letter_expr = finite_lookup(data["letter"], d, packed=True)
    next_expr = finite_lookup([x for row in data["next"] for x in row], n,
                              f"i.val * {d} + j.val", True)
    text = f'''private def {prefix}Codes (i : Fin {n}) : Fin (12^12) :=
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
                  words: list[tuple[int, ...]],
                  index: str = "i.val") -> str:
    return f'''private def {name} (i : {domain}) : List (Fin {codomain_count}) :=
  {lookup([lean_word(word) for word in words], index)}

'''


def build(index: int, row: dict[str, object], selected_line: int,
          row_hash: str, budget: Budget) -> tuple[Path, str, dict[str, int]]:
    source = permutations(row.get("generators"), "source")
    owner = row.get("owner")
    require(isinstance(owner, dict) and owner.get("kind") == "v4_blocks",
            "selected row has no V4-block owner")
    base = permutations(owner.get("base"), "base")
    complement = permutations(owner.get("complement"), "complement")

    source_words = positive_words(source, AMBIENT_CEILING, budget, "source")
    base_words = positive_words(base, 64, budget, "base")
    complement_words = positive_words(complement, 81, budget, "complement")
    require(len(source_words) <= AMBIENT_CEILING, "source closure escaped its ceiling")
    require(len(base_words) == 64, "V4-block base does not have order 64")
    require(len(complement_words) in (27, 81),
            "V4-block complement does not have retained ternary order")
    require(set(base_words) <= set(source_words) and set(complement_words) <= set(source_words),
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

    module_name = f"TernaryV4Semidirect12T{index}"
    text = f'''import SymmetricSubgroupAsymptotics.C1SparseSemidirectCertificate
import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Sparse V4-block semidirect certificate for 12T{index}

Generated by export_lean_c1_v4_semidirect.py from selected transitive row
{selected_line} (raw-line SHA256 {row_hash}).  Only the 64-row binary base and
the {len(complement_words)}-row ternary complement are enumerated.  Literal
source words prove inclusion, generation and normality; no ambient Cayley
table or catalogue group identifier is used as a theorem premise.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.{module_name}

'''
    text += generator_family("source", source)
    text += generator_family("base", base)
    text += generator_family("complement", complement)
    base_block, base_order = cayley_block("base", base, 64)
    complement_block, complement_order = cayley_block("complement", complement, 81)
    text += base_block + complement_block
    text += word_function("baseInSourceWord", f"Fin {len(base)}", len(source),
                          base_in_source)
    text += word_function("complementInSourceWord", f"Fin {len(complement)}", len(source),
                          complement_in_source)
    text += word_function("sourceBaseWord", f"Fin {len(source)}", len(base),
                          source_base_words)
    text += word_function("sourceComplementWord", f"Fin {len(source)}", len(complement),
                          source_complement_words)
    text += word_function("conjugateWord",
                          f"Fin {len(source)} × Fin {len(base)}", len(base), conjugate_words,
                          f"i.1.val * {len(base)} + i.2.val")
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

theorem base_card : Nat.card certificate.base = 64 :=
  certificate.base_card

theorem complement_card : Nat.card certificate.complement = {complement_order} :=
  certificate.complement_card

theorem base_normal_in_action :
    (certificate.base.subgroupOf certificate.action).Normal :=
  certificate.base_normal_in_action

theorem action_join :
    certificate.actionBase ⊔ certificate.actionComplement = ⊤ :=
  certificate.action_join

end SymmetricSubgroupAsymptotics.{module_name}
'''
    path = ROOT / f"formal/SymmetricSubgroupAsymptotics/{module_name}.lean"
    return path, text, {
        "ambient_search_rows": len(source_words),
        "base_rows": base_order,
        "complement_rows": complement_order,
        "max_word_length": max(map(len, base_in_source + complement_in_source
                                   + source_base_words + source_complement_words
                                   + conjugate_words)),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--index", type=int, required=True, choices=sorted(ALLOWED))
    parser.add_argument("--expect-row-sha256")
    parser.add_argument("--check", action="store_true")
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
    selected = read_selected(12, args.index, budget, args.expect_row_sha256,
                             catalogue="transitive")
    path, text, stats = build(args.index, selected.value, selected.line,
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
        print(f"selected c=1 V4 semidirect: {error}", file=sys.stderr)
        raise SystemExit(2)
