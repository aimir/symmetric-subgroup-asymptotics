#!/usr/bin/env python3
"""Emit one bounded original-normal radical saturation certificate.

  python3 -B computations/python/export_lean_carrier_saturation.py \
    --master 1082 --write --report /private/path/saturation-1082.json
  python3 -B computations/python/export_lean_carrier_saturation.py --master 1082 --check

Only the selected existing derived-row words (at most64) are evaluated.
No closure search, original-group enumeration, normal enumeration, compiler,
subprocess, or network is used. For each row outside the selected radical,
the fixed radical generators are recovered by products of at most two
iterated original commutators, each of depth at most two. All original
ambient generators remain available, including redundant quotient ones.

The parser accepts only the present literal basic-commutator basis format;
source drift fails closed. The emitted Lean theorem independently checks
every original-point word equality, complete derived coverage, and exact
relative radical binding. Witness search and existing source bytes are not
proof receipts. Root must check the selected generated module.

Default mode prints a summary without writing. --check is exact-byte and
read-only; --write changes only the selected canonical source after all
validation. An optional report must be outside the publication repository.
Limits bound input/output bytes, row/word storage and counted operations.
The cooperative time limit is not an operating-system RSS or hard-time cap.
"""
from __future__ import annotations

import argparse
import ast
import hashlib
import json
import math
from pathlib import Path
import re
import sys
import time

sys.dont_write_bytecode = True
import export_lean_derived_square_words as square

ROOT, OUT = square.ROOT, square.OUT
require = square.require
MAX_ROWS = 64
MAX_RADICAL_ROWS = 8
MAX_GENERATORS = 7
MAX_PATH_DEPTH = 2
MAX_PRODUCT_LENGTH = 2
MAX_PATH_VALUES = 8
MAX_TOTAL_WITNESS_LETTERS = 768
MAX_OPERATIONS = 100_000
MAX_SECONDS = 5.0
MAX_OUTPUT_BYTES = 131_072
MAX_REPORT_BYTES = 131_072
MAX_SOURCE_BYTES = 131_072
MAX_ROW_WORD_LENGTH = 16
MAX_ROW_LETTERS = 1024

# Fixed actual radical generators, using the literal original tuple and
# the public DerivedOrder basis indices. These are checked again in Lean.
# Values are (derived rows, radical rows, radical seeds).
SPECS = {
    1082: (16, 2, (("comm", 0, 4),)),
    1083: (16, 2, (("comm", 1, 5),)),
    1084: (16, 2, (("pow", 2),)),
    1332: (64, 4, (("pow", 4), ("comm", 1, 3))),
    1547: (64, 8, (("pow", 1), ("comm", 0, 0), ("comm", 0, 1))),
}


def literal_definition(source: str, name: str) -> tuple[str, str]:
    matches = list(re.finditer(
        rf"^(?:private )?def {re.escape(name)}\b(?P<type>[^\n]*(?:\n(?!\n)[^\n]*)*?) :=\n?"
        rf"(?P<body>.*?)(?=\n\n|\Z)", source, re.M | re.S))
    require(len(matches) == 1, f"missing or ambiguous literal definition: {name}")
    return matches[0].group("type"), matches[0].group("body").strip()


def load_rows(master: int, generators, source: bytes, budget) -> dict:
    """Evaluate the complete existing row list; never discover new rows."""
    text = source.decode("utf-8")
    basis_type, basis_body = literal_definition(text, "basisWords")
    expected_rows, _, _ = SPECS[master]
    match = re.fullmatch(r"\s*: Fin (\d+) → DerivedGeneratorWord \(Fin (\d+)\)", basis_type)
    require(match is not None, "unsupported derived basis declaration")
    basis_count, generator_count = map(int, match.groups())
    require(1 <= basis_count <= 6 and generator_count == len(generators)
            and 1 <= generator_count <= MAX_GENERATORS, "derived basis size changed")
    require(re.fullmatch(r"!\[\s*\.comm \d+ \d+(?:\s*,\s*\.comm \d+ \d+)*\s*\]",
                         basis_body) is not None, "unsupported derived basis syntax")
    pairs = [tuple(map(int, pair)) for pair in re.findall(r"\.comm (\d+) (\d+)", basis_body)]
    require(len(pairs) == basis_count and all(0 <= i < generator_count and 0 <= j < generator_count
                                             for i, j in pairs), "derived basis index out of range")

    row_type, row_body = literal_definition(text, "rowWords")
    require(re.fullmatch(rf"\s*\(i : Fin {expected_rows}\) : List \(Fin {basis_count}\)", row_type)
            is not None, "derived row declaration changed")
    require(re.fullmatch(r"!\[[\s\d,\[\]]*\]\s+i", row_body) is not None,
            "unsupported literal derived-row syntax")
    row_words = ast.literal_eval(row_body[1:].rsplit("i", 1)[0].strip())
    require(isinstance(row_words, list) and len(row_words) == expected_rows
            and len(row_words) <= budget.max_states, "selected derived-row ceiling reached")
    require(all(isinstance(w, list) and len(w) <= MAX_ROW_WORD_LENGTH
                and all(type(j) is int and 0 <= j < basis_count for j in w) for w in row_words),
            "invalid or oversized derived row word")
    require(sum(map(len, row_words)) <= MAX_ROW_LETTERS, "derived row letters ceiling reached")

    def mul(a, b):
        budget.operation()
        return square.mul(a, b)

    def inverse(a):
        budget.operation()
        return square.inv(a)

    def comm(a, b):
        return mul(mul(mul(a, b), inverse(a)), inverse(b))

    identity = tuple(range(16))
    basis = [comm(generators[i], generators[j]) for i, j in pairs]
    rows = []
    for letters in row_words:
        value = identity
        for j in letters:
            value = mul(value, basis[j])
        rows.append(value)
    require(rows[0] == identity and len(set(rows)) == len(rows), "derived rows repeat or lack identity")
    budget.time_check()
    return dict(rows=rows, basis=basis, basis_count=basis_count, row_words=row_words)


def saturation(master: int, generators, data: dict, budget) -> dict:
    """Fixed-depth, fixed-product witness search on existing original rows."""
    _, radical_count, seeds = SPECS[master]
    rows, basis = data["rows"], data["basis"]
    identity = tuple(range(16))

    def mul(a, b):
        budget.operation()
        return square.mul(a, b)

    def inverse(a):
        budget.operation()
        return square.inv(a)

    def comm(a, b):
        return mul(mul(mul(a, b), inverse(a)), inverse(b))

    candidates = []
    for seed in seeds:
        require(0 <= seed[1] < len(basis), "radical seed basis index out of range")
        if seed[0] == "pow":
            candidates.append(mul(basis[seed[1]], basis[seed[1]]))
        else:
            require(seed[0] == "comm" and 0 <= seed[2] < len(generators), "invalid radical seed")
            candidates.append(comm(basis[seed[1]], generators[seed[2]]))
    # The small displayed radical words need only give distinct elements in
    # its already known cardinality. No multiplication closure is inferred.
    radical_words = [[j for j in range(len(seeds)) if (code >> j) & 1]
                     for code in range(radical_count)]
    require(radical_count == 2 ** len(seeds) and radical_count <= MAX_RADICAL_ROWS,
            "selected radical row specification changed")
    radical_rows = []
    for letters in radical_words:
        value = identity
        for j in letters:
            value = mul(value, candidates[j])
        radical_rows.append(value)
    radical_index = {value: i for i, value in enumerate(radical_rows)}
    require(len(radical_index) == radical_count and set(radical_rows) <= set(rows),
            "radical witnesses repeat or escape original derived rows")

    inside, inside_code, all_words = [], [], []
    total_letters, depth_two_rows = 0, []
    for row_index, row in enumerate(rows):
        in_radical = row in radical_index
        inside.append(in_radical)
        inside_code.append(radical_index.get(row, 0))
        if in_radical:
            all_words.append([[] for _ in seeds])
            continue
        # Dictionary insertion order fixes the first shortest lexicographic
        # path for each value. Products then use this same deterministic order.
        path_values = {}
        first = []
        for i, generator in enumerate(generators):
            value = comm(row, generator)
            first.append(value)
            require(value in radical_index, "first commutator escaped displayed radical")
            path_values.setdefault(value, [i])
        for i, value in enumerate(first):
            for j, generator in enumerate(generators):
                following = comm(value, generator)
                require(following in radical_index, "second commutator escaped displayed radical")
                path_values.setdefault(following, [i, j])
        require(len(path_values) <= MAX_PATH_VALUES, "commutator-path state ceiling reached")
        recover = {identity: []}
        for value, path in path_values.items():
            recover.setdefault(value, [path])
        for left, left_path in path_values.items():
            for right, right_path in path_values.items():
                recover.setdefault(mul(left, right), [left_path, right_path])
        require(len(recover) <= MAX_RADICAL_ROWS and set(recover) <= set(radical_rows),
                "commutator-product state ceiling reached or escaped radical")
        words = []
        for candidate in candidates:
            require(candidate in recover, f"depth/product bounds cannot recover radical seed at row{row_index}")
            word = recover[candidate]
            require(len(word) <= MAX_PRODUCT_LENGTH and all(1 <= len(w) <= MAX_PATH_DEPTH for w in word),
                    "selected saturation word ceiling reached")
            value = identity
            for path in word:
                path_value = row
                for j in path:
                    path_value = comm(path_value, generators[j])
                value = mul(value, path_value)
            require(value == candidate, "selected saturation witness evaluation mismatch")
            total_letters += sum(map(len, word))
            require(total_letters <= MAX_TOTAL_WITNESS_LETTERS, "total saturation letters ceiling reached")
            words.append(word)
        if any(len(path) == 2 for word in words for path in word):
            depth_two_rows.append(row_index)
        all_words.append(words)
    budget.time_check()
    return dict(inside=inside, inside_code=inside_code, words=all_words,
                radical_words=radical_words, total_letters=total_letters,
                depth_two_rows=depth_two_rows, seed_count=len(seeds), radical_count=radical_count)


def vector(values: list[str], per_line: int = 4) -> str:
    require(bool(values), "empty vector unsupported")
    return "![" + ",\n    ".join(",".join(values[i:i + per_line]) for i in range(0, len(values), per_line)) + "]"


def nat_list(values) -> str:
    return "[" + ",".join(map(str, values)) + "]"


def split_decide(name: str, size: int, proposition) -> str:
    """Separate at most8 literal rows per theorem; preserve Fin cast terms."""
    declarations = []

    def branch(count: int, embed) -> str:
        if count <= 8:
            leaf = f"{name}_{len(declarations):03d}"
            declarations.append(f"private theorem {leaf} : ∀ i : Fin {count},\n"
                                f"    {proposition(embed('i'))} := by\n  decide +kernel\n\n")
            return leaf
        left, right = count // 2, count - count // 2
        lhs = branch(left, lambda i: embed(f"(Fin.castAdd {right} {i})"))
        rhs = branch(right, lambda i: embed(f"(Fin.natAdd {left} {i})"))
        return f"(Fin.addCases (m := {left}) (n := {right}) {lhs} {rhs})"

    assembled = branch(size, lambda i: i)
    return "".join(declarations) + (f"private theorem {name} : ∀ i : Fin {size},\n"
                                   f"    {proposition('i')} :=\n  {assembled}\n")


TEMPLATE = r'''import SymmetricSubgroupAsymptotics.NormalSubgroupSaturationCommutators
import SymmetricSubgroupAsymptotics.BinaryCarrierDerivedRadical16T@MASTER@

/-! Selected saturation by actual iterated commutators in the original
16T@MASTER@ action. Every original derived row outside its relative radical
recovers every displayed radical generator. No normal-subgroup list or
intrinsic-only conjugation action is substituted. Generated by the bounded
selected export_lean_carrier_saturation.py producer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.BinaryCarrierRadicalSaturation16T@MASTER@

abbrev Original := BinaryCarrierDerivedOrder16T@MASTER@.Original
private abbrev D := commutator Original
private abbrev R := primeRelativeRadical 2 D
private abbrev g := BinaryActionData16.node@MASTER@Generators
private abbrev ambient := closureGenerators g
private abbrev basisWords := BinaryCarrierDerivedOrder16T@MASTER@.basisWords
private abbrev basis := derivedWordGenerators g basisWords
private abbrev rows := BinaryCarrierDerivedOrder16T@MASTER@.certificate.cayley.elements
private abbrev ambientRows := BinaryCarrierDerivedOrder16T@MASTER@.ambientRows

private def ambientBasis (j : Fin @BASIS@) : Equiv.Perm (Fin 16) := (basisWords j).eval g
private def seed : Fin @SEEDS@ → Fin @BASIS@ ⊕ (Fin @BASIS@ × Fin @GENERATORS@) :=
  @SEED_VALUES@
private def candidate (j : Fin @SEEDS@) : Original :=
  primeRelativeFiniteGenerators 2 ambient basis (seed j)
private def ambientCandidate (j : Fin @SEEDS@) : Equiv.Perm (Fin 16) :=
  primeRelativeFiniteGenerators 2 g ambientBasis (seed j)
private def radicalWords : Fin @RADICAL_ROWS@ → List (Fin @SEEDS@) :=
  @RADICAL_WORDS@
private def radicalRows (i : Fin @RADICAL_ROWS@) : Original :=
  ((radicalWords i).map candidate).prod
private def ambientRadicalRows (i : Fin @RADICAL_ROWS@) : Equiv.Perm (Fin 16) :=
  ((radicalWords i).map ambientCandidate).prod
private def inside : Fin @ROWS@ → Bool := @INSIDE@
private def insideCode : Fin @ROWS@ → Fin @RADICAL_ROWS@ := @INSIDE_CODE@
private def saturationWords (i : Fin @ROWS@) (j : Fin @SEEDS@) : List (List (Fin @GENERATORS@)) :=
  @WORDS@ i j

private theorem candidate_coe (j : Fin @SEEDS@) :
    (candidate j : Equiv.Perm (Fin 16)) = ambientCandidate j := by
  cases hs : seed j with
  | inl k =>
    change ((primeRelativeFiniteGenerators 2 ambient basis (seed j) : Original) : Equiv.Perm (Fin 16)) = _
    simp only [hs, primeRelativeFiniteGenerators, Sum.elim_inl, ambientCandidate]
    change (basis k : Equiv.Perm (Fin 16)) ^ 2 = ambientBasis k ^ 2
    rw [show (basis k : Equiv.Perm (Fin 16)) = ambientBasis k from
      closureGenerators_eval_coe g (basisWords k)]
  | inr ki =>
    change ((primeRelativeFiniteGenerators 2 ambient basis (seed j) : Original) : Equiv.Perm (Fin 16)) = _
    simp only [hs, primeRelativeFiniteGenerators, Sum.elim_inr, ambientCandidate]
    change ⁅(basis ki.1 : Equiv.Perm (Fin 16)), g ki.2⁆ = ⁅ambientBasis ki.1, g ki.2⁆
    rw [show (basis ki.1 : Equiv.Perm (Fin 16)) = ambientBasis ki.1 from
      closureGenerators_eval_coe g (basisWords ki.1)]

private theorem radicalRows_coe (i : Fin @RADICAL_ROWS@) :
    (radicalRows i : Equiv.Perm (Fin 16)) = ambientRadicalRows i := by
  change Original.subtype (((radicalWords i).map candidate).prod) = _
  have hf : Original.subtype ∘ candidate = ambientCandidate := funext candidate_coe
  rw [map_list_prod, List.map_map, hf]
  rfl

private theorem rows_coe (i : Fin @ROWS@) :
    (rows i : Equiv.Perm (Fin 16)) = ambientRows i :=
  BinaryCarrierDerivedOrder16T@MASTER@.certificate_elements_coe i

private theorem radicalRows_injective_pointwise : ∀ i j : Fin @RADICAL_ROWS@,
    (∀ x : Fin 16, ambientRadicalRows i x = ambientRadicalRows j x) → i = j := by
  decide +kernel

@INSIDE_CHECK@

@WORD_CHECK@

private theorem candidate_mem (j : Fin @SEEDS@) : candidate j ∈ R :=
  primeRelativeFiniteGenerators_mem 2 D ambient basis
    BinaryCarrierDerivedOrder16T@MASTER@.certificate.subgroup_eq_commutator (seed j)

private theorem radicalRows_mem_closure (i : Fin @RADICAL_ROWS@) :
    radicalRows i ∈ Subgroup.closure (Set.range candidate) := by
  apply (Subgroup.closure (Set.range candidate)).list_prod_mem
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  exact Subgroup.subset_closure (Set.mem_range_self j)

private theorem radicalRows_injective : Function.Injective radicalRows := by
  intro i j h
  apply radicalRows_injective_pointwise i j
  intro x
  have he := congrArg (fun z : Original => (z : Equiv.Perm (Fin 16)) x) h
  simpa only [radicalRows_coe] using he

/-- Actual relative-radical equality uses its checked cardinality and
distinct original rows, rather than assuming the candidate is normal. -/
private theorem candidate_full : Subgroup.closure (Set.range candidate) = R := by
  have hle : Subgroup.closure (Set.range candidate) ≤ R := by
    apply (Subgroup.closure_le R).mpr
    rintro _ ⟨j, rfl⟩
    exact candidate_mem j
  apply Subgroup.eq_of_le_of_card_ge hle
  let f : Fin @RADICAL_ROWS@ → Subgroup.closure (Set.range candidate) :=
    fun i => ⟨radicalRows i, radicalRows_mem_closure i⟩
  have hf : Function.Injective f := by
    intro i j h
    exact radicalRows_injective (congrArg Subtype.val h)
  have hc := Nat.card_le_card_of_injective f hf
  rw [BinaryCarrierDerivedRadical16T@MASTER@.card_relative_radical]
  simpa only [Nat.card_fin] using hc

def certificate : NormalSubgroupSaturationCertificate D R ambient candidate @ROWS@ where
  radical_le := primeRelativeRadical_le 2 D
  radical_full := candidate_full
  rows := rows
  rows_mem := by
    intro i
    have hd := BinaryCarrierDerivedOrder16T@MASTER@.certificate.subgroup_eq_commutator
    change Subgroup.closure (Set.range basis) = D at hd
    have hm : rows i ∈ Subgroup.closure (Set.range basis) :=
      (BinaryCarrierDerivedOrder16T@MASTER@.certificate.cayley.mem_closure_iff _).mpr ⟨i, rfl⟩
    exact hd ▸ hm
  rows_cover := by
    intro x hx
    have hd := BinaryCarrierDerivedOrder16T@MASTER@.certificate.subgroup_eq_commutator
    change Subgroup.closure (Set.range basis) = D at hd
    rw [← hd] at hx
    exact (BinaryCarrierDerivedOrder16T@MASTER@.certificate.cayley.mem_closure_iff x).mp hx
  inside := inside
  inside_mem := by
    intro i hi
    have he : rows i = radicalRows (insideCode i) := by
      apply Subtype.ext
      rw [rows_coe, radicalRows_coe]
      exact Equiv.ext (inside_pointwise i hi)
    rw [he, ← candidate_full]
    exact radicalRows_mem_closure _
  words := saturationWords
  words_eq := by
    intro i hi j
    apply Subtype.ext
    change Original.subtype (originalCommutatorProduct ambient (rows i) (saturationWords i j)) =
      (candidate j : Equiv.Perm (Fin 16))
    rw [map_originalCommutatorProduct]
    change originalCommutatorProduct g (rows i : Equiv.Perm (Fin 16)) (saturationWords i j) = _
    rw [rows_coe, candidate_coe]
    exact Equiv.ext (words_pointwise i hi j)

/-- Every selected path begins with a genuine original commutator. -/
theorem nonempty_words : certificate.NonemptyWords := by
  change ∀ i : Fin @ROWS@, inside i = false → ∀ j : Fin @SEEDS@,
    ∀ w ∈ saturationWords i j, w ≠ []
  decide +kernel

/-- All normals use conjugation by the whole literal original action. -/
theorem normal_comparable (B : Subgroup Original) [B.Normal] (hBD : B ≤ commutator Original) :
    B ≤ primeRelativeRadical 2 (commutator Original) ∨
      primeRelativeRadical 2 (commutator Original) ≤ B :=
  certificate.comparable B hBD

end SymmetricSubgroupAsymptotics.BinaryCarrierRadicalSaturation16T@MASTER@
'''


def emit(master: int, generator_count: int, data: dict, result: dict) -> bytes:
    rows, radical_rows, seeds = SPECS[master]
    require(len(data["rows"]) == rows and len(result["words"]) == rows,
            "emitter row count mismatch")
    words = [vector(["[" + ",".join(nat_list(path) for path in word) + "]" for word in row],
                    len(seeds)) for row in result["words"]]
    replacements = {
        "MASTER": str(master), "ROWS": str(rows), "RADICAL_ROWS": str(radical_rows),
        "GENERATORS": str(generator_count), "BASIS": str(data["basis_count"]), "SEEDS": str(len(seeds)),
        "SEED_VALUES": vector([f".inl {s[1]}" if s[0] == "pow" else f".inr ({s[1]},{s[2]})"
                               for s in seeds]),
        "RADICAL_WORDS": vector([nat_list(w) for w in result["radical_words"]]),
        "INSIDE": vector(["true" if b else "false" for b in result["inside"]], 8),
        "INSIDE_CODE": vector([str(i) for i in result["inside_code"]], 8),
        "WORDS": vector(words, 2),
        "INSIDE_CHECK": split_decide("inside_pointwise", rows, lambda i:
            f"inside {i} = true → ∀ x : Fin 16,\n"
            f"      ambientRows {i} x = ambientRadicalRows (insideCode {i}) x"),
        "WORD_CHECK": split_decide("words_pointwise", rows, lambda i:
            f"inside {i} = false → ∀ (j : Fin {len(seeds)}) (x : Fin 16),\n"
            f"      originalCommutatorProduct g (ambientRows {i}) (saturationWords {i} j) x =\n"
            f"        ambientCandidate j x"),
    }
    text = TEMPLATE
    for token, value in replacements.items():
        text = text.replace(f"@{token}@", value)
    require("@" not in text, "unexpanded template token")
    content = text.encode("utf-8")
    require(len(content) <= MAX_OUTPUT_BYTES, "Lean output byte ceiling reached")
    return content


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--master", type=int, required=True, choices=SPECS)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--write", action="store_true")
    modes.add_argument("--check", action="store_true")
    parser.add_argument("--report", type=Path)
    parser.add_argument("--max-rows", type=int, default=MAX_ROWS)
    parser.add_argument("--max-operations", type=int, default=MAX_OPERATIONS)
    parser.add_argument("--seconds", type=float, default=MAX_SECONDS)
    args = parser.parse_args()
    if not (1 <= args.max_rows <= MAX_ROWS and 1 <= args.max_operations <= MAX_OPERATIONS
            and math.isfinite(args.seconds) and 0 < args.seconds <= MAX_SECONDS):
        parser.error("immutable ceilings:64 derived rows,100000 operations,5 seconds")
    require(not (args.check and args.report is not None), "--check cannot write a report")
    report_path = None
    if args.report is not None:
        require(not args.report.is_symlink(), "report must not be a symlink")
        report_path = args.report.resolve()
        require(not report_path.is_relative_to(ROOT) and report_path.suffix == ".json"
                and report_path.parent.is_dir(), "report must be an external .json in an existing directory")
    require(OUT.resolve().is_relative_to(ROOT), "canonical output directory escapes publication")
    target = OUT / f"BinaryCarrierRadicalSaturation16T{args.master}.lean"
    require(not target.is_symlink(), "canonical output must not be a symlink")
    budget = square.Budget(args.max_rows, args.max_operations, args.seconds, time.monotonic())
    generators, snapshots = square.selected_generators(args.master)
    for path in (Path(__file__).resolve(), Path(square.__file__).resolve(),
                 OUT / f"BinaryCarrierDerivedOrder16T{args.master}.lean",
                 OUT / f"BinaryCarrierDerivedRadical16T{args.master}.lean",
                 OUT / "NormalSubgroupSaturationCertificate.lean",
                 OUT / "NormalSubgroupSaturationCommutators.lean"):
        require(not path.is_symlink(), "producer/dependency source must not be a symlink")
        snapshots[path] = square.bounded_read(path)
        require(len(snapshots[path]) <= MAX_SOURCE_BYTES, "selected source byte ceiling reached")
    derived_path = OUT / f"BinaryCarrierDerivedOrder16T{args.master}.lean"
    data = load_rows(args.master, generators, snapshots[derived_path], budget)
    result = saturation(args.master, generators, data, budget)
    content = emit(args.master, len(generators), data, result)
    summary = dict(master=args.master, derived_rows=len(data["rows"]), radical_rows=result["radical_count"],
                   outside_rows=sum(not b for b in result["inside"]),
                   depth_two_rows=result["depth_two_rows"], witness_letters=result["total_letters"],
                   operations=budget.operations, seconds=time.monotonic() - budget.start,
                   module=str(target.relative_to(ROOT)), module_sha256=hashlib.sha256(content).hexdigest(),
                   checked_bytes=args.check, write_requested=args.write)
    report_content = None
    if report_path is not None:
        report = {**summary, "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(b).hexdigest()
                                              for p, b in snapshots.items()},
                  "limits": {"rows": args.max_rows, "radical_rows": MAX_RADICAL_ROWS,
                             "path_depth": MAX_PATH_DEPTH, "product_length": MAX_PRODUCT_LENGTH,
                             "path_states": MAX_PATH_VALUES, "total_letters": MAX_TOTAL_WITNESS_LETTERS,
                             "operations": args.max_operations, "seconds": args.seconds,
                             "output_bytes": MAX_OUTPUT_BYTES},
                  "witnesses": result,
                  "scope": "Untrusted selected original commutator witnesses; Lean checking required. "
                           "No normal enumeration, original action replacement, or full carrier-row claim."}
        report_content = (json.dumps(report, indent=2) + "\n").encode("utf-8")
        require(len(report_content) <= MAX_REPORT_BYTES, "private report byte ceiling reached")
    for path, snapshot in snapshots.items():
        require(square.bounded_read(path) == snapshot, "input changed during production")
    budget.time_check()
    if args.check:
        require(target.is_file() and square.bounded_read(target) == content,
                "selected canonical Lean bytes differ")
    elif args.write:
        if not target.is_file() or square.bounded_read(target) != content:
            square.atomic_write(target, content)
    if report_content is not None:
        square.atomic_write(report_path, report_content)
    print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (square.CertificateError, OSError, UnicodeError, RecursionError,
            json.JSONDecodeError, SyntaxError) as error:
        print(f"selected carrier saturation: {error}", file=sys.stderr)
        raise SystemExit(2)
