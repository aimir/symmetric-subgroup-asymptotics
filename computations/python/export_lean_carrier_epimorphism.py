#!/usr/bin/env python3
"""Prepare exactly one selected literal P=8T35 carrier epimorphism.

This producer reads only pinned public source/data files. It performs no
group search, Cayley enumeration, normal enumeration, subprocess, or network
operation. The generated Lean proof evaluates the already certified source
parent words and independently checks all original generator transitions,
image membership and original target-generator preimages using the kernel.

Both --source and --target, and exactly one of --write/--check, are required.
The three P routes are opt-in; there is no batch or all-target mode. --write
atomically installs only its canonical selected source after validation;
--check is read-only and compares exact bytes. Resource bounds are fixed
input/row/generator/output caps and cooperative operation/time bounds, not
an operating-system RSS limit or a Lean compiler limit.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
import tempfile
import time


ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "formal/SymmetricSubgroupAsymptotics"
PINNED = {
    "certificates/data/base_alphabet.json":
        "6ca337237f79e09b1cf4d796b7fb543c9428aa99b0076cce4d6febb2d33275da",
    "certificates/data/carrier_master_maps.json":
        "941fb087c5765a9fdfa824069aca9952f70ad21fa15b432649e7ab2b96265be3",
    "formal/SymmetricSubgroupAsymptotics/FiniteCayleyMaps.lean":
        "0e3ae5dee2261211d51eeb7d576e0bfb6dc3f49bd0ecf3ba7a031fdbb020c3ee",
    "formal/SymmetricSubgroupAsymptotics/BinaryMenuCayley8T35.lean":
        "76a5f90545ba67f4e69d7f81ad46418c85aa8d46e36b644fc1e544ab045d1d95",
    "formal/SymmetricSubgroupAsymptotics/BinaryMenuCayley8T18.lean":
        "2d673111c57de3d0a97b69e9487886808805db816574625b6d026ba9ab9a6c40",
    "formal/SymmetricSubgroupAsymptotics/BinaryMenuCayley8T29.lean":
        "f3dddab2331ab02382cca395a5b8743b8a1198e31907890a877a511eb673e9b4",
    "formal/SymmetricSubgroupAsymptotics/BinaryMenuCayley8T31.lean":
        "b1a2218fb13310d15f056b17a053a0e10ce2becc92f95c78a02d8d862b69ca04",
}
TARGETS = {"8T18": (32, 5), "8T29": (64, 5), "8T31": (64, 3)}
ROUTES = [("8T26", "8T26"), ("8T27", "8T27"), ("8T27", "8T28"),
          ("8T35", "8T18"), ("8T35", "8T29"), ("8T35", "8T31"),
          ("8T35", "8T35")]
MAX_INPUT_BYTES = 1_048_576
MAX_OUTPUT_BYTES = 262_144
MAX_OPERATIONS = 250_000
MAX_SECONDS = 30.0


class Rejected(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise Rejected(message)


class Budget:
    def __init__(self, operations, seconds):
        self.limit = operations
        self.seconds = seconds
        self.operations = 0
        self.started = time.monotonic()

    def tick(self):
        self.operations += 1
        require(self.operations <= self.limit, "selected operation cap exceeded")
        require(time.monotonic() - self.started <= self.seconds,
                "selected cooperative time cap exceeded")


def digest(payload):
    return hashlib.sha256(payload).hexdigest()


def read_bounded(path, limit):
    require(limit >= 0, "selected total input-byte cap exceeded")
    with path.open("rb") as stream:
        payload = stream.read(limit + 1)
    require(len(payload) <= limit, f"input-byte cap exceeded: {path.name}")
    return payload


def input_paths(source, target):
    return ["certificates/data/base_alphabet.json",
            "certificates/data/carrier_master_maps.json",
            "formal/SymmetricSubgroupAsymptotics/FiniteCayleyMaps.lean",
            f"formal/SymmetricSubgroupAsymptotics/BinaryMenuCayley{source}.lean",
            f"formal/SymmetricSubgroupAsymptotics/BinaryMenuCayley{target}.lean"]


def prerequisites(source, target, cap, budget):
    payloads = {}
    total = 0
    for relative in input_paths(source, target):
        budget.tick()
        payload = read_bounded(ROOT / relative, cap - total)
        total += len(payload)
        require(digest(payload) == PINNED[relative],
                f"pinned selected prerequisite changed: {relative}")
        payloads[relative] = payload
    return payloads, total


def permutation(values, one_based, budget):
    budget.tick()
    require(isinstance(values, list) and len(values) == 8,
            "selected permutation must have exactly eight original points")
    require(all(type(v) is int for v in values), "permutation entries must be integers")
    base = 1 if one_based else 0
    require(sorted(values) == list(range(base, base + 8)), "invalid selected permutation")
    return tuple(v - base for v in values)


def literal_tuple(text, expected_rows, expected_generators, budget):
    """Read fixed literal permutation arrays, never evaluate Lean/Python text."""
    budget.tick()
    rows = re.findall(r"^private def codes \(i : Fin ([0-9]+)\)", text, re.MULTILINE)
    require(rows == [str(expected_rows)], "unexpected original complete row type")
    chunks = re.findall(
        r"^private def generator([0-9]+) : Equiv\.Perm \(Fin 8\) where\n"
        r"  toFun x := \(#\[([0-9,]+)\] : Array \(Fin 8\)\)\[x\.val\]!\n",
        text, re.MULTILINE)
    require([int(i) for i, _ in chunks] == list(range(expected_generators)),
            "missing, duplicate or reordered original generator definitions")
    generators = []
    for _, images in chunks:
        generators.append(permutation([int(x) for x in images.split(",")], False, budget))
    dispatch = re.findall(
        r"^def generators \(j : Fin ([0-9]+)\) : Equiv\.Perm \(Fin 8\) :=\n"
        r"  ([^\n]+)\n", text, re.MULTILINE)
    require(len(dispatch) == 1 and int(dispatch[0][0]) == expected_generators,
            "original generator tuple has unexpected arity")
    def ordered_dispatch(start, count):
        if count == 1:
            return f"generator{start}"
        left = count // 2
        return (f"(if j.val < {start + left} then {ordered_dispatch(start, left)} "
                f"else {ordered_dispatch(start + left, count - left)})")

    expected = ordered_dispatch(0, expected_generators)
    require(re.sub(r"\s+", "", dispatch[0][1]) == re.sub(r"\s+", "", expected),
            "original generator dispatch is not the pinned literal order")
    require(len(set(generators)) == expected_generators, "duplicate original generators")
    return generators


def selected_images(inputs, source, target, args, budget):
    source_rows, source_count = 128, 3
    target_rows, target_count = TARGETS[target]
    require(source_rows <= args.max_source_rows, "selected source row cap exceeded")
    require(target_rows <= args.max_target_rows, "selected target row cap exceeded")
    require(source_count <= args.max_generators, "selected source/image generator cap exceeded")
    require(target_count <= args.max_target_generators, "selected target generator cap exceeded")
    source_literal = literal_tuple(inputs[input_paths(source, target)[3]].decode("utf-8"),
                                   source_rows, source_count, budget)
    target_literal = literal_tuple(inputs[input_paths(source, target)[4]].decode("utf-8"),
                                   target_rows, target_count, budget)
    alphabet = json.loads(inputs["certificates/data/base_alphabet.json"])
    maps = json.loads(inputs["certificates/data/carrier_master_maps.json"])
    budget.tick()
    require(alphabet.get("schema_version") == 1, "unexpected alphabet schema")
    require(maps.get("schema_version") == 1 and maps.get("degree") == 8,
            "unexpected selected route schema/degree")
    routes = maps.get("routes", [])
    require([(r.get("source"), r.get("target")) for r in routes] == ROUTES,
            "fixed seven-route catalogue changed")
    selected = [r for r in routes if (r["source"], r["target"]) == (source, target)]
    require(len(selected) == 1, "missing or duplicate selected route")
    actions = alphabet.get("actions", [])
    source_actions = [a for a in actions if a.get("catalogue_locator") == [8, 35]]
    target_actions = [a for a in actions if a.get("catalogue_locator") == [8, int(target[2:])]]
    require(len(source_actions) == len(target_actions) == 1,
            "missing or duplicate original action")
    source_action, target_action = source_actions[0], target_actions[0]
    require(source_action["degree"] == target_action["degree"] == 8,
            "selected original physical degree changed")
    require(source_action["order"] == source_rows and target_action["order"] == target_rows,
            "recorded order disagrees with original checked row type")
    source_json = [permutation(g, True, budget) for g in source_action["generators"]]
    target_json = [permutation(g, True, budget) for g in target_action["generators"]]
    require(len(source_json) == source_count and len(target_json) == target_count,
            "original alphabet generator arity changed")
    require(len(set(source_json)) == source_count and set(source_literal) == set(source_json),
            "literal source generators differ from the original alphabet")
    require(len(set(target_json)) == target_count and set(target_literal) == set(target_json),
            "literal target generators differ from the original alphabet")
    images_json = [permutation(g, True, budget)
                   for g in selected[0]["source_generator_images"]]
    require(len(images_json) == source_count, "each original source generator needs one image")
    reorder = [source_json.index(g) for g in source_literal]
    require(reorder == [1, 2, 0], "selected P generator-order binding changed")
    return [images_json[j] for j in reorder], reorder, target_rows, target_count


def emit(source, target, images, target_rows, target_count, max_bytes, budget):
    src = f"BinaryMenuCayley{source}"
    tgt = f"BinaryMenuCayley{target}"
    namespace = f"BinaryCarrierEpimorphism{source}To{target[2:]}"
    parts = []
    total = 0

    def add(text):
        nonlocal total
        budget.tick()
        total += len(text.encode("utf-8"))
        require(total <= max_bytes, "selected output-byte cap exceeded")
        parts.append(text)

    add(f'''import SymmetricSubgroupAsymptotics.{src}
import SymmetricSubgroupAsymptotics.{tgt}
import SymmetricSubgroupAsymptotics.FiniteCayleyMaps

/-! A selected epimorphism between the literal original carrier actions.
Generated by export_lean_carrier_epimorphism.py for {source} -> {target} only.
The source image tuple is reordered by [1,2,0] from the committed JSON
to the exact original Lean tuple. Existing source parent words are evaluated
in Lean. All 128*3 transitions and all {target_count} original target-generator
preimages are checked; no normalizer or action-conjugacy claim is made. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.{namespace}

abbrev Source := Subgroup.closure (Set.range {src}.generators)
abbrev Target := Subgroup.closure (Set.range {tgt}.generators)

''')
    for j, perm in enumerate(images):
        inverse = [0] * 8
        for i, value in enumerate(perm):
            budget.tick()
            inverse[value] = i
        forward_text = ",".join(map(str, perm))
        inverse_text = ",".join(map(str, inverse))
        add(f'''private def image{j} : Equiv.Perm (Fin 8) where
  toFun x := (#[{forward_text}] : Array (Fin 8))[x.val]!
  invFun x := (#[{inverse_text}] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

''')
    add(f'''/-- Images of the complete original ordered source tuple. -/
def images (j : Fin 3) : Equiv.Perm (Fin 8) :=
  if j.val = 0 then image0 else if j.val = 1 then image1 else image2

/-- Evaluate only the already certified source parent word. -/
def values (i : Fin 128) : Equiv.Perm (Fin 8) :=
  (({src}.certificate.words i).map images).prod

private theorem images_mem : ∀ j : Fin 3, images j ∈ Target := by
  intro j
  apply ({tgt}.certificate.mem_closure_iff (images j)).mpr
  exact (by
    decide +kernel :
    ∀ j : Fin 3, ∃ i : Fin {target_rows},
      {tgt}.certificate.rows i = permutationCode (images j)) j

private theorem values_mem (i : Fin 128) : values i ∈ Target := by
  apply Subgroup.list_prod_mem
  intro y hy
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
  exact images_mem j

private theorem values_identity : values {src}.certificate.identity = 1 := by
  simp only [values, EncodedCayleyCertificate.words_identity,
    List.map_nil, List.prod_nil]

''')
    for chunk in range(16):
        offset = 8 * chunk
        add(f'''private theorem transition_{chunk} :
    ∀ i : Fin 8, ∀ j : Fin 3, ∀ x : Fin 8,
      values ({src}.certificate.next ⟨{offset} + i.val, by omega⟩ j) x =
      (values ⟨{offset} + i.val, by omega⟩ * images j) x := by
  decide +kernel

''')
    add(f'''private theorem transitions (i : Fin 128) (j : Fin 3) :
    values ({src}.certificate.next i j) = values i * images j := by
  apply Equiv.ext
  intro x
''')
    for chunk in range(15):
        offset = 8 * chunk
        add(f'''  by_cases h{chunk} : i.val < {offset + 8}
  · have hi : (⟨{offset} + (i.val - {offset}), by omega⟩ : Fin 128) = i := by
      apply Fin.ext
      change {offset} + (i.val - {offset}) = i.val
      omega
    simpa only [hi] using transition_{chunk} ⟨i.val - {offset}, by omega⟩ j x
''')
    add(f'''  have hi : (⟨120 + (i.val - 120), by omega⟩ : Fin 128) = i := by
    apply Fin.ext
    change 120 + (i.val - 120) = i.val
    omega
  simpa only [hi] using transition_15 ⟨i.val - 120, by omega⟩ j x

local instance : Group (FiniteGroupRow 128) := {src}.group

private def rowHom : FiniteGroupRow 128 →* Equiv.Perm (Fin 8) where
  toFun i := values i.index
  map_one' := values_identity
  map_mul' i j := by
    change values ({src}.certificate.walk i.index
      ({src}.certificate.words j.index)) = values i.index * values j.index
    exact {src}.certificate.values_walk values images transitions
      i.index ({src}.certificate.words j.index)

private def permutationHom : Source →* Equiv.Perm (Fin 8) :=
  rowHom.comp {src}.originalEquiv.symm.toMonoidHom

private theorem permutationHom_row (i : Fin 128) :
    permutationHom ({src}.originalEquiv ⟨i⟩) = values i := by
  change rowHom ({src}.originalEquiv.symm ({src}.originalEquiv ⟨i⟩)) = values i
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The target is the literal original closure, not an abstract replacement. -/
def hom : Source →* Target :=
  permutationHom.codRestrict Target (fun x =>
    values_mem ({src}.originalEquiv.symm x).index)

@[simp] theorem hom_row (i : Fin 128) :
    (hom ({src}.originalEquiv ⟨i⟩) : Equiv.Perm (Fin 8)) = values i :=
  permutationHom_row i

theorem hom_generator (j : Fin 3) :
    (hom ⟨{src}.generators j,
      Subgroup.subset_closure (Set.mem_range_self j)⟩ : Equiv.Perm (Fin 8)) =
      images j := by
  have he : {src}.originalEquiv
      ⟨{src}.certificate.next {src}.certificate.identity j⟩ =
      (⟨{src}.generators j,
        Subgroup.subset_closure (Set.mem_range_self j)⟩ : Source) := by
    apply Subtype.ext
    change {src}.certificate.toCayley.elements
      ({src}.certificate.toCayley.next {src}.certificate.toCayley.identity j) = _
    rw [{src}.certificate.toCayley.next_eq,
      {src}.certificate.toCayley.identity_eq, one_mul]
  rw [← he, hom_row, transitions, values_identity, one_mul]

private theorem target_generator_preimages :
    ∀ j : Fin {target_count}, ∃ i : Fin 128, ∀ x : Fin 8,
      values i x = {tgt}.generators j x := by
  decide +kernel

theorem hom_surjective : Function.Surjective hom := by
  have hrange : Target ≤ permutationHom.range := by
    apply (Subgroup.closure_le _).mpr
    rintro y ⟨j, rfl⟩
    obtain ⟨i, hi⟩ := target_generator_preimages j
    refine ⟨{src}.originalEquiv ⟨i⟩, ?_⟩
    exact (permutationHom_row i).trans (Equiv.ext hi)
  intro y
  obtain ⟨x, hx⟩ := hrange y.property
  exact ⟨x, Subtype.ext hx⟩

end SymmetricSubgroupAsymptotics.{namespace}
''')
    return "".join(parts).encode("utf-8")


def atomic_write(path, payload):
    require(path.parent.is_dir(), "selected output directory does not exist")
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", choices=["8T35"], required=True)
    parser.add_argument("--target", choices=list(TARGETS), required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--max-source-rows", type=int, default=128)
    parser.add_argument("--max-target-rows", type=int, default=128)
    parser.add_argument("--max-generators", type=int, default=3,
                        help="original source/image tuple cap")
    parser.add_argument("--max-target-generators", type=int, default=5)
    parser.add_argument("--max-input-bytes", type=int, default=MAX_INPUT_BYTES)
    parser.add_argument("--max-output-bytes", type=int, default=65536)
    parser.add_argument("--max-operations", type=int, default=100000)
    parser.add_argument("--max-seconds", type=float, default=10.0)
    parser.add_argument("--private-report", type=Path)
    args = parser.parse_args()
    for key, ceiling in [("max_source_rows", 128), ("max_target_rows", 128),
                         ("max_generators", 3), ("max_target_generators", 5),
                         ("max_input_bytes", MAX_INPUT_BYTES),
                         ("max_output_bytes", MAX_OUTPUT_BYTES),
                         ("max_operations", MAX_OPERATIONS)]:
        if not 1 <= getattr(args, key) <= ceiling:
            parser.error(f"{key.replace('_', '-')} must be in [1,{ceiling}]")
    if not math.isfinite(args.max_seconds) or not 0 < args.max_seconds <= MAX_SECONDS:
        parser.error("max-seconds must be finite and in (0,30]")
    if args.check and args.private_report:
        parser.error("--check is read-only and cannot write a report")
    report_output_path = args.private_report.resolve() if args.private_report else None
    if report_output_path is not None:
        if report_output_path.is_relative_to(ROOT) or not report_output_path.parent.is_dir():
            parser.error("report path must have an existing parent outside the repository")
    budget = Budget(args.max_operations, args.max_seconds)
    inputs, input_bytes = prerequisites(args.source, args.target, args.max_input_bytes, budget)
    images, reorder, target_rows, target_count = selected_images(
        inputs, args.source, args.target, args, budget)
    payload = emit(args.source, args.target, images, target_rows, target_count,
                   args.max_output_bytes, budget)
    output = LEAN / f"BinaryCarrierEpimorphism{args.source}To{args.target[2:]}.lean"
    require(not output.is_symlink(), "selected output must not be a symlink")
    for relative, expected in inputs.items():
        budget.tick()
        require(read_bounded(ROOT / relative, len(expected)) == expected,
                f"selected prerequisite changed during preparation: {relative}")
    report = {
        "schema": 1, "source": args.source, "target": args.target,
        "source_rows": 128, "target_rows": target_rows,
        "source_generators": 3, "target_generators": target_count,
        "lean_source_to_json_generator_order": reorder,
        "input_sha256": {p: digest(v) for p, v in inputs.items()},
        "input_bytes": input_bytes, "output": str(output.relative_to(ROOT)),
        "output_sha256": digest(payload), "output_bytes": len(payload),
        "group_search": False, "compiler_run": False,
    }
    report_payload = None
    if report_output_path is not None:
        require(report_output_path != output.resolve(), "report/output path collision")
        report_payload = (json.dumps(report, indent=2, sort_keys=True) + "\n").encode()
        require(len(report_payload) <= 16384, "private report-byte cap exceeded")
    budget.tick()
    if args.check:
        require(read_bounded(output, args.max_output_bytes) == payload,
                "selected generated bytes differ")
        budget.tick()
    else:
        atomic_write(output, payload)
        if report_output_path is not None:
            atomic_write(report_output_path, report_payload)
    print(json.dumps({"mode": "check" if args.check else "write",
                      "source": args.source, "target": args.target,
                      "output_sha256": digest(payload), "output_bytes": len(payload),
                      "operations": budget.operations}, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (Rejected, OSError, ValueError, KeyError, TypeError) as error:
        raise SystemExit(f"REJECTED: {error}")
