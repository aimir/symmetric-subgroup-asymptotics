#!/usr/bin/env python3
"""Emit only the selected J=8T27 actual normal-head maximum bindings.

Read the accepted 13 complete normal-row definitions and actual headRank
definition, with bounded input and a strict tiny numeral/if parser. There is
no group search, normal enumeration, compressed data read, or stored profile
input. The generated Lean proof independently computes every containment
from Derived.normalMask and consumes Derived.source_derived_eq, registry
completeness, and the actual whole-ambient head equations.

The selected Derived source is explicit through --derived-sha256, allowing
this stage to follow its separately checked literal derived certificate.
--check is read-only. --write atomically replaces only HeadMaxima.lean after
all inputs and bounds have been checked. Bounds are cooperative operation/
time and fixed input/state/output bounds, not hard RSS limits.
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
SELECTED = ROOT / "formal/SymmetricSubgroupAsymptotics/GeneratedCarrierNormal8T27"
OUTPUT = SELECTED / "HeadMaxima.lean"
PINNED = {
    "States.lean": "e5679bf32d0ba049a7296db3cb3b95dc9b09de5c213054b9ec98fb41c5be8468",
    "Registry.lean": "0dfbe63775394a33409287319029dd73434dda6c8755ec874dc83bbc58ea2223",
    "RadicalProfiles.lean": "43d11f5d560714dd0f179e8c8fe3a9dae004251e23ce546daea291e51cdfae58",
}
MAX_INPUT_BYTES = 1048576
MAX_OUTPUT_BYTES = 262144
MAX_OPERATIONS = 200000
MAX_SECONDS = 30.0
MAX_TOKENS = 4096
MAX_DEPTH = 64
NAMESPACE = "SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T27"


class Rejected(ValueError):
    pass


class Budget:
    def __init__(self, operations: int, seconds: float):
        self.limit = operations
        self.seconds = seconds
        self.started = time.monotonic()
        self.operations = 0

    def tick(self):
        self.operations += 1
        if self.operations > self.limit:
            raise Rejected("selected operation cap exceeded")
        if time.monotonic() - self.started > self.seconds:
            raise Rejected("selected cooperative time cap exceeded")


def digest(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def read_bounded(path: Path, limit: int) -> bytes:
    with path.open("rb") as stream:
        payload = stream.read(limit + 1)
    if len(payload) > limit:
        raise Rejected(f"input-byte cap exceeded: {path.name}")
    return payload


def prerequisites(derived_sha256: str, budget: Budget):
    expected = {**PINNED, "Derived.lean": derived_sha256}
    result = {}
    total = 0
    for name, sha in expected.items():
        budget.tick()
        payload = read_bounded(SELECTED / name, MAX_INPUT_BYTES - total)
        total += len(payload)
        if digest(payload) != sha:
            raise Rejected(f"selected prerequisite changed: {name}")
        result[name] = payload
    return result, total


class NumeralLookup:
    """Parse only the existing balanced lookup grammar, never Python/Lean eval."""

    def __init__(self, text: str, budget: Budget):
        pattern = r"i\.val|if|then|else|Fin|[0-9]+|[():<]"
        self.tokens = re.findall(pattern, text)
        if re.sub(r"\s+", "", text) != "".join(self.tokens):
            raise Rejected("unrecognized selected lookup syntax")
        if len(self.tokens) > MAX_TOKENS:
            raise Rejected("selected lookup token cap exceeded")
        self.position = 0
        self.budget = budget
        self.tree = self.expression(0)
        if self.position != len(self.tokens):
            raise Rejected("trailing selected lookup tokens")

    def pop(self, expected=None):
        self.budget.tick()
        if self.position >= len(self.tokens):
            raise Rejected("truncated selected lookup")
        value = self.tokens[self.position]
        self.position += 1
        if expected is not None and value != expected:
            raise Rejected("malformed selected lookup")
        return value

    def natural(self):
        value = self.pop()
        if not value.isdecimal() or len(value) > 3:
            raise Rejected("selected lookup numeral out of bounds")
        return int(value)

    def expression(self, depth):
        if depth > MAX_DEPTH:
            raise Rejected("selected lookup depth cap exceeded")
        first = self.pop()
        if first == "(":
            tree = self.expression(depth + 1)
            if self.position < len(self.tokens) and self.tokens[self.position] == ":":
                self.pop(":")
                self.pop("Fin")
                if self.natural() != 64:
                    raise Rejected("unexpected selected row type")
            self.pop(")")
            return tree
        if first == "if":
            self.pop("i.val")
            self.pop("<")
            split = self.natural()
            self.pop("then")
            left = self.expression(depth + 1)
            self.pop("else")
            right = self.expression(depth + 1)
            return (split, left, right)
        if first.isdecimal() and len(first) <= 3:
            return int(first)
        raise Rejected("selected lookup must contain only numeral leaves")

    def value(self, index):
        tree = self.tree
        while isinstance(tree, tuple):
            self.budget.tick()
            split, left, right = tree
            tree = left if index < split else right
        self.budget.tick()
        return tree


def selected_values(inputs, budget):
    text = inputs["States.lean"].decode("utf-8")
    blocks = list(re.finditer(r"^namespace N([0-9]+)\n(.*?)^end N\1$", text,
                              re.MULTILINE | re.DOTALL))
    if [int(m.group(1)) for m in blocks] != list(range(13)):
        raise Rejected("expected exactly the 13 original state namespaces")
    normals = []
    for block in blocks:
        budget.tick()
        row_defs = re.findall(r"^private def rows \(i : Fin ([0-9]+)\) : Fin 64 := (.+)$",
                              block.group(2), re.MULTILINE)
        if len(row_defs) != 1:
            raise Rejected("missing or repeated complete state-row definition")
        count, expression = row_defs[0]
        count = int(count)
        if not 1 <= count <= 64:
            raise Rejected("selected state-row cap exceeded")
        lookup = NumeralLookup(expression, budget)
        rows = [lookup.value(i) for i in range(count)]
        if len(set(rows)) != count or any(not 0 <= x < 64 for x in rows):
            raise Rejected("selected complete row codes are not distinct Fin64 values")
        normals.append(frozenset(rows))
    if sum(map(len, normals)) > 13 * 64:
        raise Rejected("selected total normal-row cap exceeded")
    profiles = inputs["RadicalProfiles.lean"].decode("utf-8")
    head_defs = re.findall(r"^def headRank \(i : Fin 13\) : ℕ := (.+)$", profiles,
                           re.MULTILINE)
    if len(head_defs) != 1:
        raise Rejected("missing or repeated actual headRank definition")
    lookup = NumeralLookup(head_defs[0], budget)
    heads = [lookup.value(i) for i in range(13)]
    if any(not 0 <= h <= 6 for h in heads):
        raise Rejected("selected actual head value out of bounds")
    maxima = []
    containments = []
    for target in range(13):
        eligible = []
        for j in range(13):
            budget.tick()
            if normals[j] <= normals[target] and normals[j] <= normals[4]:
                eligible.append(j)
        maxima.append(max((heads[j] for j in eligible), default=0))
        containments.append(eligible)
    return maxima, heads, containments


def lean_lookup(values, start=0):
    if len(values) == 1:
        return str(values[0])
    middle = len(values) // 2
    return (f"(if i.val < {start + middle} then {lean_lookup(values[:middle], start)} "
            f"else {lean_lookup(values[middle:], start + middle)})")


def emit(maxima):
    return f'''import SymmetricSubgroupAsymptotics.BinaryNormalRegistryHeads
import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T27.Derived
import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T27.RadicalProfiles

/-! Actual m-values for the complete literal J=8T27 normal registry.
Generated only by export_lean_carrier_j_heads.py. Every head and containment
is bound to an original subgroup; no stored carrier profile is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace {NAMESPACE}
local instance headMaximaSourceGroup : Group Source := BinaryMenuCayley8T27.group

/-- Containment is computed from the checked complete original element masks. -/
def normalBelow (j i : Fin 13) : Bool :=
  decide (∀ x : Fin 64, normalMask j x = true → normalMask i x = true)

theorem normalBelow_iff (j i : Fin 13) :
    normalBelow j i = true ↔ (states j).kernel ≤ (states i).kernel := by
  simp only [normalBelow, decide_eq_true_eq]
  constructor
  · intro h x hx
    exact (normalMask_mem i x).mp (h x.index ((normalMask_mem j x).mpr hx))
  · intro h x hx
    exact (normalMask_mem i (⟨x⟩ : Source)).mpr
      (h ((normalMask_mem j (⟨x⟩ : Source)).mp hx))

def normalInDerived (j : Fin 13) : Bool := normalBelow j 4

theorem normalInDerived_iff (j : Fin 13) :
    normalInDerived j = true ↔ (states j).kernel ≤ commutator Source := by
  change normalBelow j 4 = true ↔ (states j).kernel ≤ commutator Source
  simpa only [source_derived_eq] using normalBelow_iff j 4

/-- The finite maximum of proved heads below N and the actual derived subgroup. -/
def derivedHeadRank (i : Fin 13) : ℕ := {lean_lookup(maxima)}

private theorem derivedHeadRank_checked : ∀ i : Fin 13,
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j i && normalInDerived j) = derivedHeadRank i := by
  intro i
  fin_cases i <;> decide +kernel

theorem state_derived_head_eq (i : Fin 13) :
    primeNormalHeadMax 2 ((states i).kernel ⊓ commutator Source) = derivedHeadRank i :=
  registry.axisNormalHeadMax_eq_of_finiteMaximum source_isPGroup 2
    headRank state_head_eq normalBelow normalBelow_iff normalInDerived
    normalInDerived_iff derivedHeadRank derivedHeadRank_checked i

/-- The same m-value concerns the original literal Fin8 action and all of its
ambient-normal subgroups, transported by its specified source equivalence. -/
theorem original_derived_head_eq (i : Fin 13) :
    primeNormalHeadMax 2 (originalKernel i ⊓ commutator Original) = derivedHeadRank i :=
  (registry.axisNormalHeadMax_map_eq_finiteMaximum source_isPGroup 2
    BinaryMenuCayley8T27.originalEquiv headRank original_head_eq normalBelow
    normalBelow_iff normalInDerived normalInDerived_iff i).trans
      (derivedHeadRank_checked i)

theorem complete_original_head_maxima (N : Subgroup Original) [N.Normal] :
    ∃ i : Fin 13, originalKernel i = N ∧
      primeNormalHeadMax 2 (N ⊓ commutator Original) = derivedHeadRank i := by
  obtain ⟨i, hi⟩ := complete_original N
  change originalKernel i = N at hi
  subst N
  exact ⟨i, rfl, original_derived_head_eq i⟩

end {NAMESPACE}
'''


def atomic_write(path: Path, payload: bytes):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(payload)
        os.replace(temporary, path)
        temporary = None
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--master", choices=["8T27"], required=True)
    parser.add_argument("--derived-sha256", required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--max-rows", type=int, default=64)
    parser.add_argument("--max-states", type=int, default=13)
    parser.add_argument("--max-operations", type=int, default=100000)
    parser.add_argument("--max-seconds", type=float, default=10.0)
    parser.add_argument("--max-output-bytes", type=int, default=65536)
    parser.add_argument("--private-report", type=Path)
    args = parser.parse_args()
    if re.fullmatch(r"[0-9a-f]{64}", args.derived_sha256) is None:
        parser.error("derived-sha256 must be the selected checked Derived source SHA256")
    if args.max_rows != 64 or args.max_states != 13:
        parser.error("this selected certificate requires exactly64 rows and13 states")
    if not 1 <= args.max_operations <= MAX_OPERATIONS:
        parser.error("max-operations must be in [1,200000]")
    if not math.isfinite(args.max_seconds) or not 0 < args.max_seconds <= MAX_SECONDS:
        parser.error("max-seconds must be finite and in (0,30]")
    if not 1 <= args.max_output_bytes <= MAX_OUTPUT_BYTES:
        parser.error("max-output-bytes must be in [1,262144]")
    if args.check and args.private_report is not None:
        parser.error("--check is read-only and cannot write a report")
    report_output_path = None
    if args.private_report is not None:
        report_output_path = args.private_report.resolve()
        private_root = (ROOT.parent / "private_audits").resolve()
        if not report_output_path.is_relative_to(private_root) or report_output_path == private_root:
            parser.error("reports must be files under private_audits")
    budget = Budget(args.max_operations, args.max_seconds)
    inputs, input_bytes = prerequisites(args.derived_sha256, budget)
    maxima, heads, eligible = selected_values(inputs, budget)
    payload = emit(maxima).encode("utf-8")
    if len(payload) > args.max_output_bytes:
        raise Rejected("selected output-byte cap exceeded")
    # Complete validation precedes the only public write; also reject concurrent changes.
    current, _ = prerequisites(args.derived_sha256, budget)
    if current != inputs:
        raise Rejected("selected prerequisite changed during preparation")
    budget.tick()
    if args.check:
        if read_bounded(OUTPUT, MAX_OUTPUT_BYTES) != payload:
            raise Rejected("selected HeadMaxima source does not match deterministic output")
    else:
        atomic_write(OUTPUT, payload)
    report = {
        "master": "8T27", "stage": "actual normal-head maxima",
        "source_rows": 64, "normal_states": 13,
        "actual_head_ranks": heads, "derived_head_ranks": maxima,
        "eligible_original_state_indices_zero_based": eligible,
        "input_bytes": input_bytes, "output_bytes": len(payload),
        "operations": budget.operations,
        "prerequisites": {name: digest(data) for name, data in inputs.items()},
        "output": str(OUTPUT.relative_to(ROOT)), "output_sha256": digest(payload),
        "group_search": False, "normal_enumeration": False,
        "stored_profile_fields_used": False, "lean_status": "pending root check",
        "mode": "check" if args.check else "write",
    }
    if report_output_path is not None:
        atomic_write(report_output_path, (json.dumps(report, indent=2) + "\n").encode())
    print(json.dumps(report, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (Rejected, OSError, UnicodeError, ValueError) as error:
        raise SystemExit(str(error)) from error
