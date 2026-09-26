#!/usr/bin/env python3
"""Emit one bounded, explicitly selected literal carrier-normal registry.

The emitter is parameterized by a pinned source specification; the first
enabled pilot is X=8T26 only. P is deliberately not enabled before that
pilot is accepted. The committed normal tuples are certificates to verify,
not a trusted exhaustive list: completeness is derived in Lean from every
actual central-involution quotient row and its checked normal child.

No normal-subgroup search, catalogue traversal, compiler, or legacy main is
called. Literal original generator order is preserved. --check is read-only;
--write atomically replaces only this selected master's States/Registry.
Resource counters are cooperative bounds, not hard RSS/time guarantees.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import tempfile
import time

import export_lean_normal_registry as legacy


ROOT = Path(__file__).resolve().parents[2]
INPUT_BYTE_CEILING = 262144
OUTPUT_BYTE_CEILING = 4194304
OPERATION_CEILING = 1000000
SECONDS_CEILING = 60.0
SOURCE_ROW_CEILING = 128
NORMAL_STATE_CEILING = 28
GENERATOR_CEILING = 8
NORMAL_ROW_TOTAL_CEILING = 1024
QUOTIENT_ROW_TOTAL_CEILING = 1024


@dataclass(frozen=True)
class SelectedMaster:
    master: str
    order_log: int
    normal_count: int
    generator_count: int
    record_line: int
    record_sha256: str
    source_sha256: str

    @property
    def source_rows(self):
        return 2 ** self.order_log

    @property
    def source_module(self):
        return "BinaryMenuCayley" + self.master

    @property
    def namespace(self):
        return "SymmetricSubgroupAsymptotics.BinaryCarrierNormal" + self.master

    @property
    def output_directory(self):
        return ROOT / "formal/SymmetricSubgroupAsymptotics" / ("GeneratedCarrierNormal" + self.master)


# Admission is explicit. Adding another master requires its original-source
# receipt and a separately authorized selected pilot; there is no bulk mode.
SPECS = {
    "8T26": SelectedMaster(
        master="8T26", order_log=6, normal_count=27, generator_count=3, record_line=1,
        record_sha256="89feb301725e1593c82b11c7f57905689e158196d13fe63a5254e258d5c34043",
        source_sha256="dd25940fce3f2bdb486ce63b2df73a2b0966011ba221f61d546ed929980dd6ca"),
}


class Rejected(ValueError):
    pass


class Budget:
    def __init__(self, operations, seconds, output_bytes):
        self.operations_limit = operations
        self.seconds_limit = seconds
        self.output_limit = output_bytes
        self.operations = 0
        self.started = time.monotonic()

    def tick(self, amount=1):
        self.operations += amount
        if self.operations > self.operations_limit:
            raise Rejected("selected operation cap exceeded")
        if time.monotonic() - self.started > self.seconds_limit:
            raise Rejected("selected cooperative time cap exceeded")

    def compose(self, a, b):
        self.tick()
        return tuple(a[x] for x in b)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def read_small(path, limit=INPUT_BYTE_CEILING):
    with path.open("rb") as stream:
        data = stream.read(limit + 1)
    if len(data) > limit:
        raise Rejected(f"input byte cap exceeded: {path.name}")
    return data


def validate_perm(values):
    if (not isinstance(values, list) or len(values) != 8
            or any(type(x) is not int for x in values)
            or sorted(values) != list(range(1, 9))):
        raise Rejected("invalid literal eight-point permutation")
    return tuple(x - 1 for x in values)


def selected_inputs(spec, budget):
    if (spec.source_rows > SOURCE_ROW_CEILING or spec.normal_count > NORMAL_STATE_CEILING
            or spec.generator_count > GENERATOR_CEILING or not 1 <= spec.record_line <= 3):
        raise Rejected("selected specification exceeds immutable structural caps")
    source_path = ROOT / "formal/SymmetricSubgroupAsymptotics" / (spec.source_module + ".lean")
    source_bytes = read_small(source_path)
    if sha256(source_bytes) != spec.source_sha256:
        raise Rejected("pinned literal source digest changed")
    declarations = re.findall(r"toFun x := \(#\[([0-9,]+)\]", source_bytes.decode("utf-8"))
    if len(declarations) != spec.generator_count:
        raise Rejected("original source generator count changed")
    generators = [[int(x) + 1 for x in declaration.split(",")] for declaration in declarations]
    for g in generators:
        validate_perm(g)

    total_bytes = 0
    record = None
    with gzip.open(ROOT / "certificates/data/carrier_normals.jsonl.gz", "rb") as stream:
        for line in range(1, spec.record_line + 1):
            budget.tick()
            raw = stream.readline(INPUT_BYTE_CEILING - total_bytes + 1)
            total_bytes += len(raw)
            if total_bytes > INPUT_BYTE_CEILING or not raw.endswith(b"\n"):
                raise Rejected("selected decompressed input cap exceeded")
            if line == spec.record_line:
                if sha256(raw) != spec.record_sha256:
                    raise Rejected("pinned selected normal record changed")
                record = json.loads(raw)
    if record is None or record.get("action_id") != spec.master or record.get("schema_version") != 1:
        raise Rejected("unexpected selected normal record")
    normals = record.get("normals")
    if not isinstance(normals, list) or len(normals) != spec.normal_count:
        raise Rejected("selected normal-state count changed")
    for normal in normals:
        budget.tick()
        ng = normal.get("normal_generators")
        if not isinstance(ng, list) or len(ng) > GENERATOR_CEILING:
            raise Rejected("normal generator count exceeds cap")
        for g in ng:
            validate_perm(g)
        order = normal.get("order")
        if type(order) is not int or not 1 <= order <= spec.source_rows:
            raise Rejected("invalid diagnostic normal order")
        children = normal.get("children")
        if (not isinstance(children, list) or len(children) > spec.normal_count
                or any(type(j) is not int or not 1 <= j <= spec.normal_count for j in children)):
            raise Rejected("invalid selected normal child labels")

    alphabet = json.loads(read_small(ROOT / "certificates/data/base_alphabet.json"))
    number = int(spec.master.split("T")[1])
    action = next((a for a in alphabet["actions"]
                   if a.get("degree") == 8 and a.get("catalogue_locator") == [8, number]), None)
    if action is None or sorted(action["generators"]) != sorted(generators):
        raise Rejected("original source tuple differs from the committed alphabet")
    # Deliberately retain the source tuple order, even when alphabet order differs.
    node = {"id": f"b8_{number}", "degree": 8, "generators": generators}
    return node, record, total_bytes


def bounded_table_factory(spec, budget):
    cache = {}
    call_cap = 4 * spec.normal_count + 1

    def table(generators, degree):
        budget.tick()
        if degree != 8 or len(generators) > GENERATOR_CEILING + 1:
            raise Rejected("unselected degree or generator count")
        key = tuple(tuple(g) for g in generators)
        if key in cache:
            return cache[key]
        if len(cache) >= call_cap:
            raise Rejected("selected finite closure-call cap exceeded")
        identity = tuple(range(8))
        rows, position = [identity], {identity: 0}
        parents, letters, transitions = [0], [0], []
        for i, element in enumerate(rows):
            edges = []
            for j, generator in enumerate(key):
                product = budget.compose(element, generator)
                if product not in position:
                    if len(rows) >= spec.source_rows:
                        raise Rejected("selected closure source-row cap exceeded")
                    position[product] = len(rows)
                    rows.append(product)
                    parents.append(i)
                    letters.append(j)
                edges.append(position[product])
            transitions.append(edges)
        ordered = sorted(range(len(rows)), key=lambda i: legacy.packed(rows[i]))
        remap = {old: new for new, old in enumerate(ordered)}
        nxt = [[remap[x] for x in transitions[i]] for i in ordered]
        prev = [[0] * len(key) for _ in rows]
        for i, edges in enumerate(nxt):
            for j, target in enumerate(edges):
                prev[target][j] = i
        result = dict(codes=[legacy.packed(rows[i]) for i in ordered], rank=ordered,
                      parent=[remap[parents[i]] for i in ordered],
                      letter=[letters[i] for i in ordered], identity=remap[0], next=nxt, prev=prev)
        cache[key] = result
        return result

    return table


def emit_states(spec, node, record):
    _, text = legacy.emit(node, record)
    text = text.replace("SymmetricSubgroupAsymptotics.BinaryNormal" + spec.master, spec.namespace)
    text = text.replace("set_option maxRecDepth 100000\n", "")
    text = text.replace("set_option maxHeartbeats 0\n", "set_option Elab.async false\n")
    text = text.replace("local instance : Group Source :=", "local instance selectedStateSourceGroup : Group Source :=")
    text = text.replace("Generated by export_lean_normal_registry.py",
                        "Selected by export_lean_carrier_normal_registry_selected.py")
    for i, normal in enumerate(record["normals"]):
        extra = "\n"
        generators = [validate_perm(g) for g in normal["normal_generators"]]
        for j, generator in enumerate(generators):
            inverse = legacy.inv(generator)
            extra += f'''private def literalGenerator{j} : Equiv.Perm (Fin 8) where
  toFun x := ({legacy.arr(generator)} : Array (Fin 8))[x.val]!
  invFun x := ({legacy.arr(inverse)} : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

'''
        rhs = legacy.lookup([f"literalGenerator{j}" for j in range(len(generators))], "k.val") if generators else "Fin.elim0 k"
        extra += f'''def literalNormalGenerators (k : Fin {len(generators)}) : Equiv.Perm (Fin 8) :=
  {rhs}

/-- Same ordered literal normal tuple as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin {len(generators)}) :
    ({spec.source_module}.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
'''
        if generators:
            extra += f'''  apply permutationCode_injective 8
  change permutationCode ({spec.source_module}.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode ({spec.source_module}.certificate.toCayley.elements
        (normalGenerators k).index) =
      {spec.source_module}.certificate.rows (normalGenerators k).index :=
    {spec.source_module}.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel
'''
        else:
            extra += "  exact Fin.elim0 k\n"
        text = text.replace(f"\nend N{i}\n", extra + f"\nend N{i}\n")
    return text


def emit_registry(spec, data, budget):
    ambient, _, source, _, normals = data
    lookup = {frozenset(n["ns"]): i for i, n in enumerate(normals)}
    if len(source) != spec.source_rows or len(lookup) != spec.normal_count:
        raise Rejected("selected source size or distinct-normal count mismatch")
    bottom = lookup.get(frozenset([tuple(range(8))]))
    if bottom is None or normals[bottom]["ng"]:
        raise Rejected("selected bottom is not the actual empty tuple")
    text = f'''import SymmetricSubgroupAsymptotics.BinaryNormalSparseRegistry
import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal{spec.master}.States

/-! Complete original normal registry for the explicitly selected {spec.master}.
Every original central involution in every literal quotient is checked;
no completeness or numerical carrier-profile claim is trusted from input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace {spec.namespace}
local instance selectedRegistrySourceGroup : Group Source := {spec.source_module}.group

'''
    for i, normal in enumerate(normals):
        budget.tick()
        nset, selected = set(normal["ns"]), []
        for z, element in enumerate(normal["reps"]):
            central = (element not in nset and budget.compose(element, element) in nset
                       and all(budget.compose(budget.compose(element, g),
                                              legacy.inv(budget.compose(g, element))) in nset
                               for g in ambient))
            if central:
                extension = legacy.table(normal["ng"] + [element], 8)
                child = lookup.get(frozenset(legacy.unpack(c, 8) for c in extension["codes"]))
                if child is None or child + 1 not in normal["record"]["children"]:
                    raise Rejected("an actual central-involution child is absent")
                selected.append((z, child))
        if {child + 1 for _, child in selected} != set(normal["record"]["children"]):
            raise Rejected("selected child labels do not match all actual central-involution rows")
        count, q = len(selected), len(normal["reps"])
        row_expr = f'⟨{legacy.finfun([z for z, _ in selected], q, "j.val")}⟩' if count else "Fin.elim0 j"
        child_expr = legacy.finfun([child for _, child in selected], spec.normal_count, "j.val") if count else "Fin.elim0 j"
        text += f'''private def childRows{i} (j : Fin {count}) : N{i}.state.Row := {row_expr}
private def childIndex{i} (j : Fin {count}) : Fin {spec.normal_count} := {child_expr}

private theorem covers{i} : ∀ z : Fin {q},
    N{i}.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin {count}, childRows{i} j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact {legacy.checks(q)}

private theorem child{i}_generators : ∀ j : Fin {count}, ∀ k,
    N{i}.normalGenerators k ∈ (states (childIndex{i} j)).kernel := by
'''
        if not count:
            text += "  intro j\n  exact Fin.elim0 j\n"
        else:
            text += "  intro j\n  fin_cases j\n"
            for _, child in selected:
                target = normals[child]
                if not normal["ng"]:
                    text += "  · intro k\n    exact Fin.elim0 k\n"
                    continue
                indices = [target["ni"][g] for g in normal["ng"]]
                index_expr = legacy.finfun(indices, len(target["ns"]), "k.val")
                text += f'''  · change ∀ k, N{i}.normalGenerators k ∈ N{child}.kernel
    intro k
    have he : ∀ k : Fin {len(normal["ng"])}, N{i}.normalGenerators k =
        (⟨N{child}.normalCertificate.rows ({index_expr})⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N{child}.normalCertificate _
'''
        text += f'''
private theorem child{i}_lift : ∀ j : Fin {count},
    N{i}.cosets.representatives (childRows{i} j).index ∈
      (states (childIndex{i} j)).kernel := by
'''
        if not count:
            text += "  intro j\n  exact Fin.elim0 j\n"
        else:
            text += "  intro j\n  fin_cases j\n"
            for z, child in selected:
                witness = normals[child]["ni"][normal["reps"][z]]
                text += f'''  · change N{i}.cosets.representatives {z} ∈ N{child}.kernel
    have he : N{i}.cosets.representatives {z} =
        (⟨N{child}.normalCertificate.rows {witness}⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N{child}.normalCertificate _
'''
        text += f'''
private theorem child{i}_card : ∀ j : Fin {count},
    Nat.card (states (childIndex{i} j)).kernel = Nat.card N{i}.kernel * 2 := by
'''
        if not count:
            text += "  intro j\n  exact Fin.elim0 j\n"
        else:
            text += "  intro j\n  fin_cases j\n"
            for _, child in selected:
                text += f'''  · change Nat.card N{child}.kernel = Nat.card N{i}.kernel * 2
    norm_num [N{child}.kernel_card, N{i}.kernel_card]
'''
        text += f'''
private def children{i} : BinaryNormalChildren generators_full (states {i}) states where
  count := {count}
  rows := childRows{i}
  covers := by
    rintro ⟨z⟩ hz
    exact covers{i} z hz
  child := childIndex{i}
  generator_mem := child{i}_generators
  lift_mem := child{i}_lift
  child_card := child{i}_card

'''
    children = "(fun i => Fin.elim0 i)"
    for i in reversed(range(spec.normal_count)):
        children = f"(Fin.cases children{i} {children})"
    text += f'''private def children : (i : Fin {spec.normal_count}) →
    BinaryNormalChildren generators_full (states i) states :=
  {children}

def registry : BinaryNormalSparseRegistry generators_full states where
  bottom := {bottom}
  bottom_kernel := by
    change Subgroup.closure (Set.range N{bottom}.normalGenerators) = ⊥
    rw [show Set.range N{bottom}.normalGenerators = ∅ by ext x; simp]
    exact Subgroup.closure_empty
  children := children

theorem source_isPGroup : IsPGroup 2 Source :=
  IsPGroup.of_card (n := {spec.order_log}) (by rw [source_card]; rfl)

theorem complete (N : Subgroup Source) [N.Normal] :
    ∃ i, (states i).kernel = N := registry.complete source_isPGroup N

/-- Completeness for the same literal original permutation action. -/
theorem complete_original
    (N : Subgroup (Subgroup.closure (Set.range {spec.source_module}.generators))) [N.Normal] :
    ∃ i, (states i).kernel.map {spec.source_module}.originalEquiv.toMonoidHom = N :=
  registry.complete_map_of_equiv source_isPGroup {spec.source_module}.originalEquiv N

end {spec.namespace}
'''
    return text


def atomic_write(destination, payload):
    destination.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=destination.name + ".", dir=destination.parent)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, destination)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--master", choices=sorted(SPECS), required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--max-operations", type=int, default=200000)
    parser.add_argument("--max-seconds", type=float, default=10)
    parser.add_argument("--max-output-bytes", type=int, default=2097152)
    parser.add_argument("--private-report", type=Path)
    args = parser.parse_args()
    if not 1 <= args.max_operations <= OPERATION_CEILING:
        parser.error("max-operations must be in [1,1000000]")
    if not 0 < args.max_seconds <= SECONDS_CEILING:
        parser.error("max-seconds must be in (0,60]")
    if not 1 <= args.max_output_bytes <= OUTPUT_BYTE_CEILING:
        parser.error("max-output-bytes must be in [1,4194304]")
    if args.check and args.private_report is not None:
        parser.error("--check is read-only and cannot write a report")
    if args.private_report is not None:
        report_destination = args.private_report.resolve()
        if not report_destination.is_relative_to((ROOT.parent / "private_audits").resolve()):
            parser.error("reports must remain under private_audits")
    spec = SPECS[args.master]
    budget = Budget(args.max_operations, args.max_seconds, args.max_output_bytes)
    node, record, decompressed_bytes = selected_inputs(spec, budget)
    # Only the legacy pure state renderer is reused. Every multiplication and
    # closure it invokes is replaced by these bounded selected implementations.
    legacy.compose = budget.compose
    legacy.table = bounded_table_factory(spec, budget)
    data = legacy.action_data(node, record)
    source_rows_count = len(data[2])
    normals = data[4]
    normal_rows = sum(len(n["ns"]) for n in normals)
    quotient_rows = sum(len(n["reps"]) for n in normals)
    if source_rows_count != spec.source_rows or normal_rows > NORMAL_ROW_TOTAL_CEILING:
        raise Rejected("selected source/normal row totals exceed caps")
    if quotient_rows > QUOTIENT_ROW_TOTAL_CEILING:
        raise Rejected("selected quotient row total exceeds cap")
    if any(len(n["ns"]) != n["record"]["order"] for n in normals):
        raise Rejected("a diagnostic normal order differs from its literal closure")
    texts = {"States.lean": emit_states(spec, node, record),
             "Registry.lean": emit_registry(spec, data, budget)}
    payloads = {name: text.encode("utf-8") for name, text in texts.items()}
    output_bytes = sum(map(len, payloads.values()))
    budget.tick()
    if output_bytes > budget.output_limit:
        raise Rejected("selected output-byte cap exceeded")
    outputs = {}
    for name, payload in payloads.items():
        destination = spec.output_directory / name
        if args.check:
            if not destination.exists() or read_small(destination, budget.output_limit) != payload:
                raise Rejected(f"selected generated source mismatch: {name}")
        else:
            atomic_write(destination, payload)
        outputs[str(destination.relative_to(ROOT))] = sha256(payload)
    report = {
        "master": spec.master, "stage": "all-original-normal sparse registry only",
        "source_rows": source_rows_count, "normal_states": spec.normal_count,
        "normal_rows": normal_rows, "quotient_rows": quotient_rows,
        "original_generators": spec.generator_count, "operations": budget.operations,
        "decompressed_bytes": decompressed_bytes, "output_bytes": output_bytes,
        "source_sha256": spec.source_sha256, "record_sha256": spec.record_sha256,
        "outputs": outputs, "profile_fields_bound": False,
        "other_masters_enabled": False, "lean_status": "pending root checks",
        "mode": "check" if args.check else "write",
    }
    if args.private_report is not None:
        atomic_write(report_destination, (json.dumps(report, indent=2) + "\n").encode())
    print(json.dumps(report, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (Rejected, KeyError, TypeError, ValueError) as error:
        raise SystemExit(str(error)) from error
