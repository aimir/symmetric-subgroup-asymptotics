#!/usr/bin/env python3
"""Prepare only the literal 13-normal J=8T27 sparse registry pilot.

This selected producer does not enumerate normal subgroups: it reads the
committed J normal tuples, checks their bounded finite closures, and emits
Lean obligations for every original normal, coset row and central-involution
child. Registry completeness follows in Lean. Stored six-field profiles are
diagnostics only; this first-stage producer does NOT certify their ranks,
second radicals, quotient invariants, or a carrier-energy bound.

No compiler is invoked. --check is read-only; --write atomically replaces only
the two generated J files. Resource counters are cooperative bounds, not RSS
limits or preemptive timeouts. A bounded root compiler check remains required.
"""
from __future__ import annotations

import argparse
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
MASTER = "8T27"
SOURCE_MODULE = "BinaryMenuCayley8T27"
SOURCE_SHA256 = "4b7cff26997b94289d1820630fd3d16c464cbaff79aa829751c2151400d117d3"
RECORD_SHA256 = "a067822bdea58dfdc9486a6dd6f440fd807d0aee02364cbe462f7e787f122d0b"
NAMESPACE = "SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T27"
OUTPUT_DIRECTORY = ROOT / "formal/SymmetricSubgroupAsymptotics/GeneratedCarrierNormal8T27"
MAX_SOURCE_ROWS = 64
MAX_NORMALS = 13
MAX_GENERATORS = 8
MAX_QUOTIENT_ROWS_TOTAL = 1024
MAX_NORMAL_ROWS_TOTAL = 1024
INPUT_BYTE_CEILING = 262144
OUTPUT_BYTE_CEILING = 4194304
OPERATION_CEILING = 1000000
SECONDS_CEILING = 60.0


class Rejected(ValueError):
    pass


class Budget:
    def __init__(self, operations: int, seconds: float, output_bytes: int):
        self.operations_limit = operations
        self.seconds_limit = seconds
        self.output_limit = output_bytes
        self.operations = 0
        self.started = time.monotonic()

    def tick(self, amount: int = 1) -> None:
        self.operations += amount
        if self.operations > self.operations_limit:
            raise Rejected("selected operation cap exceeded")
        if time.monotonic() - self.started > self.seconds_limit:
            raise Rejected("selected cooperative time cap exceeded")

    def compose(self, a, b):
        self.tick()
        return tuple(a[x] for x in b)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_small(path: Path, limit: int = INPUT_BYTE_CEILING) -> bytes:
    with path.open("rb") as stream:
        data = stream.read(limit + 1)
    if len(data) > limit:
        raise Rejected(f"input cap exceeded: {path.name}")
    return data


def validate_perm(values):
    if (not isinstance(values, list) or len(values) != 8
            or any(type(x) is not int for x in values)
            or sorted(values) != list(range(1, 9))):
        raise Rejected("invalid original eight-point permutation")
    return tuple(x - 1 for x in values)


def selected_inputs(budget: Budget):
    """Read only the first two bounded carrier lines and stop at J."""
    path = ROOT / "certificates/data/carrier_normals.jsonl.gz"
    total = 0
    record = None
    with gzip.open(path, "rb") as stream:
        for expected in ("8T26", MASTER):
            budget.tick()
            raw = stream.readline(INPUT_BYTE_CEILING - total + 1)
            total += len(raw)
            if total > INPUT_BYTE_CEILING or not raw.endswith(b"\n"):
                raise Rejected("selected decompressed-byte cap exceeded")
            candidate = json.loads(raw)
            if candidate.get("action_id") != expected:
                raise Rejected("unexpected committed carrier-line order")
            if expected == MASTER:
                if sha256(raw) != RECORD_SHA256:
                    raise Rejected("selected J record digest changed")
                record = candidate
    if record is None or record.get("schema_version") != 1:
        raise Rejected("missing selected J record")
    normals = record.get("normals")
    if not isinstance(normals, list) or len(normals) != MAX_NORMALS:
        raise Rejected("the selected pilot requires exactly13 committed normal records")
    for normal in normals:
        budget.tick()
        generators = normal.get("normal_generators")
        if not isinstance(generators, list) or len(generators) > MAX_GENERATORS:
            raise Rejected("normal generator-count cap exceeded")
        for generator in generators:
            validate_perm(generator)
        order = normal.get("order")
        if type(order) is not int or not 1 <= order <= MAX_SOURCE_ROWS:
            raise Rejected("invalid diagnostic normal order")
        children = normal.get("children")
        if (not isinstance(children, list) or len(children) > MAX_NORMALS
                or any(type(i) is not int or not 1 <= i <= MAX_NORMALS for i in children)):
            raise Rejected("invalid selected child labels")

    source_path = ROOT / "formal/SymmetricSubgroupAsymptotics" / (SOURCE_MODULE + ".lean")
    source_bytes = read_small(source_path)
    if sha256(source_bytes) != SOURCE_SHA256:
        raise Rejected("the selected literal J source digest changed")
    source = source_bytes.decode("utf-8")
    original = re.findall(r"toFun x := \(#\[([0-9,]+)\]", source)
    if len(original) != 2:
        raise Rejected("expected exactly two original J generator declarations")
    generators = [[int(x) + 1 for x in row.split(",")] for row in original]
    for generator in generators:
        validate_perm(generator)
    alphabet = json.loads(read_small(ROOT / "certificates/data/base_alphabet.json"))
    action = next((a for a in alphabet["actions"]
                   if a.get("degree") == 8 and a.get("catalogue_locator") == [8, 27]), None)
    if action is None:
        raise Rejected("missing original J alphabet action")
    if sorted(action["generators"]) != sorted(generators):
        raise Rejected("literal original J generator set differs from committed alphabet")
    # Table/word positions use the literal Lean order, not alphabet order [1,0].
    node = {"id": "b8_27", "degree": 8, "generators": generators}
    return node, record, total


def bounded_table_factory(budget: Budget):
    cache = {}

    def table(generators, degree):
        budget.tick()
        if degree != 8 or len(generators) > MAX_GENERATORS + 1:
            raise Rejected("unselected group/tuple size")
        key = tuple(tuple(g) for g in generators)
        if key in cache:
            return cache[key]
        if len(cache) >= 64:
            raise Rejected("selected closure-call cap exceeded")
        identity = tuple(range(8))
        rows, position = [identity], {identity: 0}
        parents, letters, transitions = [0], [0], []
        for i, element in enumerate(rows):
            edges = []
            for j, generator in enumerate(key):
                product = budget.compose(element, generator)
                if product not in position:
                    if len(rows) >= MAX_SOURCE_ROWS:
                        raise Rejected("selected finite closure exceeded64 rows")
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


def header(imports: list[str]) -> str:
    return "\n".join("import " + name for name in imports) + f'''

/-! Selected original J=8T27 normal-registry pilot. Finite source data
are untrusted until these kernel proofs pass. No six-field profile or
energy/counting assertion is made by this registry stage. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace {NAMESPACE}
local instance : Group Source := BinaryMenuCayley8T27.group

'''


def emit_states(node, record) -> str:
    _, text = legacy.emit(node, record)
    text = text.replace("SymmetricSubgroupAsymptotics.BinaryNormal8T27", NAMESPACE)
    text = text.replace("set_option maxRecDepth 100000\n", "")
    text = text.replace("set_option maxHeartbeats 0\n", "set_option Elab.async false\n")
    text = text.replace("Generated by export_lean_normal_registry.py", "Selected by export_lean_carrier_j_registry.py")
    # Bind the chosen normal tuples pointwise to the committed permutations,
    # rather than relying on Python's source-index lookup for that identity.
    for i, normal in enumerate(record['normals']):
        extra = '\n'
        generators = [validate_perm(g) for g in normal['normal_generators']]
        for j, generator in enumerate(generators):
            inverse = legacy.inv(generator)
            extra += f'''private def literalGenerator{j} : Equiv.Perm (Fin 8) where
  toFun x := ({legacy.arr(generator)} : Array (Fin 8))[x.val]!
  invFun x := ({legacy.arr(inverse)} : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

'''
        rhs = (legacy.lookup([f'literalGenerator{j}' for j in range(len(generators))], 'k.val')
               if generators else 'Fin.elim0 k')
        extra += f'''def literalNormalGenerators (k : Fin {len(generators)}) : Equiv.Perm (Fin 8) :=
  {rhs}

/-- Same original normal generators as the selected committed record. -/
theorem original_normal_generator_coe (k : Fin {len(generators)}) :
    (BinaryMenuCayley8T27.originalEquiv (normalGenerators k) : Equiv.Perm (Fin 8)) =
      literalNormalGenerators k := by
'''
        if generators:
            extra += '''  apply permutationCode_injective 8
  change permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
    (normalGenerators k).index) = permutationCode (literalNormalGenerators k)
  have hcode :
      permutationCode (BinaryMenuCayley8T27.certificate.toCayley.elements
        (normalGenerators k).index) =
      BinaryMenuCayley8T27.certificate.rows (normalGenerators k).index :=
    BinaryMenuCayley8T27.certificate.encode_elements _
  rw [hcode]
  fin_cases k <;> decide +kernel
'''
        else:
            extra += '  exact Fin.elim0 k\n'
        text = text.replace(f'\nend N{i}\n', extra + f'\nend N{i}\n')
    return text


def emit_sparse_registry(node, record, data, budget: Budget) -> str:
    generators, source_table, source, _, normals = data
    source_count = len(source)
    if source_count != MAX_SOURCE_ROWS:
        raise Rejected("selected original J closure is not64 rows")
    normal_lookup = {frozenset(nd["ns"]): i for i, nd in enumerate(normals)}
    if len(normal_lookup) != MAX_NORMALS:
        raise Rejected("duplicate original normal generator closures")
    identity = tuple(range(8))
    bottom = normal_lookup.get(frozenset([identity]))
    if bottom is None or normals[bottom]["ng"]:
        raise Rejected("selected bottom requires the actual empty tuple")
    text = header(["SymmetricSubgroupAsymptotics.BinaryNormalSparseRegistry",
                   "SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T27.States"])
    for i, normal in enumerate(normals):
        budget.tick()
        representatives = normal["reps"]
        nset = set(normal["ns"])
        selected = []
        for z, element in enumerate(representatives):
            central = (element not in nset
                       and budget.compose(element, element) in nset
                       and all(budget.compose(budget.compose(element, g),
                                              legacy.inv(budget.compose(g, element))) in nset
                               for g in generators))
            if central:
                extension = legacy.table(normal["ng"] + [element], 8)
                elements = frozenset(legacy.unpack(c, 8) for c in extension["codes"])
                child = normal_lookup.get(elements)
                if child is None or child + 1 not in normal["record"]["children"]:
                    raise Rejected("a literal central-involution child is missing")
                selected.append((z, child))
        if {child + 1 for _, child in selected} != set(normal["record"]["children"]):
            raise Rejected("selected child list is not the complete original list")
        count, quotient_count = len(selected), len(representatives)
        rows = [z for z, _ in selected]
        children = [child for _, child in selected]
        row_expr = f'⟨{legacy.finfun(rows, quotient_count, "j.val")}⟩' if count else 'Fin.elim0 j'
        child_expr = legacy.finfun(children, MAX_NORMALS, 'j.val') if count else 'Fin.elim0 j'
        text += f'''private def childRows{i} (j : Fin {count}) : N{i}.state.Row := {row_expr}
private def childIndex{i} (j : Fin {count}) : Fin 13 := {child_expr}

private theorem covers{i} : ∀ z : Fin {quotient_count},
    N{i}.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin {count}, childRows{i} j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact {legacy.checks(quotient_count)}

private theorem child{i}_generators : ∀ j : Fin {count}, ∀ k,
    N{i}.normalGenerators k ∈ (states (childIndex{i} j)).kernel := by
'''
        if not count:
            text += '  intro j\n  exact Fin.elim0 j\n'
        else:
            text += '  intro j\n  fin_cases j\n'
            for _, child in selected:
                target = normals[child]
                size = len(target["ns"])
                if not normal["ng"]:
                    text += '  · intro k\n    exact Fin.elim0 k\n'
                    continue
                indices = [target["ni"][g] for g in normal["ng"]]
                index_expr = legacy.finfun(indices, size, 'k.val')
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
            text += '  intro j\n  exact Fin.elim0 j\n'
        else:
            text += '  intro j\n  fin_cases j\n'
            for z, child in selected:
                witness = normals[child]["ni"][representatives[z]]
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
            text += '  intro j\n  exact Fin.elim0 j\n'
        else:
            text += '  intro j\n  fin_cases j\n'
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
    children_expr = '(fun i => Fin.elim0 i)'
    for i in reversed(range(MAX_NORMALS)):
        children_expr = f'(Fin.cases children{i} {children_expr})'
    text += f'''private def children : (i : Fin 13) →
    BinaryNormalChildren generators_full (states i) states :=
  {children_expr}

def registry : BinaryNormalSparseRegistry generators_full states where
  bottom := {bottom}
  bottom_kernel := by
    change Subgroup.closure (Set.range N{bottom}.normalGenerators) = ⊥
    rw [show Set.range N{bottom}.normalGenerators = ∅ by ext x; simp]
    exact Subgroup.closure_empty
  children := children

theorem source_isPGroup : IsPGroup 2 Source :=
  IsPGroup.of_card (n := 6) (by rw [source_card]; rfl)

theorem complete (N : Subgroup Source) [N.Normal] :
    ∃ i, (states i).kernel = N := registry.complete source_isPGroup N

/-- Completeness concerns the same original literal Fin8 action. -/
theorem complete_original
    (N : Subgroup (Subgroup.closure (Set.range BinaryMenuCayley8T27.generators)))
    [N.Normal] :
    ∃ i, (states i).kernel.map BinaryMenuCayley8T27.originalEquiv.toMonoidHom = N :=
  registry.complete_map_of_equiv source_isPGroup BinaryMenuCayley8T27.originalEquiv N

end {NAMESPACE}
'''
    return text


def atomic_write(destination: Path, payload: bytes) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary_name = tempfile.mkstemp(prefix=destination.name + '.', dir=destination.parent)
    try:
        with os.fdopen(fd, 'wb') as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary_name, destination)
    finally:
        if os.path.exists(temporary_name):
            os.unlink(temporary_name)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--master', choices=[MASTER], required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    parser.add_argument('--max-operations', type=int, default=200000)
    parser.add_argument('--max-seconds', type=float, default=10)
    parser.add_argument('--max-output-bytes', type=int, default=2097152)
    parser.add_argument('--private-report', type=Path)
    args = parser.parse_args()
    if not 1 <= args.max_operations <= OPERATION_CEILING:
        parser.error('max-operations must be in[1,1000000]')
    if not 0 < args.max_seconds <= SECONDS_CEILING:
        parser.error('max-seconds must be in(0,60]')
    if not 1 <= args.max_output_bytes <= OUTPUT_BYTE_CEILING:
        parser.error('max-output-bytes must be in[1,4194304]')
    if args.check and args.private_report is not None:
        parser.error('--check is read-only and cannot write a report')
    if args.private_report is not None:
        report_destination = args.private_report.resolve()
        private_root = (ROOT.parent / 'private_audits').resolve()
        if not report_destination.is_relative_to(private_root):
            parser.error('reports must stay under the private_audits directory')
    budget = Budget(args.max_operations, args.max_seconds, args.max_output_bytes)
    node, record, decompressed_bytes = selected_inputs(budget)
    # Reuse only the legacy pure state emitter and its data shape. ALL its
    # group operations/closures are replaced by the bounded selected versions.
    legacy.compose = budget.compose
    legacy.table = bounded_table_factory(budget)
    data = legacy.action_data(node, record)
    source_rows = len(data[2])
    normals = data[4]
    normal_rows = sum(len(nd['ns']) for nd in normals)
    quotient_rows = sum(len(nd['reps']) for nd in normals)
    if source_rows != MAX_SOURCE_ROWS or normal_rows > MAX_NORMAL_ROWS_TOTAL:
        raise Rejected('selected source/normal-row cap violated')
    if quotient_rows > MAX_QUOTIENT_ROWS_TOTAL:
        raise Rejected('selected quotient-row cap violated')
    if any(len(nd['ns']) != nd['record']['order'] for nd in normals):
        raise Rejected('a stored normal order disagrees with its literal closure')
    texts = {'States.lean': emit_states(node, record),
             'Registry.lean': emit_sparse_registry(node, record, data, budget)}
    payloads = {name: text.encode('utf-8') for name, text in texts.items()}
    output_bytes = sum(map(len, payloads.values()))
    budget.tick()
    if output_bytes > budget.output_limit:
        raise Rejected('selected output-byte cap exceeded')
    outputs = {}
    for name, payload in payloads.items():
        destination = OUTPUT_DIRECTORY / name
        if args.check:
            if not destination.exists() or read_small(destination, budget.output_limit) != payload:
                raise Rejected(f'selected generated source mismatch: {name}')
        else:
            atomic_write(destination, payload)
        outputs[str(destination.relative_to(ROOT))] = sha256(payload)
    report = {'master': MASTER, 'stage': 'all-original-normal sparse registry only',
              'profile_fields_bound': False, 'normal_count': MAX_NORMALS,
              'source_rows': source_rows, 'normal_rows': normal_rows,
              'quotient_rows': quotient_rows, 'operations': budget.operations,
              'decompressed_bytes': decompressed_bytes, 'output_bytes': output_bytes,
              'source_sha256': SOURCE_SHA256, 'normal_record_sha256': RECORD_SHA256,
              'outputs': outputs, 'mode': 'check' if args.check else 'write'}
    if args.private_report is not None:
        atomic_write(report_destination, (json.dumps(report, indent=2) + '\n').encode())
    print(json.dumps(report, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (Rejected, KeyError, TypeError, ValueError) as error:
        raise SystemExit(str(error)) from error
