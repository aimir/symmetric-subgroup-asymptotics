#!/usr/bin/env python3
"""Selected J=8T27 derived-subgroup and quotient-invariant certificates.

Reads only the same committed J record/original tuple as the accepted sparse
registry. It emits finite membership masks, an eight-element derived-word
certificate, and exact center/intersection tests for those 13 literal states.
No normal subgroup enumeration, quotient multiplication tables, stored
profile fields, compiler invocation, or legacy exporter main is used.

--check is read-only. --write atomically replaces only Derived.lean and
QuotientProfiles.lean. Fixed state and cooperative operation/time/output
bounds are not a hard RSS limit or preemptive timeout.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import export_lean_carrier_j_registry as registry
import export_lean_carrier_j_radicals as radicals


ROOT = registry.ROOT
OUT = registry.OUTPUT_DIRECTORY
NAMESPACE = registry.NAMESPACE
DERIVED_STATE = 4
DERIVED_ROWS = 8
MAX_OPERATIONS = 500000
MAX_SECONDS = 30.0
MAX_OUTPUT_BYTES = 2097152
MAX_WORD_DEPTH = 16


def commutator(a, b, budget):
    return budget.compose(budget.compose(budget.compose(a, b), registry.legacy.inv(a)),
                          registry.legacy.inv(b))


def selected_derived_words(ambient, normals, budget):
    target = normals[DERIVED_STATE]
    allowed = set(target["rows"])
    if len(allowed) != DERIVED_ROWS:
        raise registry.Rejected("the selected derived-state candidate is not eight rows")
    identity = tuple(range(8))
    rows, positions, nodes, depths = [identity], {identity: 0}, [("one",)], [0]

    def add(value, node, depth):
        budget.tick()
        if value not in allowed:
            raise registry.Rejected("original commutator word escapes selected N4")
        if value in positions:
            return positions[value]
        if len(rows) >= DERIVED_ROWS or depth > MAX_WORD_DEPTH:
            raise registry.Rejected("selected derived word bound exceeded")
        positions[value] = len(rows)
        rows.append(value)
        nodes.append(node)
        depths.append(depth)
        return positions[value]

    seeds, commutators = [], []
    for i, a in enumerate(ambient):
        current = []
        for j, b in enumerate(ambient):
            value = commutator(a, b, budget)
            current.append(value)
            seeds.append(add(value, ("comm", i, j), 1))
        commutators.append(current)
    seeds = sorted(set(seeds) - {0})
    inverse = [registry.legacy.inv(g) for g in ambient]
    cursor = 0
    while cursor < len(rows):
        budget.tick()
        x = rows[cursor]
        for seed in seeds:
            add(budget.compose(x, rows[seed]), ("mul", cursor, seed),
                1 + max(depths[cursor], depths[seed]))
        for i, g in enumerate(ambient):
            add(budget.compose(budget.compose(g, x), inverse[i]), ("conj", i, cursor),
                1 + depths[cursor])
            add(budget.compose(budget.compose(inverse[i], x), g), ("conjInv", i, cursor),
                1 + depths[cursor])
        cursor += 1
    if set(rows) != allowed:
        raise registry.Rejected("derived words do not cover the actual selected N4 generators")
    return {"positions": positions, "nodes": nodes, "commutators": commutators,
            "max_depth": max(depths)}


def word_expression(node):
    tag, *a = node
    if tag == "one":
        return ".one"
    if tag == "comm":
        return f".comm {a[0]} {a[1]}"
    if tag == "mul":
        return f".mul derivedWord{a[0]} derivedWord{a[1]}"
    if tag in ("conj", "conjInv"):
        return f".{tag} {a[0]} derivedWord{a[1]}"
    raise registry.Rejected("invalid derived-word node")


def bool_array(values):
    return "#[" + ",".join("true" if v else "false" for v in values) + "]"


def bool_matrix(values, first="i.val", second="x.val"):
    return f'({registry.legacy.lookup([bool_array(row) for row in values], first)} : Array Bool)[{second}]!'


def header(imports, description, instance_name):
    return "\n".join("import SymmetricSubgroupAsymptotics." + m for m in imports) + f'''

/-! {description}
Selected by export_lean_carrier_j_quotients.py. Stored carrier profiles
are not proof inputs; every mask is bound to the same original elements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace {NAMESPACE}
local instance {instance_name} : Group Source := BinaryMenuCayley8T27.group

'''


def source_rows(ambient, budget):
    table = registry.bounded_table_factory(budget)(ambient, 8)
    rows = [registry.legacy.unpack(c, 8) for c in table["codes"]]
    if len(rows) != 64:
        raise registry.Rejected("selected source-row count changed")
    return rows


def masks_and_counts(ambient, normals, source, budget):
    normal_masks, center_masks, intersections = [], [], []
    dset = set(normals[DERIVED_STATE]["rows"])
    # Compute each original commutator only once; no quotient table is formed.
    source_commutators = [[commutator(x, g, budget) for g in ambient] for x in source]
    for normal in normals:
        budget.tick()
        nset = set(normal["rows"])
        normal_masks.append([x in nset for x in source])
        center_masks.append([all(c in nset for c in row) for row in source_commutators])
        intersections.append(len(nset & dset))
    centers = [sum(mask) for mask in center_masks]
    center_orders, derived_orders = [], []
    for n, c, b in zip(normals, centers, intersections):
        if c % len(n["rows"]) or DERIVED_ROWS % b:
            raise registry.Rejected("selected exact quotient cardinal division failed")
        center_orders.append(c // len(n["rows"]))
        derived_orders.append(DERIVED_ROWS // b)
    center_logs = [radicals.log2_exact(c) for c in center_orders]
    derived_logs = [radicals.log2_exact(g) for g in derived_orders]
    return {"normal": normal_masks, "center": center_masks, "center_preimage": centers,
            "intersection": intersections, "center_orders": center_orders,
            "derived_orders": derived_orders, "center_logs": center_logs,
            "derived_logs": derived_logs}


def emit_derived(normals, words, masks):
    text = header(["GeneratedCarrierNormal8T27.States", "DerivedGeneratorWords",
                   "FiniteQuotientInvariantCertificates"],
                  "Literal membership masks and the actual derived subgroup of J.",
                  "derivedMasksSourceGroup")
    text += f'''def sourceIndexEquiv : Fin 64 ≃ Source where
  toFun i := ⟨i⟩
  invFun x := x.index
  left_inv _ := rfl
  right_inv _ := rfl

/-- Membership in the same accepted 13 literal normal subgroups. -/
def normalMask (i : Fin 13) (x : Fin 64) : Bool :=
  {bool_matrix(masks["normal"])}

'''
    for i, normal in enumerate(normals):
        text += f'''private theorem normalMask_checked{i} : ∀ x : Fin 64,
    normalMask {i} x = true ↔ ∃ j : Fin {len(normal["rows"])},
      N{i}.normalCertificate.rows j = x :=
  {registry.legacy.checks(64)}

'''
    text += '''theorem normalMask_mem (i : Fin 13) (x : Source) :
    normalMask i x.index = true ↔ x ∈ (states i).kernel := by
  fin_cases i
'''
    for i in range(13):
        text += (f"  · exact (normalMask_checked{i} x.index).trans\n"
                 f"      (N{i}.normalCertificate.mem_closure_iff x).symm\n")
    text += "\n"
    for i, node in enumerate(words["nodes"]):
        text += f"private def derivedWord{i} : DerivedGeneratorWord (Fin 2) := {word_expression(node)}\n"
    dg = normals[DERIVED_STATE]["generators"]
    word_names = [f'derivedWord{words["positions"][g]}' for g in dg]
    comm_rows = [[normals[DERIVED_STATE]["index"][v] for v in row]
                 for row in words["commutators"]]
    text += f'''
private def derivedWords (j : Fin {len(dg)}) : DerivedGeneratorWord (Fin 2) :=
  {registry.legacy.lookup(word_names, "j.val")}

private theorem derivedWords_checked : ∀ j : Fin {len(dg)},
    (derivedWords j).eval generators = N4.normalGenerators j := by
  intro j
  fin_cases j <;> decide +kernel

private def generatorCommutatorRow (i j : Fin 2) : Fin 8 :=
  {registry.legacy.mat(comm_rows, "Fin 8")}

private theorem generatorCommutators_checked : ∀ i j : Fin 2,
    ⁅generators i, generators j⁆ =
      (⟨N4.normalCertificate.rows (generatorCommutatorRow i j)⟩ : Source) := by
  decide +kernel

/-- N4 is identified with the actual derived subgroup in both directions. -/
theorem source_derived_eq : commutator Source = N4.kernel := by
  apply le_antisymm
  · apply commutator_le_of_generator_commutators N4.kernel generators generators_full
    intro i j
    rw [generatorCommutators_checked]
    exact binaryNormalRow_mem N4.normalCertificate _
  · change Subgroup.closure (Set.range N4.normalGenerators) ≤ commutator Source
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    rw [← derivedWords_checked j]
    exact (derivedWords j).eval_mem_commutator generators

theorem source_derived_card : Nat.card (commutator Source) = 8 := by
  rw [source_derived_eq]
  exact N4.kernel_card

'''
    return text + f"end {NAMESPACE}\n"


def emit_quotients(normals, masks):
    text = header(["GeneratedCarrierNormal8T27.Derived",
                   "GeneratedCarrierNormal8T27.RadicalProfiles", "FiniteQuotientInvariantMasks"],
                  "Exact center and derived orders of all 13 original J quotients.",
                  "quotientProfilesSourceGroup")
    text += f'''def centerMask (i : Fin 13) (x : Fin 64) : Bool :=
  {bool_matrix(masks["center"])}

def intersectionMask (i : Fin 13) (x : Fin 64) : Bool :=
  normalMask i x && normalMask 4 x

def centerLog (i : Fin 13) : ℕ := {registry.legacy.lookup(masks["center_logs"])}
def derivedLog (i : Fin 13) : ℕ := {registry.legacy.lookup(masks["derived_logs"])}
def intersectionOrder (i : Fin 13) : ℕ := {registry.legacy.lookup(masks["intersection"])}

'''
    for i in range(13):
        text += f'''private theorem centerMask_checked{i} : ∀ x : Fin 64,
    centerMask {i} x = true ↔ ∀ j : Fin 2,
      normalMask {i} (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  {registry.legacy.checks(64)}

private theorem centerMask_card{i} :
    Fintype.card {{x : Fin 64 // centerMask {i} x = true}} = {masks["center_preimage"][i]} := by
  decide +kernel

private theorem intersectionMask_card{i} :
    Fintype.card {{x : Fin 64 // intersectionMask {i} x = true}} = {masks["intersection"][i]} := by
  decide +kernel

'''
    text += '''theorem centerMask_test (i : Fin 13) (x : Fin 64) :
    centerMask i x = true ↔ ∀ j : Fin 2,
      ⁅(⟨x⟩ : Source), generators j⁆ ∈ (states i).kernel := by
  have h : centerMask i x = true ↔ ∀ j : Fin 2,
      normalMask i (⁅(⟨x⟩ : Source), generators j⁆).index = true := by
    fin_cases i
'''
    text += "".join(f"    · exact centerMask_checked{i} x\n" for i in range(13))
    text += '''  exact h.trans (forall_congr' (fun j => normalMask_mem i _))

theorem intersectionMask_mem (i : Fin 13) (x : Fin 64) :
    intersectionMask i x = true ↔
      (⟨x⟩ : Source) ∈ (states i).kernel ⊓ commutator Source := by
  rw [source_derived_eq]
  change (normalMask i x && normalMask 4 x) = true ↔ _
  rw [Bool.and_eq_true]
  exact and_congr (normalMask_mem i ⟨x⟩) (normalMask_mem 4 ⟨x⟩)

theorem centerMask_card (i : Fin 13) :
    Nat.card {x : Fin 64 // centerMask i x = true} =
      2 ^ centerLog i * Nat.card (states i).kernel := by
  rw [Nat.card_eq_fintype_card]
  fin_cases i
'''
    text += "".join(f"  · change Fintype.card {{x : Fin 64 // centerMask {i} x = true}} =\n"
                    f"      2 ^ {masks['center_logs'][i]} * Nat.card N{i}.kernel\n"
                    f"    rw [N{i}.kernel_card]\n"
                    f"    exact centerMask_card{i}\n" for i in range(13))
    text += '''
theorem intersectionMask_card (i : Fin 13) :
    Nat.card {x : Fin 64 // intersectionMask i x = true} = intersectionOrder i := by
  rw [Nat.card_eq_fintype_card]
  fin_cases i
'''
    text += "".join(f"  · exact intersectionMask_card{i}\n" for i in range(13))
    text += '''
theorem source_intersection_card (i : Fin 13) :
    Nat.card ↥((states i).kernel ⊓ commutator Source) = intersectionOrder i := by
  let e := sourceIndexEquiv.subtypeEquiv (intersectionMask_mem i)
  exact (Nat.card_congr e).symm.trans (intersectionMask_card i)

theorem source_quotient_center_card (i : Fin 13) :
    Nat.card (Subgroup.center (Source ⧸ (states i).kernel)) = 2 ^ centerLog i :=
  quotientCenter_card_of_mask (states i).kernel generators generators_full sourceIndexEquiv
    (fun x => centerMask i x = true) (centerMask_test i) _ (centerMask_card i)

theorem source_quotient_derived_card (i : Fin 13) :
    Nat.card (commutator (Source ⧸ (states i).kernel)) = 2 ^ derivedLog i := by
  apply quotientCommutator_card_of_inf_card
  rw [source_derived_card, source_intersection_card]
  fin_cases i <;> decide +kernel

/-- The original tuple and all original elements are transported together. -/
def originalAmbientGenerators (j : Fin 2) : Original :=
  BinaryMenuCayley8T27.originalEquiv (generators j)

theorem originalAmbientGenerators_full :
    Subgroup.closure (Set.range originalAmbientGenerators) = ⊤ := by
  have h := congrArg (fun K : Subgroup Source =>
    K.map BinaryMenuCayley8T27.originalEquiv.toMonoidHom) generators_full
  dsimp only at h
  rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective
    BinaryMenuCayley8T27.originalEquiv.toMonoidHom
    BinaryMenuCayley8T27.originalEquiv.surjective] at h
  have hs : BinaryMenuCayley8T27.originalEquiv.toMonoidHom '' Set.range generators =
      Set.range originalAmbientGenerators := by
    ext x
    simp [originalAmbientGenerators]
  rwa [hs] at h

def originalIndexEquiv : Fin 64 ≃ Original :=
  sourceIndexEquiv.trans BinaryMenuCayley8T27.originalEquiv.toEquiv

theorem originalEquiv_mem_originalKernel (i : Fin 13) (x : Source) :
    BinaryMenuCayley8T27.originalEquiv x ∈ originalKernel i ↔ x ∈ (states i).kernel := by
  constructor
  · rintro ⟨y, hy, he⟩
    exact BinaryMenuCayley8T27.originalEquiv.injective he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem original_derived_eq : commutator Original = originalKernel 4 := by
  have h : (commutator Source).map BinaryMenuCayley8T27.originalEquiv.toMonoidHom =
      commutator Original := by
    have hr : BinaryMenuCayley8T27.originalEquiv.toMonoidHom.range = ⊤ :=
      MonoidHom.range_eq_top.mpr BinaryMenuCayley8T27.originalEquiv.surjective
    rw [map_commutator_eq, hr, ← commutator_def]
  exact h.symm.trans (congrArg (fun K : Subgroup Source =>
    K.map BinaryMenuCayley8T27.originalEquiv.toMonoidHom) source_derived_eq)

theorem original_derived_card : Nat.card (commutator Original) = 8 := by
  rw [original_derived_eq]
  exact original_card 4

theorem original_centerMask_test (i : Fin 13) (x : Fin 64) :
    centerMask i x = true ↔ ∀ j : Fin 2,
      ⁅originalIndexEquiv x, originalAmbientGenerators j⁆ ∈ originalKernel i := by
  apply (centerMask_test i x).trans
  apply forall_congr'
  intro j
  have h := originalEquiv_mem_originalKernel i ⁅(⟨x⟩ : Source), generators j⁆
  simpa only [map_commutatorElement] using h.symm

theorem original_intersectionMask_mem (i : Fin 13) (x : Fin 64) :
    intersectionMask i x = true ↔
      originalIndexEquiv x ∈ originalKernel i ⊓ commutator Original := by
  rw [original_derived_eq]
  change (normalMask i x && normalMask 4 x) = true ↔ _
  rw [Bool.and_eq_true]
  exact and_congr ((normalMask_mem i ⟨x⟩).trans
    (originalEquiv_mem_originalKernel i ⟨x⟩).symm)
    ((normalMask_mem 4 ⟨x⟩).trans (originalEquiv_mem_originalKernel 4 ⟨x⟩).symm)

theorem original_intersection_card (i : Fin 13) :
    Nat.card ↥(originalKernel i ⊓ commutator Original) = intersectionOrder i := by
  let e := originalIndexEquiv.subtypeEquiv (original_intersectionMask_mem i)
  exact (Nat.card_congr e).symm.trans (intersectionMask_card i)

theorem original_quotient_center_card (i : Fin 13) :
    Nat.card (Subgroup.center (Original ⧸ originalKernel i)) = 2 ^ centerLog i := by
  apply quotientCenter_card_of_mask (originalKernel i) originalAmbientGenerators
    originalAmbientGenerators_full originalIndexEquiv (fun x => centerMask i x = true)
    (original_centerMask_test i)
  have h := centerMask_card i
  rw [state_card] at h
  simpa only [original_card] using h

theorem original_quotient_derived_card (i : Fin 13) :
    Nat.card (commutator (Original ⧸ originalKernel i)) = 2 ^ derivedLog i := by
  apply quotientCommutator_card_of_inf_card
  rw [original_derived_card, original_intersection_card]
  fin_cases i <;> decide +kernel

/-- Every actual original normal has the certified quotient fields c,g.
The independent head-maximum and physical-weight tasks are not assumed. -/
theorem complete_original_quotient_profiles (N : Subgroup Original) [N.Normal] :
    ∃ i : Fin 13, originalKernel i = N ∧
      Nat.card (Subgroup.center (Original ⧸ N)) = 2 ^ centerLog i ∧
      Nat.card (commutator (Original ⧸ N)) = 2 ^ derivedLog i := by
  obtain ⟨i, hi⟩ := complete_original N
  change originalKernel i = N at hi
  subst N
  exact ⟨i, rfl, original_quotient_center_card i, original_quotient_derived_card i⟩

'''
    return text + f"end {NAMESPACE}\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--master", choices=["8T27"], required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--max-operations", type=int, default=100000)
    parser.add_argument("--max-seconds", type=float, default=10)
    parser.add_argument("--max-output-bytes", type=int, default=1048576)
    parser.add_argument("--private-report", type=Path)
    args = parser.parse_args()
    if not 1 <= args.max_operations <= MAX_OPERATIONS:
        parser.error("max-operations must be in [1,500000]")
    if not 0 < args.max_seconds <= MAX_SECONDS:
        parser.error("max-seconds must be in (0,30]")
    if not 1 <= args.max_output_bytes <= MAX_OUTPUT_BYTES:
        parser.error("max-output-bytes must be in [1,2097152]")
    if args.check and args.private_report is not None:
        parser.error("--check is read-only and cannot write a report")
    if args.private_report is not None:
        report_destination = args.private_report.resolve()
        if not report_destination.is_relative_to((ROOT.parent / "private_audits").resolve()):
            parser.error("reports must remain under private_audits")
    budget = registry.Budget(args.max_operations, args.max_seconds, args.max_output_bytes)
    prerequisites = radicals.checked_prerequisites()
    ambient, normals, _, input_bytes = radicals.selected_data(budget)
    source = source_rows(ambient, budget)
    words = selected_derived_words(ambient, normals, budget)
    masks = masks_and_counts(ambient, normals, source, budget)
    texts = {"Derived.lean": emit_derived(normals, words, masks),
             "QuotientProfiles.lean": emit_quotients(normals, masks)}
    payloads = {name: text.encode("utf-8") for name, text in texts.items()}
    output_bytes = sum(map(len, payloads.values()))
    budget.tick()
    if output_bytes > budget.output_limit:
        raise registry.Rejected("selected output-byte cap exceeded")
    outputs = {}
    for name, payload in payloads.items():
        destination = OUT / name
        if args.check:
            if not destination.exists() or registry.read_small(destination, MAX_OUTPUT_BYTES) != payload:
                raise registry.Rejected(f"selected generated source mismatch: {name}")
        else:
            registry.atomic_write(destination, payload)
        outputs[str(destination.relative_to(ROOT))] = registry.sha256(payload)
    radicals.checked_prerequisites()
    report = {
        "master": "8T27", "stage": "actual derived subgroup and quotient c,g only",
        "source_rows": 64, "normal_states": 13, "derived_state_index_zero_based": DERIVED_STATE,
        "derived_word_nodes": len(words["nodes"]), "derived_word_max_depth": words["max_depth"],
        "normal_membership_bits": 13 * 64, "center_tests": 13 * 64 * 2,
        "center_preimage_orders": masks["center_preimage"], "intersection_orders": masks["intersection"],
        "computed_center_logs": masks["center_logs"], "computed_derived_logs": masks["derived_logs"],
        "decompressed_bytes": input_bytes, "operations": budget.operations, "output_bytes": output_bytes,
        "outputs": outputs, "stored_profile_fields_used": False,
        "accepted_prerequisites": {str(p.relative_to(ROOT)): h for p, h in prerequisites.items()},
        "lean_status": "pending root checks", "mode": "check" if args.check else "write",
    }
    if args.private_report is not None:
        registry.atomic_write(report_destination, (json.dumps(report, indent=2) + "\n").encode())
    print(json.dumps(report, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (registry.Rejected, KeyError, TypeError, ValueError) as error:
        raise SystemExit(str(error)) from error
