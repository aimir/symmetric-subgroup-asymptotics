#!/usr/bin/env python3
"""Emit one individually selected, bounded original-carrier profile stage.

The enabled master is X=8T26. Select exactly one of ``--stage radicals``,
``--stage derived``, ``--stage quotients`` or ``--stage heads``. Radicals identifies actual
relative radicals and their iterates, binding k,n,a2 to the same original
normal. Derived proves G' and original normal membership masks. Quotients
proves c,g using actual center/intersection masks; check Derived first.
Heads proves the ambient-normal maximum from the complete checked registry
and requires its accepted Derived source digest via --derived-sha256.
No numerical profile, a2 <= m shortcut, normal discovery, quotient-table
search, or catalogue-wide mode is used. The accepted States/Registry and
all original source data are pinned. Literal generator order is retained.

The stage is parameterized by the shared selected-registry specification;
every stage is gated separately. J sources and producers remain untouched. Neither a Lean
compiler nor any imported exporter's main is called. --check is read-only;
--write atomically replaces only this selected stage's output sources.
Bounds are cooperative/state/output bounds, not hard RSS/time guarantees.
"""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

import export_lean_carrier_normal_registry_selected as registry


ROOT = registry.ROOT
MAX_WORD_DEPTH = 64
MAX_WORD_NODES_TOTAL = 3584
MAX_OUTPUT_BYTES = 2097152
MAX_OPERATIONS = 500000
MAX_SECONDS = 30.0
REGISTRY_PRODUCER_SHA256 = "ffc6bd238c2946d8823111369444e6db3396710ab0ca52eb4959811dbefb1e01"
FORMAT_HELPER_SHA256 = "550ca3a24f2c63489355ac64c20f38d33ac69083b876d3673cfad5ca9305f6eb"
RADICAL_WORDS_SHA256 = "7815c2e29ba1cb2d1c5637a6bdaf728414e456964c504d90be283d10cdb01274"
# Admission requires a selected root check; no implicit admission from SPECS.
ACCEPTED = {
    "8T26": {
        "States.lean": "99874578be301c2620758f5f3e2726e2980353d59fc441869459dc1341400f54",
        "Registry.lean": "a917062dde031342ab81595494935fa0815e183b3023e283a0b99d17c9e2f34b",
    },
}


def checked_prerequisites(spec):
    paths = {spec.output_directory / name: digest for name, digest in ACCEPTED[spec.master].items()}
    paths.update({
        Path(registry.__file__).resolve(): REGISTRY_PRODUCER_SHA256,
        Path(registry.legacy.__file__).resolve(): FORMAT_HELPER_SHA256,
        ROOT / "formal/SymmetricSubgroupAsymptotics/PrimeRelativeRadicalWords.lean": RADICAL_WORDS_SHA256,
        ROOT / "formal/SymmetricSubgroupAsymptotics" / (spec.source_module + ".lean"): spec.source_sha256,
    })
    for path, expected in paths.items():
        if registry.sha256(registry.read_small(path, MAX_OUTPUT_BYTES)) != expected:
            raise registry.Rejected(f"accepted selected prerequisite changed: {path.name}")
    return paths


def selected_data(spec, budget):
    # Do not call legacy.action_data: this stage needs only literal subgroup
    # closures, not the already certified coset actions or multiplication tables.
    node, record, input_bytes = registry.selected_inputs(spec, budget)
    table = registry.bounded_table_factory(spec, budget)
    generators = [registry.validate_perm(g) for g in node["generators"]]
    source_table = table(generators, 8)
    source = [registry.legacy.unpack(c, 8) for c in source_table["codes"]]
    if len(source) != spec.source_rows:
        raise registry.Rejected("selected literal source-row count changed")
    source_set = set(source)
    normals = []
    normal_rows = 0
    for normal in record["normals"]:
        budget.tick()
        ng = [registry.validate_perm(g) for g in normal["normal_generators"]]
        nt = table(ng, 8)
        rows = [registry.legacy.unpack(c, 8) for c in nt["codes"]]
        normal_rows += len(rows)
        if normal_rows > registry.NORMAL_ROW_TOTAL_CEILING:
            raise registry.Rejected("selected normal-row total cap exceeded")
        if not set(rows) <= source_set or len(rows) != normal["order"]:
            raise registry.Rejected("selected normal closure/source mismatch")
        normals.append({"generators": ng, "rows": rows,
                        "index": {g: i for i, g in enumerate(rows)}})
    lookup = {frozenset(n["rows"]): i for i, n in enumerate(normals)}
    if len(lookup) != spec.normal_count:
        raise registry.Rejected("duplicate selected normal closures")
    return generators, normals, lookup, input_bytes


def radical_search(spec, ambient, normal, lookup, budget):
    """Finite normal closure via seed multiplication and original conjugations.

    All discovered elements carry acyclic explicit word witnesses. The search
    result is untrusted: Lean later checks lower words and upper generator
    tests against a separately normal target from the accepted registry.
    """
    identity = tuple(range(8))
    nset = set(normal["rows"])
    rows = [identity]
    position = {identity: 0}
    nodes = [("one",)]
    depth = [0]

    def add(value, word, word_depth):
        budget.tick()
        if value not in nset:
            raise registry.Rejected("radical word escaped its original normal")
        if value in position:
            return position[value]
        if len(rows) >= spec.source_rows or word_depth > MAX_WORD_DEPTH:
            raise registry.Rejected("selected radical word/state cap exceeded")
        index = len(rows)
        position[value] = index
        rows.append(value)
        nodes.append(word)
        depth.append(word_depth)
        return index

    powers, mixed, seeds = [], [], []
    inverse_ambient = [registry.legacy.inv(g) for g in ambient]
    for j, n in enumerate(normal["generators"]):
        square = budget.compose(n, n)
        powers.append(square)
        seeds.append(add(square, ("power", j), 1))
        commutators = []
        inverse_n = registry.legacy.inv(n)
        for i, g in enumerate(ambient):
            value = budget.compose(budget.compose(budget.compose(n, g), inverse_n),
                                   inverse_ambient[i])
            commutators.append(value)
            seeds.append(add(value, ("mixed", j, i), 1))
        mixed.append(commutators)
    seeds = sorted(set(seeds) - {0})
    cursor = 0
    while cursor < len(rows):
        budget.tick()
        x = rows[cursor]
        for seed in seeds:
            value = budget.compose(x, rows[seed])
            add(value, ("mul", cursor, seed), 1 + max(depth[cursor], depth[seed]))
        for i, g in enumerate(ambient):
            value = budget.compose(budget.compose(g, x), inverse_ambient[i])
            add(value, ("conj", i, cursor), 1 + depth[cursor])
            value = budget.compose(budget.compose(inverse_ambient[i], x), g)
            add(value, ("conjInv", i, cursor), 1 + depth[cursor])
        cursor += 1
    target = lookup.get(frozenset(rows))
    if target is None:
        raise registry.Rejected("the exact radical is absent from the selected registry")
    return {"target": target, "nodes": nodes, "position": position,
            "powers": powers, "mixed": mixed, "depth": max(depth)}


def word_expression(node):
    tag, *args = node
    if tag == "one":
        return ".one"
    if tag == "power":
        return f".power {args[0]}"
    if tag == "mixed":
        return f".mixed {args[0]} {args[1]}"
    if tag == "mul":
        return f".mul word{args[0]} word{args[1]}"
    if tag in ("conj", "conjInv"):
        return f".{tag} {args[0]} word{args[1]}"
    raise registry.Rejected("unrecognized relative-radical word node")


def log2_exact(n):
    if type(n) is not int or n <= 0 or n & (n - 1):
        raise registry.Rejected("selected exact order is not a power of two")
    return n.bit_length() - 1


def header(spec, imports, description, instance_name):
    return "\n".join("import SymmetricSubgroupAsymptotics." + m for m in imports) + f'''

/-! {description}
Generated only by export_lean_carrier_profiles_selected.py --stage radicals. All finite equations
are kernel checked; no stored numerical carrier profile is a premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace {spec.namespace}
local instance {instance_name} : Group Source := {spec.source_module}.group

'''


def emit_radicals(spec, normals, searches):
    text = header(spec, ["PrimeRelativeRadicalWords", f"GeneratedCarrierNormal{spec.master}.States"],
                  f"Exact whole-original-group relative radicals of the {spec.normal_count} accepted {spec.master} states.",
                  "radicalCertificateSourceGroup")
    for i, (normal, search) in enumerate(zip(normals, searches)):
        r = search["target"]
        target = normals[r]
        ng, rg = len(normal["generators"]), len(target["generators"])
        target_order = len(target["rows"])
        rank = log2_exact(len(normal["rows"])) - log2_exact(target_order)
        if rank < 0:
            raise registry.Rejected("a radical has larger order than its original normal")
        text += f"namespace RadicalN{i}\n\n"
        for j, node in enumerate(search["nodes"]):
            text += (f"private def word{j} : PrimeRelativeRadicalWord (Fin {spec.generator_count}) (Fin {ng}) :=\n"
                     f"  {word_expression(node)}\n")
        words = [f'word{search["position"][g]}' for g in target["generators"]]
        words_expr = registry.legacy.lookup(words, "j.val") if rg else "Fin.elim0 j"
        text += f'''
private def radicalWords (j : Fin {rg}) : PrimeRelativeRadicalWord (Fin {spec.generator_count}) (Fin {ng}) :=
  {words_expr}

private theorem radicalWords_checked : ∀ j : Fin {rg},
    (radicalWords j).eval 2 generators N{i}.normalGenerators = N{r}.normalGenerators j := by
'''
        if rg:
            text += "  intro j\n  fin_cases j <;> decide +kernel\n"
        else:
            text += "  intro j\n  exact Fin.elim0 j\n"
        power_indices = [target["index"][x] for x in search["powers"]]
        mixed_indices = [[target["index"][x] for x in row] for row in search["mixed"]]
        power_expr = (registry.legacy.finfun(power_indices, target_order, "j.val")
                      if ng else "Fin.elim0 j")
        mixed_expr = (f'({registry.legacy.lookup([registry.legacy.arr(row) for row in mixed_indices], "j.val")} '
                      f': Array (Fin {target_order}))[i.val]!' if ng else "Fin.elim0 j")
        text += f'''
private def powerRow (j : Fin {ng}) : Fin {target_order} := {power_expr}
private def mixedRow (j : Fin {ng}) (i : Fin {spec.generator_count}) : Fin {target_order} := {mixed_expr}

private theorem power_checked : ∀ j : Fin {ng}, N{i}.normalGenerators j ^ 2 =
    (⟨N{r}.normalCertificate.rows (powerRow j)⟩ : Source) := by
'''
        if ng:
            text += "  intro j\n  fin_cases j <;> decide +kernel\n"
        else:
            text += "  intro j\n  exact Fin.elim0 j\n"
        text += f'''
private theorem mixed_checked : ∀ (j : Fin {ng}) (i : Fin {spec.generator_count}),
    ⁅N{i}.normalGenerators j, generators i⁆ =
      (⟨N{r}.normalCertificate.rows (mixedRow j i)⟩ : Source) := by
'''
        if ng:
            text += "  intro j\n  fin_cases j <;> decide +kernel\n"
        else:
            text += "  intro j\n  exact Fin.elim0 j\n"
        text += f'''
theorem radical_eq : primeRelativeRadical 2 N{i}.kernel = N{r}.kernel := by
  apply primeRelativeRadical_eq_of_generator_words 2 N{i}.kernel N{r}.kernel
    generators generators_full N{i}.normalGenerators rfl N{r}.normalGenerators rfl
    radicalWords radicalWords_checked
  · intro j
    rw [power_checked]
    exact binaryNormalRow_mem N{r}.normalCertificate _
  · intro j k
    rw [mixed_checked]
    exact binaryNormalRow_mem N{r}.normalCertificate _

theorem head_eq : Module.finrank (ZMod 2) (primeRelativeCharacters 2 N{i}.kernel) = {rank} := by
  apply primeRelativeHead_eq_of_radical_card 2 N{i}.kernel N{r}.kernel {rank} radical_eq
  norm_num [N{i}.kernel_card, N{r}.kernel_card]

end RadicalN{i}

'''
    return text + f"end {spec.namespace}\n"


def emit_profiles(spec, normals, searches):
    targets = [s["target"] for s in searches]
    ranks = [log2_exact(len(n["rows"])) - log2_exact(len(normals[r]["rows"]))
             for n, r in zip(normals, targets)]
    orders = [log2_exact(len(n["rows"])) for n in normals]
    text = header(spec, [f"GeneratedCarrierNormal{spec.master}.Registry",
                  f"GeneratedCarrierNormal{spec.master}.Radicals", "RelativeAmbientTransport"],
                  f"Actual {spec.master} head, order, and second-radical-head bindings for every original normal.",
                  "radicalProfilesSourceGroup")
    text += f'''def radicalIndex (i : Fin {spec.normal_count}) : Fin {spec.normal_count} :=
  {registry.legacy.finfun(targets, spec.normal_count)}

def headRank (i : Fin {spec.normal_count}) : ℕ := {registry.legacy.lookup(ranks)}
def orderLog (i : Fin {spec.normal_count}) : ℕ := {registry.legacy.lookup(orders)}

theorem state_radical_eq (i : Fin {spec.normal_count}) :
    primeRelativeRadical 2 (states i).kernel = (states (radicalIndex i)).kernel := by
  fin_cases i
'''
    text += "".join(f"  · exact RadicalN{i}.radical_eq\n" for i in range(spec.normal_count))
    text += f'''
theorem state_head_eq (i : Fin {spec.normal_count}) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (states i).kernel) = headRank i := by
  fin_cases i
'''
    text += "".join(f"  · exact RadicalN{i}.head_eq\n" for i in range(spec.normal_count))
    text += f'''
theorem state_card (i : Fin {spec.normal_count}) : Nat.card (states i).kernel = 2 ^ orderLog i := by
  fin_cases i
'''
    text += "".join(f"  · exact N{i}.kernel_card\n" for i in range(spec.normal_count))
    text += f'''
/-- The second head uses the radical as a normal of the SAME original Source. -/
theorem state_radical_head_eq (i : Fin {spec.normal_count}) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2
      (primeRelativeRadical 2 (states i).kernel)) = headRank (radicalIndex i) :=
  (primeRelativeHead_eq_of_subgroup_eq 2 _ _ (state_radical_eq i)).trans
    (state_head_eq (radicalIndex i))

abbrev Original := Subgroup.closure (Set.range {spec.source_module}.generators)

def originalKernel (i : Fin {spec.normal_count}) : Subgroup Original :=
  (states i).kernel.map {spec.source_module}.originalEquiv.toMonoidHom

instance originalKernel_normal (i : Fin {spec.normal_count}) : (originalKernel i).Normal :=
  Subgroup.Normal.map inferInstance _ {spec.source_module}.originalEquiv.surjective

theorem original_radical_eq (i : Fin {spec.normal_count}) :
    primeRelativeRadical 2 (originalKernel i) = originalKernel (radicalIndex i) := by
  letI : ((states i).kernel.map {spec.source_module}.originalEquiv.toMonoidHom).Normal :=
    originalKernel_normal i
  exact (primeRelativeRadical_map_equiv 2 {spec.source_module}.originalEquiv
    (states i).kernel).symm.trans
      (congrArg (fun K : Subgroup Source =>
        K.map {spec.source_module}.originalEquiv.toMonoidHom) (state_radical_eq i))

theorem original_head_eq (i : Fin {spec.normal_count}) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (originalKernel i)) = headRank i :=
  (relativeCharacterAmbientCongr 2 {spec.source_module}.originalEquiv
    (states i).kernel (originalKernel i) rfl).finrank_eq.trans (state_head_eq i)

theorem original_card (i : Fin {spec.normal_count}) : Nat.card (originalKernel i) = 2 ^ orderLog i :=
  (Nat.card_congr (normalAmbientEquiv {spec.source_module}.originalEquiv
    (states i).kernel (originalKernel i) rfl).toEquiv).symm.trans (state_card i)

theorem original_radical_head_eq (i : Fin {spec.normal_count}) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2
      (primeRelativeRadical 2 (originalKernel i))) = headRank (radicalIndex i) :=
  (primeRelativeHead_eq_of_subgroup_eq 2 _ _ (original_radical_eq i)).trans
    (original_head_eq (radicalIndex i))

private theorem radical_congr (N R : Subgroup Original) [N.Normal] [R.Normal] (h : N = R) :
    primeRelativeRadical 2 N = primeRelativeRadical 2 R := by
  subst R
  rfl

theorem original_second_radical_eq (i : Fin {spec.normal_count}) :
    primeRelativeRadical 2 (primeRelativeRadical 2 (originalKernel i)) =
      originalKernel (radicalIndex (radicalIndex i)) :=
  (radical_congr _ _ (original_radical_eq i)).trans (original_radical_eq (radicalIndex i))

/-- Exhaustive binding uses the accepted original-normal registry, not
the stored profile fields. The maximum head m and quotient fields c,g
remain separate obligations. In particular no inequality a2 ≤ m is used. -/
theorem complete_original_radical_profiles (N : Subgroup Original) [N.Normal] :
    ∃ i : Fin {spec.normal_count}, originalKernel i = N ∧
      primeRelativeRadical 2 N = originalKernel (radicalIndex i) ∧
      primeRelativeRadical 2 (primeRelativeRadical 2 N) =
        originalKernel (radicalIndex (radicalIndex i)) ∧
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) = headRank i ∧
      Nat.card N = 2 ^ orderLog i ∧
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 (primeRelativeRadical 2 N)) =
        headRank (radicalIndex i) := by
  obtain ⟨i, hi⟩ := complete_original N
  change originalKernel i = N at hi
  subst N
  exact ⟨i, rfl, original_radical_eq i, original_second_radical_eq i,
    original_head_eq i, original_card i, original_radical_head_eq i⟩

'''
    return text + f"end {spec.namespace}\n"


def radical_stage(spec, budget):
    ambient, normals, lookup, input_bytes = selected_data(spec, budget)
    searches = []
    total_nodes = 0
    for normal in normals:
        search = radical_search(spec, ambient, normal, lookup, budget)
        total_nodes += len(search["nodes"])
        if total_nodes > min(MAX_WORD_NODES_TOTAL, spec.normal_count * spec.source_rows):
            raise registry.Rejected("selected total word-node cap exceeded")
        searches.append(search)
    texts = {"Radicals.lean": emit_radicals(spec, normals, searches),
             "RadicalProfiles.lean": emit_profiles(spec, normals, searches)}
    targets = [s["target"] for s in searches]
    heads = [log2_exact(len(n["rows"])) - log2_exact(len(normals[r]["rows"]))
             for n, r in zip(normals, targets)]
    details = {
        "stage": "radicals", "source_rows": spec.source_rows,
        "normal_states": spec.normal_count, "normal_rows": sum(len(n["rows"]) for n in normals),
        "original_generators": spec.generator_count,
        "radical_state_indices_zero_based": targets,
        "computed_head_ranks": heads, "computed_second_head_ranks": [heads[r] for r in targets],
        "word_nodes": total_nodes, "max_word_depth": max(s["depth"] for s in searches),
        "decompressed_bytes": input_bytes, "stored_profile_fields_used": False,
        "axis_maximum_bound": False, "quotient_invariants_bound": False,
    }
    return texts, details


# These leaves are already kernel checked; digests prevent a stale template
# from silently binding to a different API or a different original action.
DERIVED_HELPERS = {
    "DerivedGeneratorWords.lean": "d957ba9eb155df89e5f6d598ec67e5ea3005f6d99fed45a827c9f47854c241eb",
    "FiniteQuotientInvariantCertificates.lean": "a2e55e8c50975355526a6295e7baf6d24afecf15c8b946f802c500e2d426d1ba",
}
QUOTIENT_HELPERS = {
    "FiniteQuotientInvariantMasks.lean": "1699c394fc62e2ef753bd9020d50556ac8c975ac9ca1bdbcfbed1a976491eaf8",
}
ACCEPTED_RADICALS = {
    "8T26": {
        "Radicals.lean": "2b5928ad6a11c8b6ad784fd3960709c125cd0b0c4490cc874d9c5bac87fae836",
        "RadicalProfiles.lean": "cc2a183efad083b995844c0c335bd48f103dfca600661c1ceb0dcb5146b316da",
    },
}
MAX_DERIVED_WORD_DEPTH = 16


def checked_stage_prerequisites(spec, stage):
    paths = {}
    formal = ROOT / "formal/SymmetricSubgroupAsymptotics"
    if stage in ("derived", "quotients"):
        paths.update({formal / name: digest for name, digest in DERIVED_HELPERS.items()})
    if stage == "quotients":
        paths.update({formal / name: digest for name, digest in QUOTIENT_HELPERS.items()})
    if stage == "heads":
        paths.update({formal / name: digest for name, digest in HEAD_HELPERS.items()})
    if stage in ("quotients", "heads"):
        paths.update({spec.output_directory / name: digest
                      for name, digest in ACCEPTED_RADICALS[spec.master].items()})
    for path, expected in paths.items():
        if registry.sha256(registry.read_small(path, MAX_OUTPUT_BYTES)) != expected:
            raise registry.Rejected(f"accepted selected stage prerequisite changed: {path.name}")
    return paths


def commutator(a, b, budget):
    return budget.compose(budget.compose(budget.compose(a, b), registry.legacy.inv(a)),
                          registry.legacy.inv(b))


def source_rows(spec, ambient, budget):
    table = registry.bounded_table_factory(spec, budget)(ambient, 8)
    rows = [registry.legacy.unpack(c, 8) for c in table["codes"]]
    if len(rows) != spec.source_rows:
        raise registry.Rejected("selected source-row count changed")
    return rows


def selected_derived_words(spec, ambient, source, lookup, budget):
    """Close only original commutator words inside the bounded original group.

    The eventual registry state is determined by this literal closure. Its
    equality to G' is not trusted: Lean separately checks all upper original
    generator commutators and lower derived words for its entire tuple.
    """
    allowed = set(source)
    identity = tuple(range(8))
    rows, positions, nodes, depths = [identity], {identity: 0}, [("one",)], [0]

    def add(value, node, depth):
        budget.tick()
        if value not in allowed:
            raise registry.Rejected("original derived word escaped the selected source")
        if value in positions:
            return positions[value]
        if len(rows) >= spec.source_rows or depth > MAX_DERIVED_WORD_DEPTH:
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
    target = lookup.get(frozenset(rows))
    if target is None:
        raise registry.Rejected("actual derived word closure is absent from the selected registry")
    return {"target": target, "rows": rows, "positions": positions, "nodes": nodes,
            "commutators": commutators, "max_depth": max(depths)}


def derived_word_expression(node):
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


def normal_membership_masks(normals, source, budget):
    masks = []
    for normal in normals:
        nset = set(normal["rows"])
        budget.tick(len(source))
        masks.append([x in nset for x in source])
    return {"normal": masks}


def masks_and_counts(ambient, normals, source, derived, budget):
    masks = normal_membership_masks(normals, source, budget)
    center_masks, intersections = [], []
    dset = set(normals[derived]["rows"])
    drows = len(dset)
    source_commutators = [[commutator(x, g, budget) for g in ambient] for x in source]
    for normal in normals:
        nset = set(normal["rows"])
        budget.tick(len(source) * len(ambient))
        center_masks.append([all(c in nset for c in row) for row in source_commutators])
        intersections.append(len(nset & dset))
    centers = [sum(mask) for mask in center_masks]
    center_orders, derived_orders = [], []
    for normal, c, b in zip(normals, centers, intersections):
        if b == 0 or c % len(normal["rows"]) or drows % b:
            raise registry.Rejected("selected exact quotient cardinal division failed")
        center_orders.append(c // len(normal["rows"]))
        derived_orders.append(drows // b)
    return {**masks, "center": center_masks, "center_preimage": centers,
            "intersection": intersections, "center_orders": center_orders,
            "derived_orders": derived_orders,
            "center_logs": [log2_exact(c) for c in center_orders],
            "derived_logs": [log2_exact(g) for g in derived_orders]}


def quotient_header(spec, imports, description, instance_name):
    return "\n".join("import SymmetricSubgroupAsymptotics." + m for m in imports) + f'''

/-! {description}
Selected by export_lean_carrier_profiles_selected.py. Stored carrier profiles
are not proof inputs; every mask is bound to the same original elements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace {spec.namespace}
local instance {instance_name} : Group Source := {spec.source_module}.group

'''


def emit_derived(spec, normals, words, masks):
    r = words["target"]
    drows = len(normals[r]["rows"])
    text = quotient_header(spec, [f"GeneratedCarrierNormal{spec.master}.States", "DerivedGeneratorWords",
                   "FiniteQuotientInvariantCertificates"],
                  f"Literal membership masks and the actual derived subgroup of {spec.master}.",
                  "derivedMasksSourceGroup")
    text += f'''def derivedIndex : Fin {spec.normal_count} := {r}

def sourceIndexEquiv : Fin {spec.source_rows} ≃ Source where
  toFun i := ⟨i⟩
  invFun x := x.index
  left_inv _ := rfl
  right_inv _ := rfl

/-- Membership in the same accepted {spec.normal_count} literal normal subgroups. -/
def normalMask (i : Fin {spec.normal_count}) (x : Fin {spec.source_rows}) : Bool :=
  {bool_matrix(masks["normal"])}

'''
    for i, normal in enumerate(normals):
        text += f'''private theorem normalMask_checked{i} : ∀ x : Fin {spec.source_rows},
    normalMask {i} x = true ↔ ∃ j : Fin {len(normal["rows"])},
      N{i}.normalCertificate.rows j = x :=
  {registry.legacy.checks(spec.source_rows)}

'''
    text += f'''theorem normalMask_mem (i : Fin {spec.normal_count}) (x : Source) :
    normalMask i x.index = true ↔ x ∈ (states i).kernel := by
  fin_cases i
'''
    for i in range(spec.normal_count):
        text += (f"  · exact (normalMask_checked{i} x.index).trans\n"
                 f"      (N{i}.normalCertificate.mem_closure_iff x).symm\n")
    text += "\n"
    for i, node in enumerate(words["nodes"]):
        text += f"private def derivedWord{i} : DerivedGeneratorWord (Fin {spec.generator_count}) := {derived_word_expression(node)}\n"
    dg = normals[r]["generators"]
    word_names = [f'derivedWord{words["positions"][g]}' for g in dg]
    words_expr = registry.legacy.lookup(word_names, "j.val") if dg else "Fin.elim0 j"
    comm_rows = [[normals[r]["index"][v] for v in row]
                 for row in words["commutators"]]
    text += f'''
private def derivedWords (j : Fin {len(dg)}) : DerivedGeneratorWord (Fin {spec.generator_count}) :=
  {words_expr}

private theorem derivedWords_checked : ∀ j : Fin {len(dg)},
    (derivedWords j).eval generators = N{r}.normalGenerators j := by
  intro j
  {"fin_cases j <;> decide +kernel" if dg else "exact Fin.elim0 j"}

private def generatorCommutatorRow (i j : Fin {spec.generator_count}) : Fin {drows} :=
  {registry.legacy.mat(comm_rows, f"Fin {drows}")}

private theorem generatorCommutators_checked : ∀ i j : Fin {spec.generator_count},
    ⁅generators i, generators j⁆ =
      (⟨N{r}.normalCertificate.rows (generatorCommutatorRow i j)⟩ : Source) := by
  decide +kernel

/-- N{r} is identified with the actual derived subgroup in both directions. -/
theorem source_derived_eq : commutator Source = N{r}.kernel := by
  apply le_antisymm
  · apply commutator_le_of_generator_commutators N{r}.kernel generators generators_full
    intro i j
    rw [generatorCommutators_checked]
    exact binaryNormalRow_mem N{r}.normalCertificate _
  · change Subgroup.closure (Set.range N{r}.normalGenerators) ≤ commutator Source
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    rw [← derivedWords_checked j]
    exact (derivedWords j).eval_mem_commutator generators

theorem source_derived_state_eq : commutator Source = (states derivedIndex).kernel :=
  source_derived_eq

theorem source_derived_card : Nat.card (commutator Source) = {drows} := by
  rw [source_derived_eq]
  exact N{r}.kernel_card

'''
    return text + f"end {spec.namespace}\n"


def emit_quotients(spec, normals, derived, masks):
    r = derived
    drows = len(normals[r]["rows"])
    text = quotient_header(spec, [f"GeneratedCarrierNormal{spec.master}.Derived",
                   f"GeneratedCarrierNormal{spec.master}.RadicalProfiles", "FiniteQuotientInvariantMasks"],
                  f"Exact center and derived orders of all {spec.normal_count} original {spec.master} quotients.",
                  "quotientProfilesSourceGroup")
    text += f'''def centerMask (i : Fin {spec.normal_count}) (x : Fin {spec.source_rows}) : Bool :=
  {bool_matrix(masks["center"])}

def intersectionMask (i : Fin {spec.normal_count}) (x : Fin {spec.source_rows}) : Bool :=
  normalMask i x && normalMask {r} x

def centerLog (i : Fin {spec.normal_count}) : ℕ := {registry.legacy.lookup(masks["center_logs"])}
def derivedLog (i : Fin {spec.normal_count}) : ℕ := {registry.legacy.lookup(masks["derived_logs"])}
def intersectionOrder (i : Fin {spec.normal_count}) : ℕ := {registry.legacy.lookup(masks["intersection"])}

'''
    for i in range(spec.normal_count):
        text += f'''private theorem centerMask_checked{i} : ∀ x : Fin {spec.source_rows},
    centerMask {i} x = true ↔ ∀ j : Fin {spec.generator_count},
      normalMask {i} (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  {registry.legacy.checks(spec.source_rows)}

private theorem centerMask_card{i} :
    Fintype.card {{x : Fin {spec.source_rows} // centerMask {i} x = true}} = {masks["center_preimage"][i]} := by
  decide +kernel

private theorem intersectionMask_card{i} :
    Fintype.card {{x : Fin {spec.source_rows} // intersectionMask {i} x = true}} = {masks["intersection"][i]} := by
  decide +kernel

'''
    text += f'''theorem centerMask_test (i : Fin {spec.normal_count}) (x : Fin {spec.source_rows}) :
    centerMask i x = true ↔ ∀ j : Fin {spec.generator_count},
      ⁅(⟨x⟩ : Source), generators j⁆ ∈ (states i).kernel := by
  have h : centerMask i x = true ↔ ∀ j : Fin {spec.generator_count},
      normalMask i (⁅(⟨x⟩ : Source), generators j⁆).index = true := by
    fin_cases i
'''
    text += "".join(f"    · exact centerMask_checked{i} x\n" for i in range(spec.normal_count))
    text += f'''  exact h.trans (forall_congr' (fun j => normalMask_mem i _))

theorem intersectionMask_mem (i : Fin {spec.normal_count}) (x : Fin {spec.source_rows}) :
    intersectionMask i x = true ↔
      (⟨x⟩ : Source) ∈ (states i).kernel ⊓ commutator Source := by
  rw [source_derived_eq]
  change (normalMask i x && normalMask {r} x) = true ↔ _
  rw [Bool.and_eq_true]
  exact and_congr (normalMask_mem i ⟨x⟩) (normalMask_mem {r} ⟨x⟩)

theorem centerMask_card (i : Fin {spec.normal_count}) :
    Nat.card {{x : Fin {spec.source_rows} // centerMask i x = true}} =
      2 ^ centerLog i * Nat.card (states i).kernel := by
  rw [Nat.card_eq_fintype_card]
  fin_cases i
'''
    text += "".join(f"  · change Fintype.card {{x : Fin {spec.source_rows} // centerMask {i} x = true}} =\n"
                    f"      2 ^ {masks['center_logs'][i]} * Nat.card N{i}.kernel\n"
                    f"    rw [N{i}.kernel_card]\n"
                    f"    exact centerMask_card{i}\n" for i in range(spec.normal_count))
    text += f'''
theorem intersectionMask_card (i : Fin {spec.normal_count}) :
    Nat.card {{x : Fin {spec.source_rows} // intersectionMask i x = true}} = intersectionOrder i := by
  rw [Nat.card_eq_fintype_card]
  fin_cases i
'''
    text += "".join(f"  · exact intersectionMask_card{i}\n" for i in range(spec.normal_count))
    text += f'''
theorem source_intersection_card (i : Fin {spec.normal_count}) :
    Nat.card ↥((states i).kernel ⊓ commutator Source) = intersectionOrder i := by
  let e := sourceIndexEquiv.subtypeEquiv (intersectionMask_mem i)
  exact (Nat.card_congr e).symm.trans (intersectionMask_card i)

theorem source_quotient_center_card (i : Fin {spec.normal_count}) :
    Nat.card (Subgroup.center (Source ⧸ (states i).kernel)) = 2 ^ centerLog i :=
  quotientCenter_card_of_mask (states i).kernel generators generators_full sourceIndexEquiv
    (fun x => centerMask i x = true) (centerMask_test i) _ (centerMask_card i)

theorem source_quotient_derived_card (i : Fin {spec.normal_count}) :
    Nat.card (commutator (Source ⧸ (states i).kernel)) = 2 ^ derivedLog i := by
  apply quotientCommutator_card_of_inf_card
  rw [source_derived_card, source_intersection_card]
  fin_cases i <;> decide +kernel

/-- The original tuple and all original elements are transported together. -/
def originalAmbientGenerators (j : Fin {spec.generator_count}) : Original :=
  {spec.source_module}.originalEquiv (generators j)

theorem originalAmbientGenerators_full :
    Subgroup.closure (Set.range originalAmbientGenerators) = ⊤ := by
  have h := congrArg (fun K : Subgroup Source =>
    K.map {spec.source_module}.originalEquiv.toMonoidHom) generators_full
  dsimp only at h
  rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective
    {spec.source_module}.originalEquiv.toMonoidHom
    {spec.source_module}.originalEquiv.surjective] at h
  have hs : {spec.source_module}.originalEquiv.toMonoidHom '' Set.range generators =
      Set.range originalAmbientGenerators := by
    ext x
    simp [originalAmbientGenerators]
  rwa [hs] at h

def originalIndexEquiv : Fin {spec.source_rows} ≃ Original :=
  sourceIndexEquiv.trans {spec.source_module}.originalEquiv.toEquiv

theorem originalEquiv_mem_originalKernel (i : Fin {spec.normal_count}) (x : Source) :
    {spec.source_module}.originalEquiv x ∈ originalKernel i ↔ x ∈ (states i).kernel := by
  constructor
  · rintro ⟨y, hy, he⟩
    exact {spec.source_module}.originalEquiv.injective he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem original_derived_eq : commutator Original = originalKernel {r} := by
  have h : (commutator Source).map {spec.source_module}.originalEquiv.toMonoidHom =
      commutator Original := by
    have hr : {spec.source_module}.originalEquiv.toMonoidHom.range = ⊤ :=
      MonoidHom.range_eq_top.mpr {spec.source_module}.originalEquiv.surjective
    rw [map_commutator_eq, hr, ← commutator_def]
  exact h.symm.trans (congrArg (fun K : Subgroup Source =>
    K.map {spec.source_module}.originalEquiv.toMonoidHom) source_derived_eq)

theorem original_derived_card : Nat.card (commutator Original) = {drows} := by
  rw [original_derived_eq]
  exact original_card {r}

theorem original_centerMask_test (i : Fin {spec.normal_count}) (x : Fin {spec.source_rows}) :
    centerMask i x = true ↔ ∀ j : Fin {spec.generator_count},
      ⁅originalIndexEquiv x, originalAmbientGenerators j⁆ ∈ originalKernel i := by
  apply (centerMask_test i x).trans
  apply forall_congr'
  intro j
  have h := originalEquiv_mem_originalKernel i ⁅(⟨x⟩ : Source), generators j⁆
  simpa only [map_commutatorElement] using h.symm

theorem original_intersectionMask_mem (i : Fin {spec.normal_count}) (x : Fin {spec.source_rows}) :
    intersectionMask i x = true ↔
      originalIndexEquiv x ∈ originalKernel i ⊓ commutator Original := by
  rw [original_derived_eq]
  change (normalMask i x && normalMask {r} x) = true ↔ _
  rw [Bool.and_eq_true]
  exact and_congr ((normalMask_mem i ⟨x⟩).trans
    (originalEquiv_mem_originalKernel i ⟨x⟩).symm)
    ((normalMask_mem {r} ⟨x⟩).trans (originalEquiv_mem_originalKernel {r} ⟨x⟩).symm)

theorem original_intersection_card (i : Fin {spec.normal_count}) :
    Nat.card ↥(originalKernel i ⊓ commutator Original) = intersectionOrder i := by
  let e := originalIndexEquiv.subtypeEquiv (original_intersectionMask_mem i)
  exact (Nat.card_congr e).symm.trans (intersectionMask_card i)

theorem original_quotient_center_card (i : Fin {spec.normal_count}) :
    Nat.card (Subgroup.center (Original ⧸ originalKernel i)) = 2 ^ centerLog i := by
  apply quotientCenter_card_of_mask (originalKernel i) originalAmbientGenerators
    originalAmbientGenerators_full originalIndexEquiv (fun x => centerMask i x = true)
    (original_centerMask_test i)
  have h := centerMask_card i
  rw [state_card] at h
  simpa only [original_card] using h

theorem original_quotient_derived_card (i : Fin {spec.normal_count}) :
    Nat.card (commutator (Original ⧸ originalKernel i)) = 2 ^ derivedLog i := by
  apply quotientCommutator_card_of_inf_card
  rw [original_derived_card, original_intersection_card]
  fin_cases i <;> decide +kernel

/-- Every actual original normal has the certified quotient fields c,g.
The independent head-maximum and physical-weight tasks are not assumed. -/
theorem complete_original_quotient_profiles (N : Subgroup Original) [N.Normal] :
    ∃ i : Fin {spec.normal_count}, originalKernel i = N ∧
      Nat.card (Subgroup.center (Original ⧸ N)) = 2 ^ centerLog i ∧
      Nat.card (commutator (Original ⧸ N)) = 2 ^ derivedLog i := by
  obtain ⟨i, hi⟩ := complete_original N
  change originalKernel i = N at hi
  subst N
  exact ⟨i, rfl, original_quotient_center_card i, original_quotient_derived_card i⟩

'''
    return text + f"end {spec.namespace}\n"


def derived_stage_data(spec, budget):
    ambient, normals, lookup, input_bytes = selected_data(spec, budget)
    source = source_rows(spec, ambient, budget)
    words = selected_derived_words(spec, ambient, source, lookup, budget)
    return ambient, normals, source, words, input_bytes


def derived_stage(spec, budget):
    _, normals, source, words, input_bytes = derived_stage_data(spec, budget)
    masks = normal_membership_masks(normals, source, budget)
    return {"Derived.lean": emit_derived(spec, normals, words, masks)}, {
        "stage": "derived", "source_rows": spec.source_rows,
        "normal_states": spec.normal_count, "original_generators": spec.generator_count,
        "derived_state_index_zero_based": words["target"],
        "derived_rows": len(words["rows"]), "derived_word_nodes": len(words["nodes"]),
        "derived_word_max_depth": words["max_depth"],
        "normal_membership_bits": spec.normal_count * spec.source_rows,
        "decompressed_bytes": input_bytes, "stored_profile_fields_used": False,
        "axis_maximum_bound": False, "quotient_invariants_bound": False,
    }


def quotient_stage(spec, budget):
    ambient, normals, source, words, input_bytes = derived_stage_data(spec, budget)
    masks = masks_and_counts(ambient, normals, source, words["target"], budget)
    expected_derived = emit_derived(spec, normals, words, masks).encode("utf-8")
    derived_path = spec.output_directory / "Derived.lean"
    if (not derived_path.exists()
            or registry.read_small(derived_path, MAX_OUTPUT_BYTES) != expected_derived):
        raise registry.Rejected("derived-stage prerequisite missing or not byte-identical; run/check that stage first")
    # The root must check Derived.lean before selecting this stage. Byte
    # matching here binds the data; it does not claim a successful Lean check.
    return {"QuotientProfiles.lean": emit_quotients(spec, normals, words["target"], masks)}, {
        "stage": "quotients", "source_rows": spec.source_rows,
        "normal_states": spec.normal_count, "original_generators": spec.generator_count,
        "derived_state_index_zero_based": words["target"],
        "derived_rows": len(words["rows"]), "derived_word_nodes": len(words["nodes"]),
        "derived_word_max_depth": words["max_depth"],
        "center_tests": spec.normal_count * spec.source_rows * spec.generator_count,
        "center_preimage_orders": masks["center_preimage"], "intersection_orders": masks["intersection"],
        "computed_center_logs": masks["center_logs"], "computed_derived_logs": masks["derived_logs"],
        "required_stage_sources": {str(derived_path): registry.sha256(expected_derived)},
        "decompressed_bytes": input_bytes, "stored_profile_fields_used": False,
        "axis_maximum_bound": False, "quotient_invariants_bound": True,
    }


MAX_HEAD_LOOKUP_TOKENS = 4096
MAX_HEAD_LOOKUP_DEPTH = 64
HEAD_INPUT_BYTE_CEILING = 1048576
HEAD_HELPERS = {
    "BinaryNormalRegistryHeads.lean": "a6435be9ef633060d64e3a59d6f3e6eda6728fa84218b77c04cdfd8b4a32ac57",
}


class NumeralLookup:
    """Parse only the existing balanced lookup grammar, never Python/Lean eval."""

    def __init__(self, text: str, row_bound: int, budget):
        self.row_bound = row_bound
        pattern = r"i\.val|if|then|else|Fin|[0-9]+|[():<]"
        self.tokens = re.findall(pattern, text)
        if re.sub(r"\s+", "", text) != "".join(self.tokens):
            raise registry.Rejected("unrecognized selected lookup syntax")
        if len(self.tokens) > MAX_HEAD_LOOKUP_TOKENS:
            raise registry.Rejected("selected lookup token cap exceeded")
        self.position = 0
        self.budget = budget
        self.tree = self.expression(0)
        if self.position != len(self.tokens):
            raise registry.Rejected("trailing selected lookup tokens")

    def pop(self, expected=None):
        self.budget.tick()
        if self.position >= len(self.tokens):
            raise registry.Rejected("truncated selected lookup")
        value = self.tokens[self.position]
        self.position += 1
        if expected is not None and value != expected:
            raise registry.Rejected("malformed selected lookup")
        return value

    def natural(self):
        value = self.pop()
        if not value.isdecimal() or len(value) > 3:
            raise registry.Rejected("selected lookup numeral out of bounds")
        return int(value)

    def expression(self, depth):
        if depth > MAX_HEAD_LOOKUP_DEPTH:
            raise registry.Rejected("selected lookup depth cap exceeded")
        first = self.pop()
        if first == "(":
            tree = self.expression(depth + 1)
            if self.position < len(self.tokens) and self.tokens[self.position] == ":":
                self.pop(":")
                self.pop("Fin")
                if self.natural() != self.row_bound:
                    raise registry.Rejected("unexpected selected row type")
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
        raise registry.Rejected("selected lookup must contain only numeral leaves")

    def value(self, index):
        tree = self.tree
        while isinstance(tree, tuple):
            self.budget.tick()
            split, left, right = tree
            tree = left if index < split else right
        self.budget.tick()
        return tree


def selected_head_values(spec, inputs, budget):
    text = inputs["States.lean"].decode("utf-8")
    blocks = list(re.finditer(r"^namespace N([0-9]+)\n(.*?)^end N\1$", text,
                              re.MULTILINE | re.DOTALL))
    if [int(m.group(1)) for m in blocks] != list(range(spec.normal_count)):
        raise registry.Rejected("unexpected selected original state namespaces")
    normals = []
    for block in blocks:
        budget.tick()
        row_defs = re.findall(rf"^private def rows \(i : Fin ([0-9]+)\) : Fin {spec.source_rows} := (.+)$",
                              block.group(2), re.MULTILINE)
        if len(row_defs) != 1:
            raise registry.Rejected("missing or repeated complete state-row definition")
        count, expression = row_defs[0]
        count = int(count)
        if not 1 <= count <= spec.source_rows:
            raise registry.Rejected("selected state-row cap exceeded")
        lookup = NumeralLookup(expression, spec.source_rows, budget)
        rows = [lookup.value(i) for i in range(count)]
        if len(set(rows)) != count or any(not 0 <= x < spec.source_rows for x in rows):
            raise registry.Rejected("selected complete row codes are not distinct bounded row values")
        normals.append(frozenset(rows))
    if sum(map(len, normals)) > registry.NORMAL_ROW_TOTAL_CEILING:
        raise registry.Rejected("selected total normal-row cap exceeded")
    profiles = inputs["RadicalProfiles.lean"].decode("utf-8")
    head_defs = re.findall(rf"^def headRank \(i : Fin {spec.normal_count}\) : ℕ := (.+)$", profiles,
                           re.MULTILINE)
    if len(head_defs) != 1:
        raise registry.Rejected("missing or repeated actual headRank definition")
    lookup = NumeralLookup(head_defs[0], spec.source_rows, budget)
    heads = [lookup.value(i) for i in range(spec.normal_count)]
    if any(not 0 <= h <= spec.order_log for h in heads):
        raise registry.Rejected("selected actual head value out of bounds")
    derived_defs = re.findall(rf"^def derivedIndex : Fin {spec.normal_count} := ([0-9]+)$",
                              inputs["Derived.lean"].decode("utf-8"), re.MULTILINE)
    if len(derived_defs) != 1 or not 0 <= int(derived_defs[0]) < spec.normal_count:
        raise registry.Rejected("missing or invalid actual derived-state index")
    derived = int(derived_defs[0])
    maxima = []
    containments = []
    for target in range(spec.normal_count):
        eligible = []
        for j in range(spec.normal_count):
            budget.tick(spec.source_rows)
            if normals[j] <= normals[target] and normals[j] <= normals[derived]:
                eligible.append(j)
        maxima.append(max((heads[j] for j in eligible), default=0))
        containments.append(eligible)
    return maxima, heads, containments, derived


def emit_heads(spec, maxima):
    checks = ""
    for i in range(spec.normal_count):
        checks += f'''private theorem derivedHeadRank_checked{i} :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j {i} && normalInDerived j) = derivedHeadRank {i} := by
  decide +kernel

'''
    branches = "".join(f"  · exact derivedHeadRank_checked{i}\n" for i in range(spec.normal_count))
    return f'''import SymmetricSubgroupAsymptotics.BinaryNormalRegistryHeads
import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal{spec.master}.Derived
import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal{spec.master}.RadicalProfiles

/-! Actual m-values for the complete literal {spec.master} normal registry.
Generated only by export_lean_carrier_profiles_selected.py --stage heads. Every head and containment
is bound to an original subgroup; no stored carrier profile is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace {spec.namespace}
local instance headMaximaSourceGroup : Group Source := {spec.source_module}.group

/-- Containment is computed from the checked complete original element masks. -/
def normalBelow (j i : Fin {spec.normal_count}) : Bool :=
  decide (∀ x : Fin {spec.source_rows}, normalMask j x = true → normalMask i x = true)

theorem normalBelow_iff (j i : Fin {spec.normal_count}) :
    normalBelow j i = true ↔ (states j).kernel ≤ (states i).kernel := by
  simp only [normalBelow, decide_eq_true_eq]
  constructor
  · intro h x hx
    exact (normalMask_mem i x).mp (h x.index ((normalMask_mem j x).mpr hx))
  · intro h x hx
    exact (normalMask_mem i (⟨x⟩ : Source)).mpr
      (h ((normalMask_mem j (⟨x⟩ : Source)).mp hx))

def normalInDerived (j : Fin {spec.normal_count}) : Bool := normalBelow j derivedIndex

theorem normalInDerived_iff (j : Fin {spec.normal_count}) :
    normalInDerived j = true ↔ (states j).kernel ≤ commutator Source := by
  change normalBelow j derivedIndex = true ↔ (states j).kernel ≤ commutator Source
  simpa only [source_derived_state_eq] using normalBelow_iff j derivedIndex

/-- The finite maximum of proved heads below N and the actual derived subgroup. -/
def derivedHeadRank (i : Fin {spec.normal_count}) : ℕ := {registry.legacy.lookup(maxima)}

{checks}private theorem derivedHeadRank_checked : ∀ i : Fin {spec.normal_count},
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j i && normalInDerived j) = derivedHeadRank i := by
  intro i
  fin_cases i
{branches}
theorem state_derived_head_eq (i : Fin {spec.normal_count}) :
    primeNormalHeadMax 2 ((states i).kernel ⊓ commutator Source) = derivedHeadRank i :=
  registry.axisNormalHeadMax_eq_of_finiteMaximum source_isPGroup 2
    headRank state_head_eq normalBelow normalBelow_iff normalInDerived
    normalInDerived_iff derivedHeadRank derivedHeadRank_checked i

/-- The same m-value concerns the original literal Fin8 action and all of its
ambient-normal subgroups, transported by its specified source equivalence. -/
theorem original_derived_head_eq (i : Fin {spec.normal_count}) :
    primeNormalHeadMax 2 (originalKernel i ⊓ commutator Original) = derivedHeadRank i :=
  (registry.axisNormalHeadMax_map_eq_finiteMaximum source_isPGroup 2
    {spec.source_module}.originalEquiv headRank original_head_eq normalBelow
    normalBelow_iff normalInDerived normalInDerived_iff i).trans
      (derivedHeadRank_checked i)

theorem complete_original_head_maxima (N : Subgroup Original) [N.Normal] :
    ∃ i : Fin {spec.normal_count}, originalKernel i = N ∧
      primeNormalHeadMax 2 (N ⊓ commutator Original) = derivedHeadRank i := by
  obtain ⟨i, hi⟩ := complete_original N
  change originalKernel i = N at hi
  subst N
  exact ⟨i, rfl, original_derived_head_eq i⟩

end {spec.namespace}
'''


def heads_stage(spec, budget):
    # This stage parses only pinned existing Lean literals. No permutation
    # closure, compressed record, derived search or normal discovery is run.
    inputs = {}
    input_bytes = 0
    for name in ("States.lean", "RadicalProfiles.lean", "Derived.lean"):
        budget.tick()
        payload = registry.read_small(spec.output_directory / name,
                                      HEAD_INPUT_BYTE_CEILING - input_bytes)
        input_bytes += len(payload)
        inputs[name] = payload
    maxima, heads, eligible, derived = selected_head_values(spec, inputs, budget)
    return {"HeadMaxima.lean": emit_heads(spec, maxima)}, {
        "stage": "heads", "source_rows": spec.source_rows,
        "normal_states": spec.normal_count, "original_generators": spec.generator_count,
        "derived_state_index_zero_based": derived,
        "actual_head_ranks": heads, "derived_head_ranks": maxima,
        "eligible_original_state_indices_zero_based": eligible,
        "input_bytes": input_bytes, "stored_profile_fields_used": False,
        "group_search": False, "normal_enumeration": False,
        "axis_maximum_bound": True, "quotient_invariants_bound": False,
    }


# Each stage must be explicitly selected and accepted separately. There is no
# all-stages action; heads additionally requires the accepted Derived digest.
STAGES = {"radicals": radical_stage, "derived": derived_stage,
          "quotients": quotient_stage, "heads": heads_stage}


def verify_prerequisite_paths(paths):
    for path, expected in paths.items():
        if registry.sha256(registry.read_small(path, MAX_OUTPUT_BYTES)) != expected:
            raise registry.Rejected(f"selected prerequisite changed during stage: {path.name}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--master", choices=sorted(ACCEPTED), required=True)
    parser.add_argument("--stage", choices=sorted(STAGES), required=True)
    parser.add_argument("--derived-sha256", help="required only for heads, after root checks Derived")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--max-operations", type=int, default=200000)
    parser.add_argument("--max-seconds", type=float, default=10.0)
    parser.add_argument("--max-output-bytes", type=int, default=1048576)
    parser.add_argument("--private-report", type=Path)
    args = parser.parse_args()
    if args.stage == "heads":
        if args.derived_sha256 is None or re.fullmatch(r"[0-9a-f]{64}", args.derived_sha256) is None:
            parser.error("heads requires --derived-sha256 with the selected checked Derived source SHA256")
    elif args.derived_sha256 is not None:
        parser.error("--derived-sha256 is used only by the heads stage")
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
    spec = registry.SPECS[args.master]
    budget = registry.Budget(args.max_operations, args.max_seconds, args.max_output_bytes)
    prerequisites = checked_prerequisites(spec)
    prerequisites.update(checked_stage_prerequisites(spec, args.stage))
    if args.stage == "heads":
        prerequisites[spec.output_directory / "Derived.lean"] = args.derived_sha256
        verify_prerequisite_paths(prerequisites)
    texts, details = STAGES[args.stage](spec, budget)
    prerequisites.update({Path(path): digest for path, digest in details.pop("required_stage_sources", {}).items()})
    payloads = {name: text.encode("utf-8") for name, text in texts.items()}
    output_bytes = sum(map(len, payloads.values()))
    budget.tick()
    if output_bytes > budget.output_limit:
        raise registry.Rejected("selected output-byte cap exceeded")
    verify_prerequisite_paths(prerequisites)
    outputs = {}
    for name, payload in payloads.items():
        destination = spec.output_directory / name
        if args.check:
            if not destination.exists() or registry.read_small(destination, MAX_OUTPUT_BYTES) != payload:
                raise registry.Rejected(f"selected generated source mismatch: {name}")
        else:
            registry.atomic_write(destination, payload)
        outputs[str(destination.relative_to(ROOT))] = registry.sha256(payload)
    verify_prerequisite_paths(prerequisites)
    budget.tick()
    report = {
        "master": spec.master, **details, "operations": budget.operations,
        "output_bytes": output_bytes, "outputs": outputs,
        "accepted_prerequisites": {str(p.relative_to(ROOT)): h for p, h in prerequisites.items()},
        "record_sha256": spec.record_sha256,
        "producer_sha256": registry.sha256(registry.read_small(Path(__file__).resolve())),
        "enabled_stages": sorted(STAGES), "other_masters_enabled": False,
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
