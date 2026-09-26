#!/usr/bin/env python3
"""Emit the selected J=8T27 actual radical/second-radical certificate layer.

The accepted 13-state registry is fixed by source digests. This producer only
closes the displayed generator tuples and searches radical words within the
64 original source rows; it never discovers/enumerates normal subgroups.
Every radical is identified with an already checked literal normal state by
two Lean containments. The second radical uses that same proved map again.
No stored head, a2, m, center or derived profile is a Lean input.

No compiler or legacy table/exporter main is invoked. Bounds are cooperative
operation/time and fixed state/word/output bounds, not hard RSS limits.
--check is read-only. --write atomically replaces only the two new selected
radical files, never the accepted States.lean or Registry.lean sources.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import export_lean_carrier_j_registry as registry


ROOT = registry.ROOT
OUT = registry.OUTPUT_DIRECTORY
STATES_SHA256 = "e5679bf32d0ba049a7296db3cb3b95dc9b09de5c213054b9ec98fb41c5be8468"
REGISTRY_SHA256 = "0dfbe63775394a33409287319029dd73434dda6c8755ec874dc83bbc58ea2223"
REGISTRY_PRODUCER_SHA256 = "3191ec5e0ecb98163b816c20c5e0f9c13dc53d1288547bbefce5ef3390c98dfe"
MAX_WORD_NODES = 64
MAX_WORD_DEPTH = 64
MAX_WORD_NODES_TOTAL = 832
MAX_OUTPUT_BYTES = 2097152
MAX_OPERATIONS = 500000
MAX_SECONDS = 30.0
NAMESPACE = registry.NAMESPACE


def checked_prerequisites():
    paths = {
        OUT / "States.lean": STATES_SHA256,
        OUT / "Registry.lean": REGISTRY_SHA256,
        Path(registry.__file__).resolve(): REGISTRY_PRODUCER_SHA256,
    }
    for path, expected in paths.items():
        if registry.sha256(registry.read_small(path, MAX_OUTPUT_BYTES)) != expected:
            raise registry.Rejected(f"accepted selected prerequisite changed: {path.name}")
    return paths


def selected_data(budget):
    node, record, input_bytes = registry.selected_inputs(budget)
    table = registry.bounded_table_factory(budget)
    generators = [registry.validate_perm(g) for g in node["generators"]]
    source_table = table(generators, 8)
    source = [registry.legacy.unpack(c, 8) for c in source_table["codes"]]
    if len(source) != 64:
        raise registry.Rejected("the selected literal J source is not 64 rows")
    source_set = set(source)
    normals = []
    for normal in record["normals"]:
        ng = [registry.validate_perm(g) for g in normal["normal_generators"]]
        nt = table(ng, 8)
        rows = [registry.legacy.unpack(c, 8) for c in nt["codes"]]
        if not set(rows) <= source_set or len(rows) != normal["order"]:
            raise registry.Rejected("selected normal closure/source mismatch")
        normals.append({"generators": ng, "rows": rows,
                        "index": {g: i for i, g in enumerate(rows)}})
    lookup = {frozenset(n["rows"]): i for i, n in enumerate(normals)}
    if len(lookup) != 13:
        raise registry.Rejected("duplicate selected normal closures")
    return generators, normals, lookup, input_bytes


def radical_search(ambient, normal, lookup, budget):
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
        if len(rows) >= MAX_WORD_NODES or word_depth > MAX_WORD_DEPTH:
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


def header(imports, description, instance_name):
    return "\n".join("import SymmetricSubgroupAsymptotics." + m for m in imports) + f'''

/-! {description}
Generated only by export_lean_carrier_j_radicals.py. All finite equations
are kernel checked; no stored numerical carrier profile is a premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace {NAMESPACE}
local instance {instance_name} : Group Source := BinaryMenuCayley8T27.group

'''


def emit_radicals(normals, searches):
    text = header(["PrimeRelativeRadicalWords", "GeneratedCarrierNormal8T27.States"],
                  "Exact whole-original-group relative radicals of the 13 accepted J states.",
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
            text += (f"private def word{j} : PrimeRelativeRadicalWord (Fin 2) (Fin {ng}) :=\n"
                     f"  {word_expression(node)}\n")
        words = [f'word{search["position"][g]}' for g in target["generators"]]
        words_expr = registry.legacy.lookup(words, "j.val") if rg else "Fin.elim0 j"
        text += f'''
private def radicalWords (j : Fin {rg}) : PrimeRelativeRadicalWord (Fin 2) (Fin {ng}) :=
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
private def mixedRow (j : Fin {ng}) (i : Fin 2) : Fin {target_order} := {mixed_expr}

private theorem power_checked : ∀ j : Fin {ng}, N{i}.normalGenerators j ^ 2 =
    (⟨N{r}.normalCertificate.rows (powerRow j)⟩ : Source) := by
'''
        if ng:
            text += "  intro j\n  fin_cases j <;> decide +kernel\n"
        else:
            text += "  intro j\n  exact Fin.elim0 j\n"
        text += f'''
private theorem mixed_checked : ∀ (j : Fin {ng}) (i : Fin 2),
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
    return text + f"end {NAMESPACE}\n"


def emit_profiles(normals, searches):
    targets = [s["target"] for s in searches]
    ranks = [log2_exact(len(n["rows"])) - log2_exact(len(normals[r]["rows"]))
             for n, r in zip(normals, targets)]
    orders = [log2_exact(len(n["rows"])) for n in normals]
    text = header(["GeneratedCarrierNormal8T27.Registry", "GeneratedCarrierNormal8T27.Radicals",
                   "RelativeAmbientTransport"],
                  "Actual J head, order, and second-radical-head bindings for every original normal.",
                  "radicalProfilesSourceGroup")
    text += f'''def radicalIndex (i : Fin 13) : Fin 13 :=
  {registry.legacy.finfun(targets, 13)}

def headRank (i : Fin 13) : ℕ := {registry.legacy.lookup(ranks)}
def orderLog (i : Fin 13) : ℕ := {registry.legacy.lookup(orders)}

theorem state_radical_eq (i : Fin 13) :
    primeRelativeRadical 2 (states i).kernel = (states (radicalIndex i)).kernel := by
  fin_cases i
'''
    text += "".join(f"  · exact RadicalN{i}.radical_eq\n" for i in range(13))
    text += '''
theorem state_head_eq (i : Fin 13) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (states i).kernel) = headRank i := by
  fin_cases i
'''
    text += "".join(f"  · exact RadicalN{i}.head_eq\n" for i in range(13))
    text += '''
theorem state_card (i : Fin 13) : Nat.card (states i).kernel = 2 ^ orderLog i := by
  fin_cases i
'''
    text += "".join(f"  · exact N{i}.kernel_card\n" for i in range(13))
    text += '''
/-- The second head uses the radical as a normal of the SAME original Source. -/
theorem state_radical_head_eq (i : Fin 13) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2
      (primeRelativeRadical 2 (states i).kernel)) = headRank (radicalIndex i) :=
  (primeRelativeHead_eq_of_subgroup_eq 2 _ _ (state_radical_eq i)).trans
    (state_head_eq (radicalIndex i))

abbrev Original := Subgroup.closure (Set.range BinaryMenuCayley8T27.generators)

def originalKernel (i : Fin 13) : Subgroup Original :=
  (states i).kernel.map BinaryMenuCayley8T27.originalEquiv.toMonoidHom

instance originalKernel_normal (i : Fin 13) : (originalKernel i).Normal :=
  Subgroup.Normal.map inferInstance _ BinaryMenuCayley8T27.originalEquiv.surjective

theorem original_radical_eq (i : Fin 13) :
    primeRelativeRadical 2 (originalKernel i) = originalKernel (radicalIndex i) := by
  letI : ((states i).kernel.map BinaryMenuCayley8T27.originalEquiv.toMonoidHom).Normal :=
    originalKernel_normal i
  exact (primeRelativeRadical_map_equiv 2 BinaryMenuCayley8T27.originalEquiv
    (states i).kernel).symm.trans
      (congrArg (fun K : Subgroup Source =>
        K.map BinaryMenuCayley8T27.originalEquiv.toMonoidHom) (state_radical_eq i))

theorem original_head_eq (i : Fin 13) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (originalKernel i)) = headRank i :=
  (relativeCharacterAmbientCongr 2 BinaryMenuCayley8T27.originalEquiv
    (states i).kernel (originalKernel i) rfl).finrank_eq.trans (state_head_eq i)

theorem original_card (i : Fin 13) : Nat.card (originalKernel i) = 2 ^ orderLog i :=
  (Nat.card_congr (normalAmbientEquiv BinaryMenuCayley8T27.originalEquiv
    (states i).kernel (originalKernel i) rfl).toEquiv).symm.trans (state_card i)

theorem original_radical_head_eq (i : Fin 13) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2
      (primeRelativeRadical 2 (originalKernel i))) = headRank (radicalIndex i) :=
  (primeRelativeHead_eq_of_subgroup_eq 2 _ _ (original_radical_eq i)).trans
    (original_head_eq (radicalIndex i))

private theorem radical_congr (N R : Subgroup Original) [N.Normal] [R.Normal] (h : N = R) :
    primeRelativeRadical 2 N = primeRelativeRadical 2 R := by
  subst R
  rfl

theorem original_second_radical_eq (i : Fin 13) :
    primeRelativeRadical 2 (primeRelativeRadical 2 (originalKernel i)) =
      originalKernel (radicalIndex (radicalIndex i)) :=
  (radical_congr _ _ (original_radical_eq i)).trans (original_radical_eq (radicalIndex i))

/-- Exhaustive binding uses the accepted original-normal registry, not
the stored profile fields. The maximum head m and quotient fields c,g
remain separate obligations. In particular no inequality a2 ≤ m is used. -/
theorem complete_original_radical_profiles (N : Subgroup Original) [N.Normal] :
    ∃ i : Fin 13, originalKernel i = N ∧
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
    return text + f"end {NAMESPACE}\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--master", choices=["8T27"], required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--max-operations", type=int, default=200000)
    parser.add_argument("--max-seconds", type=float, default=10.0)
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
            parser.error("reports must stay under private_audits")
    budget = registry.Budget(args.max_operations, args.max_seconds, args.max_output_bytes)
    prerequisites = checked_prerequisites()
    ambient, normals, lookup, input_bytes = selected_data(budget)
    searches = [radical_search(ambient, n, lookup, budget) for n in normals]
    total_nodes = sum(len(s["nodes"]) for s in searches)
    if total_nodes > MAX_WORD_NODES_TOTAL:
        raise registry.Rejected("selected total word-node cap exceeded")
    texts = {"Radicals.lean": emit_radicals(normals, searches),
             "RadicalProfiles.lean": emit_profiles(normals, searches)}
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
    # Catch mutation of the accepted sources during generation before reporting success.
    checked_prerequisites()
    targets = [s["target"] for s in searches]
    heads = [log2_exact(len(n["rows"])) - log2_exact(len(normals[r]["rows"]))
             for n, r in zip(normals, targets)]
    report = {
        "master": "8T27", "stage": "actual relative radical and second radical only",
        "source_rows": 64, "normal_states": 13, "radical_state_indices_zero_based": targets,
        "computed_head_ranks": heads, "computed_second_head_ranks": [heads[r] for r in targets],
        "word_nodes": total_nodes, "max_word_depth": max(s["depth"] for s in searches),
        "operations": budget.operations, "decompressed_bytes": input_bytes,
        "output_bytes": output_bytes, "outputs": outputs,
        "accepted_prerequisites": {str(p.relative_to(ROOT)): h for p, h in prerequisites.items()},
        "stored_profile_fields_used": False, "axis_maximum_bound": False,
        "quotient_invariants_bound": False, "lean_status": "pending root checks",
        "mode": "check" if args.check else "write",
    }
    if args.private_report is not None:
        registry.atomic_write(report_destination, (json.dumps(report, indent=2) + "\n").encode())
    print(json.dumps(report, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (registry.Rejected, KeyError, TypeError, ValueError) as error:
        raise SystemExit(str(error)) from error
