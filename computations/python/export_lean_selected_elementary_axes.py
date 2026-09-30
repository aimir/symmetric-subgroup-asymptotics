#!/usr/bin/env python3
"""Export the three selected elementary index-two axes of the split frontier.

For 8T9, 8T10 and 8T18, complete normal registries reduce an arbitrary
normal index-two exponent-two subgroup to a literal registered state.  The
only additional ambiguity is the second elementary index-two state of 8T9;
that state is transitive, whereas the split residual's retained axis is not.
Lean checks every quotient, power and point-motion assertion below.
"""

from pathlib import Path
import argparse
import gzip
import json
import sys

sys.dont_write_bytecode = True

from export_lean_menu_cayley import compose
from export_lean_normal_registry import action_data
from export_lean_split_top_normal_registry import complete_record


ROOT = Path(__file__).resolve().parents[2]
OUT = (
    ROOT
    / "formal/SymmetricSubgroupAsymptotics/GeneratedSplitTopNormals"
    / "SelectedElementaryAxes.lean"
)
CONFIG = {
    "b8_9": {"selected": 16, "transitive": 17},
    "b8_10": {"selected": 9},
    "b8_18": {"selected": 18},
}


def power_witness(normal, identity):
    return next((i for i, x in enumerate(normal["ns"])
                 if compose(x, x) != identity), None)


def mover_indices(normal):
    return [next(i for i, h in enumerate(normal["ns"]) if h[x] == y)
            for x in range(8) for y in range(8)]


def selected_orbits(normal):
    unseen = set(range(8))
    answer = []
    while unseen:
        x = min(unseen)
        orbit = sorted({h[x] for h in normal["ns"]})
        answer.append(orbit)
        unseen.difference_update(orbit)
    if len(answer) != 2:
        raise ValueError(f"Selected axis does not have two orbits: {answer}")
    return answer


def emit_node(node, record, config):
    label = node["id"][1:].replace("_", "T")
    _, _, source, _, normals = action_data(node, record)
    selected = config["selected"]
    identity = tuple(range(node["degree"]))
    action = f"Subgroup.closure (Set.range BinaryMenuCayley{label}.generators)"
    lines = [
        f"namespace SymmetricSubgroupAsymptotics.BinarySelectedAxis{label}",
        f"local instance : Group BinaryNormal{label}.Source := BinaryMenuCayley{label}.group",
        f"abbrev Action := {action}",
        f"def selectedAxis : Subgroup Action :=",
        f"  (BinaryNormal{label}.states {selected}).kernel.map",
        f"    BinaryMenuCayley{label}.originalEquiv.toMonoidHom",
        "",
    ]

    selected_normal = normals[selected]
    orbits = selected_orbits(selected_normal)
    left, right = orbits
    representatives = {x: orbit[0] for orbit in orbits for x in orbit}
    selected_movers = [
        next(i for i, h in enumerate(selected_normal["ns"])
             if h[representatives[x]] == x)
        for x in range(8)
    ]
    side_entries = ",".join("true" if x in left else "false" for x in range(8))
    mover_entries = ",".join(str(i) for i in selected_movers)
    selected_size = len(selected_normal["ns"])
    lines.extend(
        (
            "def selectedSide (x : Fin 8) : Bool :=",
            f"  (#[{side_entries}] : Array Bool)[x.val]!",
            f"def selectedLeftRepresentative : Fin 8 := {left[0]}",
            f"def selectedRightRepresentative : Fin 8 := {right[0]}",
            "def selectedLeftOrbit : MulAction.orbitRel.Quotient selectedAxis (Fin 8) :=",
            "  Quotient.mk'' selectedLeftRepresentative",
            "def selectedRightOrbit : MulAction.orbitRel.Quotient selectedAxis (Fin 8) :=",
            "  Quotient.mk'' selectedRightRepresentative",
            "",
            f"private def selectedMoverIndex (x : Fin 8) : Fin {selected_size} :=",
            f"  (#[{mover_entries}] : Array (Fin {selected_size}))[x.val]!",
            "private def selectedMoverSource (x : Fin 8) :",
            f"    (BinaryNormal{label}.states {selected}).kernel :=",
            f"  ⟨(⟨BinaryNormal{label}.N{selected}.normalCertificate.rows",
            f"    (selectedMoverIndex x)⟩ : BinaryNormal{label}.Source),",
            f"    BinaryNormal{label}.N{selected}.row_mem (selectedMoverIndex x)⟩",
            "",
            "private def selectedMover (x : Fin 8) : selectedAxis :=",
            f"  ⟨BinaryMenuCayley{label}.originalEquiv (selectedMoverSource x),",
            "    ⟨selectedMoverSource x,(selectedMoverSource x).property,rfl⟩⟩",
            "",
            "private theorem selectedMover_sends (x : Fin 8) :",
            "    (selectedMover x : Equiv.Perm (Fin 8))",
            "      (if selectedSide x=true then selectedLeftRepresentative",
            "        else selectedRightRepresentative)=x := by",
            "  revert x",
            "  decide +kernel",
            "",
            "/-- Every selected-axis element preserves the checked two-block partition. -/",
            "theorem selected_preserves_side (u : selectedAxis) (x : Fin 8) :",
            "    selectedSide ((u : Equiv.Perm (Fin 8)) x)=selectedSide x := by",
            "  obtain ⟨s,hs,he⟩ := u.property",
            f"  obtain ⟨i,hi⟩ := (BinaryNormal{label}.N{selected}.normalCertificate.mem_closure_iff s).mp hs",
            "  have hsi : s=(⟨BinaryNormal" + label + f".N{selected}.normalCertificate.rows i⟩ :",
            f"      BinaryNormal{label}.Source) := by",
            "    apply FiniteGroupRow.ext",
            "    exact hi.symm",
            "  have heperm : (u : Equiv.Perm (Fin 8))=",
            f"      (BinaryMenuCayley{label}.originalEquiv s : Equiv.Perm (Fin 8)) :=",
            "    (congrArg Subtype.val he).symm",
            "  rw [heperm,hsi]",
            "  clear hi hsi heperm he hs u s",
            "  revert x i",
            "  decide +kernel",
            "",
            "/-- The two displayed orbit classes are distinct. -/",
            "theorem selected_orbits_ne : selectedLeftOrbit≠selectedRightOrbit := by",
            "  intro h",
            "  have hr := Quotient.exact h",
            "  change selectedLeftRepresentative∈",
            "    MulAction.orbit selectedAxis selectedRightRepresentative at hr",
            "  obtain ⟨u,hu⟩ := MulAction.mem_orbit_iff.mp hr",
            "  have hp := selected_preserves_side u selectedRightRepresentative",
            "  change (u : Equiv.Perm (Fin 8)) selectedRightRepresentative=",
            "    selectedLeftRepresentative at hu",
            "  rw [hu] at hp",
            "  have hne : selectedSide selectedLeftRepresentative≠",
            "      selectedSide selectedRightRepresentative := by decide +kernel",
            "  exact hne hp",
            "",
            "/-- Literal membership in the displayed left orbit is the checked side flag. -/",
            "theorem mem_selectedLeftOrbit_iff (x : Fin 8) :",
            "    x∈selectedLeftOrbit.orbit ↔ selectedSide x=true := by",
            "  change x∈MulAction.orbit selectedAxis selectedLeftRepresentative ↔ _",
            "  constructor",
            "  · intro hx",
            "    obtain ⟨u,hu⟩ := MulAction.mem_orbit_iff.mp hx",
            "    have hp := selected_preserves_side u selectedLeftRepresentative",
            "    change (u : Equiv.Perm (Fin 8)) selectedLeftRepresentative=x at hu",
            "    rw [hu] at hp",
            "    simpa using hp",
            "  · intro hx",
            "    apply MulAction.mem_orbit_iff.mpr",
            "    refine ⟨selectedMover x,?_⟩",
            "    simpa [hx] using selectedMover_sends x",
            "",
            "/-- Literal membership in the displayed right orbit is the other side flag. -/",
            "theorem mem_selectedRightOrbit_iff (x : Fin 8) :",
            "    x∈selectedRightOrbit.orbit ↔ selectedSide x=false := by",
            "  change x∈MulAction.orbit selectedAxis selectedRightRepresentative ↔ _",
            "  constructor",
            "  · intro hx",
            "    obtain ⟨u,hu⟩ := MulAction.mem_orbit_iff.mp hx",
            "    have hp := selected_preserves_side u selectedRightRepresentative",
            "    change (u : Equiv.Perm (Fin 8)) selectedRightRepresentative=x at hu",
            "    rw [hu] at hp",
            "    simpa using hp",
            "  · intro hx",
            "    apply MulAction.mem_orbit_iff.mpr",
            "    refine ⟨selectedMover x,?_⟩",
            "    have hnot : selectedSide x≠true := by simpa [hx]",
            "    simpa [hnot] using selectedMover_sends x",
            "",
            "/-- The displayed classes exhaust the selected axis orbits. -/",
            "theorem selected_orbits_cover (o :",
            "    MulAction.orbitRel.Quotient selectedAxis (Fin 8)) :",
            "    o=selectedLeftOrbit ∨ o=selectedRightOrbit := by",
            "  induction o using Quotient.inductionOn' with",
            "  | _ x =>",
            "      by_cases hx : selectedSide x=true",
            "      · left",
            "        apply Quotient.sound",
            "        change x∈MulAction.orbit selectedAxis selectedLeftRepresentative",
            "        apply MulAction.mem_orbit_iff.mpr",
            "        refine ⟨selectedMover x,?_⟩",
            "        simpa [hx] using selectedMover_sends x",
            "      · right",
            "        apply Quotient.sound",
            "        change x∈MulAction.orbit selectedAxis selectedRightRepresentative",
            "        apply MulAction.mem_orbit_iff.mpr",
            "        refine ⟨selectedMover x,?_⟩",
            "        simpa [hx] using selectedMover_sends x",
            "",
        )
    )

    transitive = config.get("transitive")
    if transitive is not None:
        normal = normals[transitive]
        movers = mover_indices(normal)
        entries = ",".join(str(x) for x in movers)
        lines.extend(
            (
                "private def moverIndex (x y : Fin 8) : "
                f"Fin {len(normal['ns'])} :=",
                f"  (#[{entries}] : Array (Fin {len(normal['ns'])}))[8*x.val+y.val]!",
                "",
                "private def moverElement (x y : Fin 8) :",
                f"    (BinaryNormal{label}.states {transitive}).kernel :=",
                f"  ⟨(⟨BinaryNormal{label}.N{transitive}.normalCertificate.rows "
                f"(moverIndex x y)⟩ : BinaryNormal{label}.Source),",
                f"    BinaryNormal{label}.N{transitive}.row_mem (moverIndex x y)⟩",
                "",
                "private theorem mover_sends (x y : Fin 8) :",
                f"    (BinaryMenuCayley{label}.originalEquiv (moverElement x y) :",
                "      Equiv.Perm (Fin 8)) x=y := by",
                "  revert x y",
                "  decide +kernel",
                "",
                "/-- The other elementary index-two axis of 8T9 is transitive. -/",
                "private theorem transitive_competitor :",
                "    PermutationSubgroupTransitive",
                f"      (((BinaryNormal{label}.states {transitive}).kernel.map",
                f"        BinaryMenuCayley{label}.originalEquiv.toMonoidHom).map",
                "        Action.subtype) := by",
                "  intro x y",
                f"  let h := BinaryMenuCayley{label}.originalEquiv (moverElement x y)",
                "  refine ⟨(h : Equiv.Perm (Fin 8)),?_,?_⟩",
                "  · exact ⟨h,⟨moverElement x y,(moverElement x y).property,rfl⟩,rfl⟩",
                "  · exact mover_sends x y",
                "",
            )
        )

    lines.extend(
        (
            "/-- The complete literal normal registry leaves exactly the selected",
            "nontransitive elementary index-two axis. -/",
            "theorem complete (N : Subgroup Action) [N.Normal]",
            "    (hindex : N.index=2) (hexponent : ∀ x : N,x^2=1)",
            "    (hnottrans : ¬PermutationSubgroupTransitive (N.map Action.subtype)) :",
            "    N=selectedAxis := by",
            f"  obtain ⟨j,hj⟩ := @BinaryNormalRegistry.complete_map_of_equiv _ _ _ _ _ _ _ _",
            f"    BinaryNormal{label}.registry _ _ BinaryNormal{label}.source_isPGroup",
            f"    BinaryMenuCayley{label}.originalEquiv N inferInstance",
            "  have hquotient : (BinaryNormal" + label + ".states j).quotientCount=2 := by",
            "    rw [← (BinaryNormal" + label + ".states j).index_eq_quotientCount]",
            "    calc",
            "      (BinaryNormal" + label + ".states j).kernel.index =",
            "          ((BinaryNormal" + label + ".states j).kernel.map",
            "            BinaryMenuCayley" + label + ".originalEquiv.toMonoidHom).index :=",
            "        (Subgroup.index_map_equiv (BinaryNormal" + label + ".states j).kernel",
            "          BinaryMenuCayley" + label + ".originalEquiv).symm",
            "      _ = N.index := congrArg Subgroup.index hj",
            "      _ = 2 := hindex",
            "  let en : (BinaryNormal" + label + ".states j).kernel ≃* N :=",
            "    ((BinaryNormal" + label + ".states j).kernel.equivMapOfInjective",
            "      BinaryMenuCayley" + label + ".originalEquiv.toMonoidHom",
            "      BinaryMenuCayley" + label + ".originalEquiv.injective).trans",
            "      (MulEquiv.subgroupCongr hj)",
            "  have hexponentSource : ∀ x : (BinaryNormal" + label + ".states j).kernel,",
            "      x^2=1 := by",
            "    intro x",
            "    have hpull := congrArg en.symm (hexponent (en x))",
            "    simpa only [map_pow,map_one,MulEquiv.symm_apply_apply] using hpull",
            "  fin_cases j",
        )
    )

    for i, normal in enumerate(normals):
        if i == selected:
            lines.append("  · exact hj.symm")
            continue
        if i == transitive:
            lines.extend(
                (
                    "  · exfalso",
                    "    apply hnottrans",
                    "    rw [← hj]",
                    "    exact transitive_competitor",
                )
            )
            continue
        quotient_count = len(normal["reps"])
        if quotient_count != 2:
            lines.extend(
                (
                    "  · exfalso",
                    "    have hne : (BinaryNormal" + label +
                    f".states {i}).quotientCount≠2 := by decide +kernel",
                    "    exact hne hquotient",
                )
            )
            continue
        witness = power_witness(normal, identity)
        if witness is None:
            raise ValueError(f"Unexpected extra elementary row {label}/N{i}")
        lines.extend(
            (
                "  · exfalso",
                f"    let x : (BinaryNormal{label}.states {i}).kernel :=",
                f"      ⟨(⟨BinaryNormal{label}.N{i}.normalCertificate.rows {witness}⟩ :",
                f"        BinaryNormal{label}.Source),BinaryNormal{label}.N{i}.row_mem {witness}⟩",
                "    have hne : (x : BinaryNormal" + label + ".Source)^2≠1 := by decide +kernel",
                "    exact hne (congrArg Subtype.val (hexponentSource x))",
            )
        )
    lines.extend(("", f"end SymmetricSubgroupAsymptotics.BinarySelectedAxis{label}", ""))
    return "\n".join(lines)


def render():
    with gzip.open(ROOT / "certificates/data/binary_menu.jsonl.gz", "rt") as stream:
        metadata = json.loads(next(stream))
        records = {
            row["id"]: row
            for line in stream
            if (row := json.loads(line)).get("kind") == "action"
        }
    nodes = {node["id"]: node for node in metadata["nodes"]}
    records["b8_18"] = complete_record(nodes["b8_18"])
    imports = "\n".join(
        f"import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry{name[1:].replace('_', 'T')}"
        for name in CONFIG
    )
    header = f"""{imports}
import SymmetricSubgroupAsymptotics.BinarySylowCoverage

/-! Selected elementary index-two axes for the degree-sixteen split frontier.
Generated by export_lean_selected_elementary_axes.py. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

"""
    return header + "\n".join(
        emit_node(nodes[name], records[name], config)
        for name, config in CONFIG.items()
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    payload = render().encode()
    if args.check:
        if not OUT.exists() or OUT.read_bytes() != payload:
            raise SystemExit(f"Stale generated file {OUT}")
    else:
        OUT.parent.mkdir(exist_ok=True)
        if not OUT.exists() or OUT.read_bytes() != payload:
            OUT.write_bytes(payload)
    print(OUT.relative_to(ROOT))


if __name__ == "__main__":
    main()
