import SymmetricSubgroupAsymptotics.MinimalNormalCompositionCharts
import Mathlib.RepresentationTheory.Irreducible

/-!
# Group structure recovered from an irreducible elementary chart

The elementary-chart construction itself does not assume minimal normality:
it only needs a normal elementary abelian subgroup and exact coordinates.
This file proves the converse structural facts used by the degree-three
four-block branch.  Irreducibility of the literal quotient representation
makes the subgroup minimal normal, while faithfulness makes it
self-centralizing.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace ElementaryMinimalNormalChart

variable {G : Type} [Group G]
  {E : Subgroup G} [E.Normal]
  (C : ElementaryMinimalNormalChart E)

/-- The image in additive coordinates of an ambient subgroup lying below
the elementary normal subgroup. -/
noncomputable def invariantSubmodule
    (W : Subgroup G) (_hWE : W ≤ E) : Submodule (ZMod C.p) C.V :=
  AddSubgroup.toZModSubmodule C.p
    (Subgroup.toAddSubgroup'
      ((W.subgroupOf E).map C.equiv.toMonoidHom))

omit [E.Normal] in
@[simp] theorem mem_invariantSubmodule
    (W : Subgroup G) (hWE : W ≤ E) (v : C.V) :
    v ∈ C.invariantSubmodule W hWE ↔
      ((C.equiv.symm (Multiplicative.ofAdd v) : E) : G) ∈ W := by
  change Multiplicative.ofAdd v ∈
    (W.subgroupOf E).map C.equiv.toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]

/-- An ambient-normal subgroup below `E` gives a subrepresentation of the
literal quotient conjugation action. -/
noncomputable def invariantSubrepresentation
    (W : Subgroup G) (hW : W.Normal) (hWE : W ≤ E) :
    Subrepresentation C.quotientRepresentation.ρ where
  toSubmodule := C.invariantSubmodule W hWE
  apply_mem_toSubmodule := by
    intro q v hv
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective E q
    let e : E := C.equiv.symm (Multiplicative.ofAdd v)
    have heW : (e : G) ∈ W := (C.mem_invariantSubmodule W hWE v).mp hv
    have hconj : (MulAut.conjNormal g e : G) ∈ W := hW.conj_mem e heW g
    apply (C.mem_invariantSubmodule W hWE _).mpr
    have hev : (C.equiv e).toAdd = v := by
      simp only [e, C.equiv.apply_symm_apply, toAdd_ofAdd]
    rw [← hev, C.quotientRepresentation_apply]
    simpa only [ofAdd_toAdd, C.equiv.symm_apply_apply] using hconj

/-- Irreducibility of the quotient conjugation module forces `E` to be a
minimal normal subgroup of the ambient group. -/
theorem minimal_of_quotientRepresentation_irreducible
    [Nontrivial C.V]
    (hirreducible : Representation.IsIrreducible
      C.quotientRepresentation.ρ) :
    ∀ W : Subgroup G, W.Normal → W ≤ E → W = ⊥ ∨ W = E := by
  letI : Representation.IsIrreducible C.quotientRepresentation.ρ :=
    hirreducible
  intro W hW hWE
  let S := C.invariantSubrepresentation W hW hWE
  rcases IsSimpleOrder.eq_bot_or_eq_top S with hbot | htop
  · left
    rw [eq_bot_iff]
    intro x hx
    let e : E := ⟨x, hWE hx⟩
    let v : C.V := (C.equiv e).toAdd
    have hv : v ∈ S := by
      apply (C.mem_invariantSubmodule W hWE v).mpr
      simpa only [e, v, ofAdd_toAdd, C.equiv.symm_apply_apply] using hx
    rw [hbot] at hv
    have hv0 : v = 0 := (Submodule.mem_bot (R := ZMod C.p)).mp hv
    have he1 : e = 1 := by
      apply C.equiv.injective
      apply Multiplicative.toAdd.injective
      simp only [v, hv0, map_one, toAdd_one]
    exact congrArg Subtype.val he1
  · right
    apply le_antisymm hWE
    intro x hx
    let e : E := ⟨x, hx⟩
    let v : C.V := (C.equiv e).toAdd
    have hv : v ∈ S := by
      rw [htop]
      exact Submodule.mem_top
    have heW : (e : G) ∈ W :=
      by
        have heW' := (C.mem_invariantSubmodule W hWE v).mp hv
        have hev_e : C.equiv.symm (Multiplicative.ofAdd v) = e := by
          apply C.equiv.injective
          simp only [C.equiv.apply_symm_apply, v, ofAdd_toAdd]
        rw [hev_e] at heW'
        exact heW'
    exact heW

/-- Faithfulness of the quotient conjugation module says exactly that no
element outside `E` centralizes `E`. -/
theorem selfCentralizing_of_quotientRepresentation_injective
    (hinjective : Function.Injective C.quotientRepresentation.ρ)
    (g : G) (hg : ∀ e ∈ E, g * e = e * g) : g ∈ E := by
  have hrep : C.quotientRepresentation.ρ
      (QuotientGroup.mk' E g) = 1 := by
    apply LinearMap.ext
    intro v
    let e : E := C.equiv.symm (Multiplicative.ofAdd v)
    have hcomm : MulAut.conjNormal g e = e := by
      apply Subtype.ext
      have hge := hg e e.2
      calc
        g * (e : G) * g⁻¹ = (e : G) * g * g⁻¹ := by rw [hge]
        _ = e := by rw [mul_inv_cancel_right]
    rw [← show (C.equiv e).toAdd = v by
      simp only [e, C.equiv.apply_symm_apply, toAdd_ofAdd]]
    rw [C.quotientRepresentation_apply, hcomm]
    rfl
  have hq : QuotientGroup.mk' E g = 1 :=
    hinjective (by simpa only [map_one] using hrep)
  exact (QuotientGroup.eq_one_iff g).mp hq

end ElementaryMinimalNormalChart
end SymmetricSubgroupAsymptotics

end
