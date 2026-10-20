import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! A point-stabilizer maximality lemma for a subgroup of a transitive
normal group that is normalized by the point stabilizer. This is the
product-projection step in the classification-free degree-form argument. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers

/-- Between the intersection with a maximal subgroup and the whole E,
there is no proper intermediate subgroup normalized by that maximal group. -/
theorem maximal_normalizer_interval {G : Type} [Group G]
    (P E C : Subgroup G) (hP : IsCoatom P)
    (hCE : C≤E) (hcap : E⊓P≤C) (hnorm : P≤Subgroup.normalizer C) :
    C=E⊓P ∨ C=E := by
  by_cases heq : C⊔P=P
  · left
    apply le_antisymm _ hcap
    exact le_inf hCE (le_sup_left.trans heq.le)
  · right
    have htop : C⊔P=⊤ := hP.2 _ (lt_of_le_of_ne le_sup_right (Ne.symm heq))
    apply le_antisymm hCE
    intro e he
    have hm : e∈(C : Set G)*(P : Set G) := by
      rw [←Subgroup.coe_mul_of_right_le_normalizer_left C P hnorm,htop]
      trivial
    obtain ⟨c,hc,p,hp,hcp⟩ := hm
    change c*p=e at hcp
    have hpE : p∈E := by
      have h := E.mul_mem (E.inv_mem (hCE hc)) he
      simpa only [←hcp,inv_mul_cancel_left] using h
    have h := C.mul_mem hc (hcap ⟨hpE,hp⟩)
    simpa only [hcp] using h

/-- The same result attached to the actual stabilizer of an original
primitive action. No replacement maximal subgroup is chosen. -/
theorem primitive_stabilizer_interval {G X : Type} [Group G] [MulAction G X]
    [Nontrivial X] [MulAction.IsPreprimitive G X]
    (x : X) (E C : Subgroup G) (hCE : C≤E)
    (hcap : E⊓MulAction.stabilizer G x≤C)
    (hnorm : MulAction.stabilizer G x≤Subgroup.normalizer C) :
    C=E⊓MulAction.stabilizer G x ∨ C=E :=
  maximal_normalizer_interval _ E C
    (MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := G) x) hCE hcap hnorm

end SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers
