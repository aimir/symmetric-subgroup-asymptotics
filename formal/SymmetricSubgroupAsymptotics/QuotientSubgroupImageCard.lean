import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index

/-! Exact cardinality of an actual subgroup image through the SAME
original normal quotient, retaining its literal intersection denominator. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {G : Type*} [Group G] [Finite G]

theorem quotient_subgroup_image_card_mul_intersection
    (N C : Subgroup G) [N.Normal] :
    Nat.card (N ⊓ C : Subgroup G) * Nat.card (C.map (QuotientGroup.mk' N)) =
      Nat.card C := by
  let q := QuotientGroup.mk' N
  let f := q.subgroupMap C
  have hf : Function.Surjective f := q.subgroupMap_surjective C
  let e : f.ker ≃ (N ⊓ C : Subgroup G) := {
    toFun x := ⟨x.val.val,⟨(QuotientGroup.eq_one_iff _).mp
      (congrArg Subtype.val x.property),x.val.property⟩⟩
    invFun x := ⟨⟨x.val,x.property.2⟩,Subtype.ext
      ((QuotientGroup.eq_one_iff _).mpr x.property.1)⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hc := f.ker.card_mul_index
  rw [Subgroup.index_ker,f.range_eq_top_of_surjective hf,
    Nat.card_congr Subgroup.topEquiv.toEquiv,Nat.card_congr e] at hc
  exact hc
end SymmetricSubgroupAsymptotics
