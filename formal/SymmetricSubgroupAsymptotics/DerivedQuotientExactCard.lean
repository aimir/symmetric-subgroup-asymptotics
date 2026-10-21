import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Index

/-! Exact derived-quotient order with the SAME original denominator.
This pays retained axis intersections rather than a separate worst case. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {G : Type*} [Group G] [Finite G]

theorem quotient_derived_card_mul_intersection (N : Subgroup G) [N.Normal] :
    Nat.card (N ⊓ commutator G : Subgroup G) *
      Nat.card (commutator (G ⧸ N)) = Nat.card (commutator G) := by
  let q := QuotientGroup.mk' N
  have hm : (commutator G).map q = commutator (G ⧸ N) := by
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective N)]
    rfl
  let f := q.subgroupMap (commutator G)
  have hf : Function.Surjective f := q.subgroupMap_surjective (commutator G)
  let e : f.ker ≃ (N ⊓ commutator G : Subgroup G) := {
    toFun x := ⟨x.val.val, ⟨(QuotientGroup.eq_one_iff _).mp
      (congrArg Subtype.val x.property), x.val.property⟩⟩
    invFun x := ⟨⟨x.val, x.property.2⟩, Subtype.ext
      ((QuotientGroup.eq_one_iff _).mpr x.property.1)⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hc := f.ker.card_mul_index
  rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf,
    Nat.card_congr (Subgroup.topEquiv).toEquiv, Nat.card_congr e] at hc
  rw [← hm]
  exact hc

end SymmetricSubgroupAsymptotics
