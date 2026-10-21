import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index

/-! Exact image size charges the intersection with the SAME original
normal denominator. No independent quotient or radical is substituted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {G : Type} [Group G] [Finite G]

theorem normal_quotient_image_card_mul_intersection
    (N C : Subgroup G) [N.Normal] :
    Nat.card (C.map (QuotientGroup.mk' N)) * Nat.card (C ⊓ N : Subgroup G) = Nat.card C := by
  let q := QuotientGroup.mk' N
  let f := q.subgroupMap C
  have hf : Function.Surjective f := q.subgroupMap_surjective C
  let e : f.ker ≃ (C ⊓ N : Subgroup G) := {
    toFun x := ⟨x.val.val, x.val.property,
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val x.property)⟩
    invFun x := ⟨⟨x.val, x.property.1⟩, by
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).mpr x.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have h := f.ker.card_mul_index
  rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf,
    Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_congr e] at h
  simpa only [Nat.mul_comm] using h

theorem normal_quotient_image_card_mul_le_of_shared_subgroup
    (N C B : Subgroup G) [N.Normal] (hBC : B ≤ C) (hBN : B ≤ N) :
    Nat.card (C.map (QuotientGroup.mk' N)) * Nat.card B ≤ Nat.card C := by
  have hle : B ≤ C ⊓ N := le_inf hBC hBN
  have hc := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)
  exact (Nat.mul_le_mul_left _ hc).trans_eq (normal_quotient_image_card_mul_intersection N C)

end SymmetricSubgroupAsymptotics
