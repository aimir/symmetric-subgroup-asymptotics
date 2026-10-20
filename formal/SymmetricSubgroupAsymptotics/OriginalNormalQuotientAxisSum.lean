import SymmetricSubgroupAsymptotics.OriginalNormalQuotientAxisInjection
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Above-center original axes are charged exactly once inside the normal
menu of the actual quotient. The inequality is only an injective menu
transport of equal literal epimorphism cardinalities. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.OriginalNormalQuotientAxisInjection
variable {G J : Type} [Group G] [Group J] [Finite G]
  (Z : Subgroup G) [Z.Normal]

/-- No multiplicative normal-menu factor is paid for quotient transport. -/
theorem above_epi_sum_le :
    (∑ N : Above Z,(Nat.card (GroupEpimorphism J (G ⧸ N.val.val)) : ℝ))≤
    ∑ M : {M : Subgroup (G ⧸ Z) // M.Normal},
      (Nat.card (GroupEpimorphism J ((G ⧸ Z) ⧸ M.val)) : ℝ) := by
  have he :
      (∑ N : Above Z,(Nat.card (GroupEpimorphism J (G ⧸ N.val.val)) : ℝ))=
      ∑ M ∈ Finset.univ.image (axis Z),
        (Nat.card (GroupEpimorphism J ((G ⧸ Z) ⧸ M.val)) : ℝ) := by
    rw [Finset.sum_image (fun a _ b _ h => axis_injective Z h)]
    apply Finset.sum_congr rfl
    intro N _
    exact_mod_cast epi_card Z (J := J) N
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro M _ _
  exact Nat.cast_nonneg _

end SymmetricSubgroupAsymptotics.OriginalNormalQuotientAxisInjection
