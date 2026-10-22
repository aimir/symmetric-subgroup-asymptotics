import SymmetricSubgroupAsymptotics.CFSGOrthogonalDCenterCardinality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexCharTwo
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProjectiveSimilitudes

/-! Actual characteristic-two sharpening needed for D4 triality
bookkeeping. The SAME elementary centre is trivial, E equals the genuine
even component, and the natural similitude point image has order at most
TWO times the SAME projective elementary group. No automorphism lifting,
triality action, or permutation-degree hypothesis is added. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDCharTwoQuantitative
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexCenterCard
open CFSGOrthogonalDCenterCardinality CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIsometryIndexCharTwo CFSGOrthogonalDProjectiveSimilitudes
variable (K : Type) [Field K] [CharP K 2]

theorem center_eq_bot (s : ℕ) : Subgroup.center (elementaryRootGroup K (s + 4)) = ⊥ := by
  have he (u : Subgroup.center (elementaryRootGroup K (s + 4))) : centerEntry K s u = 1 := by
    rcases centerEntry_eq_one_or_neg_one K s u with h | h
    · exact h
    · exact h.trans (CharTwo.neg_eq (1 : K))
  apply bot_unique
  intro g hg
  have hh : (⟨g, hg⟩ : Subgroup.center (elementaryRootGroup K (s + 4))) = 1 :=
    centerEntry_injective K s ((he ⟨g, hg⟩).trans (he 1).symm)
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hh)

variable [Finite K]

theorem elementary_card_eq_projective (s : ℕ) :
    Nat.card (elementaryRootGroup K (s + 4)) = Nat.card (elementaryProjective K (s + 4)) := by
  have h := (Subgroup.center (elementaryRootGroup K (s + 4))).card_mul_index
  change Nat.card (Subgroup.center (elementaryRootGroup K (s + 4))) *
    Nat.card (elementaryProjective K (s + 4)) = Nat.card (elementaryRootGroup K (s + 4)) at h
  rw [center_eq_bot K s, Subgroup.card_bot, one_mul] at h
  exact h.symm

theorem quadratic_card_le_two_mul_projective (s : ℕ) :
    Nat.card (quadraticPreserving K (s + 4)) ≤ 2 * Nat.card (elementaryProjective K (s + 4)) := by
  let H := (elementaryRootGroup K (s + 4)).subgroupOf (quadraticPreserving K (s + 4))
  have hH : Nat.card H = Nat.card (elementaryRootGroup K (s + 4)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (elementary_le_quadraticPreserving K s)).toEquiv
  calc
    Nat.card (quadraticPreserving K (s + 4)) = Nat.card H * H.index := H.card_mul_index.symm
    _ ≤ Nat.card H * 2 := Nat.mul_le_mul_left _ (elementary_quadratic_isometry_index_le_two K s)
    _ = _ := by rw [hH, elementary_card_eq_projective, Nat.mul_comm]

theorem pointImage_card_le_two_mul_projective (s : ℕ) :
    Nat.card (pointHom K (s + 4)).range ≤ 2 * Nat.card (elementaryProjective K (s + 4)) :=
  (pointImage_card_le_quadratic K (s + 4) (by omega)).trans
    (quadratic_card_le_two_mul_projective K s)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDCharTwoQuantitative
