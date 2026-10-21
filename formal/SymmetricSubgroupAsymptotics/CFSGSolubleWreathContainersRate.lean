import SymmetricSubgroupAsymptotics.CFSGSolubleFullContainerCover
import SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainersNumerics

/-! A fixed quantitative rate for the constructed cover by actual
soluble groups. This counts every original orbit label and point relabelling. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainers

theorem cover_card_le_polylog (b : ℕ) :
    (Nat.card (CFSGSolubleFullContainerCover.cover b).Index : ℝ) ≤
      (2 : ℝ) ^ (4096 * (b : ℝ) * (Real.logb 2 ((b : ℝ) + 2)) ^ 4) := by
  calc
    _ ≤ (2 : ℝ) ^ (33 * b * logBudget b : ℕ) := by
      exact_mod_cast CFSGSolubleFullContainerCover.cover_card_le b
    _ = (2 : ℝ) ^ ((33 * b * logBudget b : ℕ) : ℝ) :=
      (Real.rpow_natCast _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (fullContainerBudget_real_le b)

end SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainers
