import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexParabolicFactor
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexLastDiagonal

/-! The actual Q-positive parabolic has a one-sided determinant coset
factorization. The elementary factor contains the SAME shear and actual
SL lift. No normality of the elementary subgroup is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexParabolicCoset
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIsometryIndexGeneralLinearLift
open CFSGOrthogonalDIsometryIndexLastSquares CFSGOrthogonalDIsometryIndexParabolicFactor
variable (K : Type) [Field K]

theorem parabolic_one_sided_factor (s : ℕ) (g : quadraticPreserving K (s + 4))
    (hP : (positiveSpace K (s + 4)).map (Matrix.mulVecLin (g.val : Mat K (s + 4))) =
      positiveSpace K (s + 4)) :
    ∃ a : Kˣ, ∃ e : elementaryRootGroup K (s + 4),
      g.val = lastDiagonalHom K (s + 3) a * e.val := by
  obtain ⟨A, e₁, he₁⟩ := parabolic_factor K s g hP
  obtain ⟨e₂, he₂⟩ := generalLinearLift_factor K (s + 3) A
  refine ⟨Matrix.GeneralLinearGroup.det A, e₂ * e₁, ?_⟩
  rw [he₁, he₂, ← lastDiagonalHom_eq_lift]
  change (lastDiagonalHom K (s + 3) (Matrix.GeneralLinearGroup.det A) * e₂.val) * e₁.val =
    lastDiagonalHom K (s + 3) (Matrix.GeneralLinearGroup.det A) * (e₂.val * e₁.val)
  exact mul_assoc _ _ _

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexParabolicCoset
