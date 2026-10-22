import SymmetricSubgroupAsymptotics.CFSGGTwoImageRealization
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticAdjointCubic

/-! The actual G2 short-root conjugation of the other simple root is a
cubic adjoint string over Q. Its length-four vanishing is the proved
literal G2 Serre relation, not a uniform adjoint-nilpotence assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoSimpleRootConjugation
open CFSGGTwoSerreMatrices

theorem simple_fourth_lie (negRoot : Bool) :
    ⁅rootMatrix ℚ negRoot 0, ⁅rootMatrix ℚ negRoot 0,
      ⁅rootMatrix ℚ negRoot 0, ⁅rootMatrix ℚ negRoot 0, rootMatrix ℚ negRoot 1⁆⁆⁆⁆ = 0 := by
  cases negRoot
  · have h := positive_serre (0 : Fin 2) (1 : Fin 2)
    exact h
  · have h := negative_serre (0 : Fin 2) (1 : Fin 2)
    exact h

theorem short_conjugate_long (negRoot : Bool) (t : ℚ) :
    (rootTransvection ℚ negRoot 0 t : Mat ℚ) * rootMatrix ℚ negRoot 1 *
      (↑((rootTransvection ℚ negRoot 0 t)⁻¹) : Mat ℚ) =
      rootMatrix ℚ negRoot 1 + t • ⁅rootMatrix ℚ negRoot 0, rootMatrix ℚ negRoot 1⁆ +
        (t ^ 2 / 2) •
          ⁅rootMatrix ℚ negRoot 0, ⁅rootMatrix ℚ negRoot 0, rootMatrix ℚ negRoot 1⁆⁆ +
        (t ^ 3 / 6) •
          ⁅rootMatrix ℚ negRoot 0, ⁅rootMatrix ℚ negRoot 0,
            ⁅rootMatrix ℚ negRoot 0, rootMatrix ℚ negRoot 1⁆⁆⁆ := by
  have hx : ⁅CFSGSerreQuadraticMatrix.fieldRoot realizationData ℚ negRoot 0,
      ⁅CFSGSerreQuadraticMatrix.fieldRoot realizationData ℚ negRoot 0,
        ⁅CFSGSerreQuadraticMatrix.fieldRoot realizationData ℚ negRoot 0,
          ⁅CFSGSerreQuadraticMatrix.fieldRoot realizationData ℚ negRoot 0,
            rootMatrix ℚ negRoot 1⁆⁆⁆⁆ = 0 := by
    simpa only [realizationData_fieldRoot] using simple_fourth_lie negRoot
  have h := CFSGSerreQuadraticMatrix.canonicalRoot_conjugation_of_fourth_lie
    realizationData negRoot 0 (rootMatrix ℚ negRoot 1) hx t
  simpa only [CFSGSerreQuadraticMatrix.canonicalRoot_val,
    CFSGSerreQuadraticMatrix.canonicalRoot_inv_val,
    realizationData_fieldRoot, realizationData_fieldSecond,
    rootTransvection_val, rootTransvection_inv_val] using h

end SymmetricSubgroupAsymptotics.CFSGGTwoSimpleRootConjugation
