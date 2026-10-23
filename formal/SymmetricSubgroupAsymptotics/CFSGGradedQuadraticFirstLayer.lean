import SymmetricSubgroupAsymptotics.CFSGGradedQuadraticUnit
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixGroupFirstLayer

/-! A genuine quadratic word in integer height greater than one has
zero first layer in every characteristic. The integer grading is kept
before reduction to the coefficient field. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGGradedQuadraticFirstLayer
open CFSGGradedQuadraticUnit CFSGGradedMatrixLieFirstLayer
open CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixSupport
variable {I L K : Type*} [Fintype I] [DecidableEq I] [AddCommGroup L] [Field K]

theorem firstLayer_eq_zero_of_height_gt_one (weight : I → L) (H : L →+ ℤ)
    (d : L) (u : (Matrix I I K)ˣ) (hu : QuadraticGrade weight d u) (hd : 1 < H d) :
    firstLayer (H ∘ weight) u = 0 := by
  obtain ⟨E, D, he, hE, hD⟩ := hu
  have hEh := support_apply_height weight d H E hE
  have hDh := support_apply_height weight (d + d) H D hD
  apply Matrix.ext
  intro i j
  change firstPart (H ∘ weight) ((u : Matrix I I K) - 1) i j = 0
  rw [firstPart_apply]
  dsimp only [Function.comp_apply]
  by_cases hij : H (weight i) = H (weight j) + 1
  · rw [if_pos hij, he, Matrix.sub_apply, Matrix.add_apply, Matrix.add_apply]
    have hEz : E i j = 0 := by
      apply hEh i j
      dsimp only [Function.comp_apply]
      omega
    have hDz : D i j = 0 := by
      apply hDh i j
      dsimp only [Function.comp_apply]
      rw [map_add]
      omega
    rw [hEz, hDz, add_zero, add_zero, sub_self]
  · rw [if_neg hij]

end SymmetricSubgroupAsymptotics.CFSGGradedQuadraticFirstLayer
