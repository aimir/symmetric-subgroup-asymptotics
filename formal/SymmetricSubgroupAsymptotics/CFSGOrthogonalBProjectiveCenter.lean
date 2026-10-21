import SymmetricSubgroupAsymptotics.CFSGOrthogonalBImageRealization
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBElementaryCenter
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticProjectiveCenter

/-! The actual natural B elementary central quotient is centre-free
away from characteristic two. The middle coordinate supplies the proved
zero diagonals for the genuine cubic-unipotent scalar argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices

theorem elementaryProjective_center_eq_bot (K : Type) [Field K] (r : ℕ) (h2 : (2:K)≠0) :
    Subgroup.center (elementaryProjective K (r+1))=⊥ := by
  have hd : ∀neg i,
      CFSGSerreQuadraticMatrix.fieldRoot (realizationData (r+1)) K neg i
        (middle (r+1)) (middle (r+1))=0 ∧
      CFSGSerreQuadraticMatrix.fieldSecond (realizationData (r+1)) K neg i
        (middle (r+1)) (middle (r+1))=0 := by
    intro neg i
    simp only [realizationData_fieldRoot,realizationData_fieldSecond]
    cases neg <;> constructor <;> by_cases hi : i.val+1<r+1 <;>
      simp [rootMatrix,rootSecond,positive,negative,positiveSecond,negativeSecond,
        hi,pos,CFSGOrthogonalBSerreMatrices.neg,middle,Matrix.single]
  exact CFSGSerreQuadraticMatrix.elementaryProjective_center_eq_bot (realizationData (r+1)) K
    (rootTransvection K (r+1)) (rootTransvection_val_data K (r+1))
    (elementaryRootGroup_center_iff_scalar K r h2) (middle (r+1)) hd

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
