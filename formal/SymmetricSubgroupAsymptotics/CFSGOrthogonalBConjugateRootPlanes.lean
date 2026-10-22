import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRootPlane
import SymmetricSubgroupAsymptotics.CFSGMatrixConjugateDisplacement

/-! Every original conjugate long root labels the image of the original
positive two-plane under the SAME actual conjugator. The label is the
range of a nonidentity element minus I, not a numerical substitute. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices
variable {K : Type} [Field K]

def conjugateRootPlane (s : ℕ) (g : elementaryRootGroup K (s + 3)) :
    Submodule K (Index (s + 3) → K) :=
  (standardRootPlane (K := K) s).map (Matrix.mulVecLin (g.val : Mat K (s + 3)))

theorem conjugate_highestRoot_displacement_range (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g : elementaryRootGroup K (s + 3)) (a : K) (ha : a ≠ 0) :
    LinearMap.range (Matrix.mulVecLin
      (((g * highestRoot s a * g⁻¹).val : Mat K (s + 3)) - 1)) = conjugateRootPlane s g := by
  change LinearMap.range (Matrix.mulVecLin
    (((g.val * (highestRoot s a).val * g.val⁻¹ : (Mat K (s + 3))ˣ) : Mat K (s + 3)) - 1)) = _
  rw [CFSGMatrixConjugateDisplacement.conjugate_sub_one,
    CFSGMatrixConjugateDisplacement.conjugate_range, highestRoot_displacement_range h2 s a ha]
  rfl

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
