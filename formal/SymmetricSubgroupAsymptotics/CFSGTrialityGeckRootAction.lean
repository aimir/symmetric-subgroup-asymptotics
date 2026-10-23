import SymmetricSubgroupAsymptotics.CFSGTrialityGeckDiagramCovariance
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckImageFourthCoefficient
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalRoots

/-! The actual original D4 root action on the SAME integral Geck image.
The fourth coefficient vanishes by the proved norm-two image form and
source-Cartan transport; no source injectivity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootAction
open CFSG.Models.Chevalley CFSGNormTwoRootPairing CFSGNormTwoGeckHeightData
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGSerreQuadraticMatrix CFSGSerreModelRootGeneration
local instance : DecidableEq (Roots (CartanMatrix.D 4)) := Classical.decEq _

theorem simple_sign (i : Base.support) : rootSign (CartanMatrix.D 4) i = -1 :=
  rootSign_simple (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) i

theorem data_fourth (K : Type) [CommRing K] (neg : Bool) (i : Fin 4)
    (x : K ⊗[ℤ] integralLattice (CartanMatrix.D 4)) :
    fieldSecond data K neg i * baseChange data K x * fieldSecond data K neg i = 0 :=
  transportSource_fourth CFSGTrialityD4NormTwo.cartan_eq rawData K
    (CFSGNormTwoGeckImageFourthCoefficient.baseChange_image_fourth_coefficient_zero
      (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite
      Base Index simple_sign K) neg i x

theorem original_root_action (K : Type) [Field K] (neg : Bool) (i : Fin 4) (t : K)
    (y : (baseChange data K).range) :
    (imageRepresentation data K (modelRoot (CartanMatrix.D 4) K neg i t) y).val =
      (canonicalRoot data K neg i t : Matrix GeckIndex GeckIndex K) * y.val *
        (↑((canonicalRoot data K neg i t)⁻¹) : Matrix GeckIndex GeckIndex K) := by
  rw [imageRepresentation_root data K (data_fourth K), canonicalRoot_val,
    canonicalRoot_inv_val]

theorem action_ranges (K : Type) [Field K] :
    (imageRepresentation data K).range = (canonicalImageAction data K (data_fourth K)).range :=
  canonical_action_ranges_eq data K (data_fourth K)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootAction
