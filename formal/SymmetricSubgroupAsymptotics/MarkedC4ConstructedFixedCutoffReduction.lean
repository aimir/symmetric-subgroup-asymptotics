import SymmetricSubgroupAsymptotics.MarkedC4BoundedOrdinaryRelativeNumerics
import SymmetricSubgroupAsymptotics.MarkedC4BoundedNilpotentTargetConvolution

/-! The complete constructed fixed-cutoff encoding chain. The relative
step and the nilpotent product step use definitionally the SAME bounded
nilpotent family. Actual physical degrees and the same orbit cutoff remain
in the target. The sharp binary-word bound is not an input to construction
of this reduction, and is not asserted here. -/
set_option autoImplicit false
noncomputable section
open Filter
namespace SymmetricSubgroupAsymptotics.MarkedC4.ConstructedFixedCutoffReduction
open OrdinaryNilpotentGeneration

def reduction
    (hsub : PublishedSolubleSubdirectHeight) (hseven : PublishedTheoremSeven)
    (hKP : KovacsPraegerAbelianizationBound) {C : ℕ} (hC : 1 < C) :
    PublishedFixedCutoffReduction (OrbitCutoffFamilies.solubleCount C)
      (BoundedNilpotentProductReduction.targetCount C) where
  middleCount := OrbitCutoffFamilies.nilpotentCount C
  relative := BoundedOrdinaryRelativeRow.reduction hsub hseven hKP C
  product := BoundedNilpotentProductReduction.reduction hC

/-- Literal target convolution, with the odd configurations charged at
their actual physical degrees. No group or orbit cutoff is forgotten. -/
theorem count_le_convolution
    (hsub : PublishedSolubleSubdirectHeight) (hseven : PublishedTheoremSeven)
    (hKP : KovacsPraegerAbelianizationBound) {C : ℕ} (hC : 1 < C) (b r : ℕ) :
    OrbitCutoffFamilies.solubleCount C b r ≤
      (2 : ℝ)^((reduction hsub hseven hKP hC).toMarkedMomentReduction.error b r) *
        PhysicalOddConvolution.count (BoundedNilpotentTargetConvolution.binaryMoment C)
          NilpotentTargetConvolution.oddCount b r := by
  apply ((reduction hsub hseven hKP hC).toMarkedMomentReduction.bound b r).trans
  exact mul_le_mul_of_nonneg_left
    (BoundedNilpotentTargetConvolution.target_le_convolution C b r) (by positivity)

/-- The numerical reduction error is uniform for every bounded r/b window. -/
theorem error_negligible
    (hsub : PublishedSolubleSubdirectHeight) (hseven : PublishedTheoremSeven)
    (hKP : KovacsPraegerAbelianizationBound) {C : ℕ} (hC : 1 < C) :
    UniformQuadraticNegligible
      (reduction hsub hseven hKP hC).toMarkedMomentReduction.error :=
  (reduction hsub hseven hKP hC).toMarkedMomentReduction.negligible

end SymmetricSubgroupAsymptotics.MarkedC4.ConstructedFixedCutoffReduction
end
