import SymmetricSubgroupAsymptotics.AlternatingFourTernaryActualSubgroupNormalGenerators
import SymmetricSubgroupAsymptotics.AlternatingSignedImageStructure
import SymmetricSubgroupAsymptotics.CubicKernelSingleTopOriginalQuotientSocles

/-! Every original normal quotient of an actual correlated ternary
four-block affine image with A4/S4 block top has whole-socle bound two.
The signed top and literal ternary kernel section are constructed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlternatingFourTernaryActualQuotientSocles
open AlternatingFourTernaryActualSubgroupNormalGenerators
open LinearSemidirectSubgroupKernelChart

variable (K : Subgroup Model)

theorem quotientSocle
    (heven : alternatingGroup (Fin 4)≤
      AlternatingSignedImageNormalGenerators.blockImage (SignedImage K))
    (N : Subgroup K) [N.Normal] : SocleNormalGeneratorBound (K ⧸ N) 2 := by
  let B := SignedImage K
  let pi := LinearSemidirectActualImageKernelChart.top action K
  let A := LinearSemidirectActualImageKernelChart.kernelModule action K
  let E := LinearSemidirectActualImageKernelChart.originalKernelChart action K
  have hpi : Function.Surjective pi := (projection action K).rangeRestrict_surjective
  letI : IsSolvable B := AlternatingSignedImageStructure.isSolvable B
  letI : IsSolvable K := E.isSolvable_of_solvable_base pi A
  have hu : UniformSubrepresentationGeneratorBound A.ρ 1 :=
    (ambient_uniform K heven).of_injective
      (LinearSemidirectActualImageKernelChart.inclusion action K)
      (LinearSemidirectActualImageKernelChart.inclusion_injective action K)
  exact CubicKernelSingleTopOriginalQuotientSocles.quotientSocle pi hpi A E hu 7
    (AlternatingSignedImageStructure.card_dvd_single_cubic B)
    (AlternatingSignedImageNormalGenerators.normal_generating_pairs B heven) N

end SymmetricSubgroupAsymptotics.AlternatingFourTernaryActualQuotientSocles
