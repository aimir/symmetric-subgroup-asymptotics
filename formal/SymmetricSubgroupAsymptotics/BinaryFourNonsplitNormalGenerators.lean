import SymmetricSubgroupAsymptotics.BinaryFourNonsplitNormalCover
import SymmetricSubgroupAsymptotics.NormalImageKernelGeneratorTransfer
import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles

/-! Two ambient normal generators for both actual nonsplit block
extensions. Inside the translation kernel the restricted odd action gives
the bound. Outside it, the forced kernel cover transfers the bound from
the actual block image, including the extra scalar in the larger source. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourFullBlockCoordinates

open BinaryFourBlockAugmentation

theorem row10_normalGen_le_two (N : Subgroup Row10Model) [N.Normal] :
    MarkedC4.normalGen N ≤ 2 := by
  by_cases hNE : N ≤ row10Projection.ker
  · exact @sourceKernel_normalGen_le_two false N (inferInstance : N.Normal) hNE
  · letI : (N.map row10Projection).Normal :=
      (inferInstance : N.Normal).map row10Projection row10Projection_surjective
    exact normalGen_le_of_kernel_cover_outside row10Projection row10Projection_surjective
      row10Projection.ker le_rfl row10_kernel_cover N hNE
      ((BinaryKleinTernaryNormalChain.normalGen_le_one _).trans (by decide))

theorem row12_normalGen_le_two (N : Subgroup Row12Model) [N.Normal] :
    MarkedC4.normalGen N ≤ 2 := by
  by_cases hNE : N ≤ row12Projection.ker
  · exact @sourceKernel_normalGen_le_two true N (inferInstance : N.Normal) hNE
  · letI : (N.map row12Quotient).Normal :=
      (inferInstance : N.Normal).map row12Quotient row12Quotient_surjective
    apply normalGen_le_of_kernel_cover_outside row12Quotient row12Quotient_surjective
      row12Projection.ker ?_ row12_kernel_cover N hNE
      (BinaryKleinTernaryNormalChain.product_normalGen_le_two _)
    intro g hg
    exact ((row12Quotient_kernel g).mp hg).1

theorem row10_normal_generating_pairs : ∀ N : Subgroup Row10Model, N.Normal →
    ∃ x : Fin 2 → Row10Model, Subgroup.normalClosure (Set.range x) = N := by
  intro N hN
  letI := hN
  exact exists_normal_generating_tuple_of_normalGen_le N (row10_normalGen_le_two N)

theorem row12_normal_generating_pairs : ∀ N : Subgroup Row12Model, N.Normal →
    ∃ x : Fin 2 → Row12Model, Subgroup.normalClosure (Set.range x) = N := by
  intro N hN
  letI := hN
  exact exists_normal_generating_tuple_of_normalGen_le N (row12_normalGen_le_two N)

theorem row10Model_socle_of_surjective {Q : Type} [Group Q]
    (pi : Row10Model →* Q) (hpi : Function.Surjective pi) : SocleNormalGeneratorBound Q 2 :=
  normal_generating_tuples_of_surjective pi hpi row10_normal_generating_pairs
    (finiteGroupSocle Q) inferInstance

theorem row12Model_socle_of_surjective {Q : Type} [Group Q]
    (pi : Row12Model →* Q) (hpi : Function.Surjective pi) : SocleNormalGeneratorBound Q 2 :=
  normal_generating_tuples_of_surjective pi hpi row12_normal_generating_pairs
    (finiteGroupSocle Q) inferInstance

end BinaryFourFullBlockCoordinates
end SymmetricSubgroupAsymptotics

end
