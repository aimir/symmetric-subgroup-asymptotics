import SymmetricSubgroupAsymptotics.BinaryDiagonalSwapSubdirectNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow12SubdirectTop
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow13QuotientSocles
import SymmetricSubgroupAsymptotics.FiniteNormalChainGenerators

/-! Uniform normal-generator pairs and every original quotient socle for
the literal row12. Both subdirect alternatives are handled structurally. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow12QuotientSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoPairedEightAffineTops
open PrimitiveAffineDegreeTwoTwoAffineSixteenRow12SubdirectTop

theorem local_normal_generators :
    ∀ N : Subgroup Local, N.Normal →
      ∃ x : Fin 1 → Local, Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective Row20.modelEquiv.toMonoidHom
    Row20.modelEquiv.surjective
    (normal_generating_singletons_of_finite_normal_total
      (DiagonalBinaryPermutationProduct.normal_total_of_three_chain Row20.normalChain))

theorem model_normal_generators :
    ∀ N : Subgroup Model, N.Normal →
      ∃ x : Fin 2 → Model, Subgroup.normalClosure (Set.range x) = N :=
  BinaryDiagonalSwapSubdirect.normal_generating_tuples φ modelGroup
    (BinaryDiagonalSwap.affine_irreducible R Row20.irreducible)
    first_surjective diagonal_mem pure_swap_mem local_normal_generators
    PrimitiveAffineDegreeTwoTwoAffineSixteenRow13QuotientSocles.model_normal_generators

theorem top_normal_generators
    (N : Subgroup DegreeTwoTwoAffineSixteenInterfaces.row12.top) (hN : N.Normal) :
    ∃ x : Fin 2 → DegreeTwoTwoAffineSixteenInterfaces.row12.top,
      Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective modelEquiv.toMonoidHom modelEquiv.surjective
    model_normal_generators N hN

theorem topSocle
    (N : {N : Subgroup DegreeTwoTwoAffineSixteenInterfaces.row12.top // N.Normal}) :
    SocleNormalGeneratorBound (DegreeTwoTwoAffineSixteenInterfaces.row12.top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples top_normal_generators N.1

noncomputable def family :
    DegreeTwoTwoAffineSixteenInterfaces.row12.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoTwoAffineSixteenInterfaces.row12.normalRegistry topSocle

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow12QuotientSocles
end SymmetricSubgroupAsymptotics

end
