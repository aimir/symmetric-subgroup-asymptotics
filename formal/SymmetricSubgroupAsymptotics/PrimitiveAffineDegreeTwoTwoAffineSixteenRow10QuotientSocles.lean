import SymmetricSubgroupAsymptotics.AffineWreathNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow10WreathTop
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow19LinearWreath
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

/-! All original row10 normal quotients inherit the two-generator bound
through the exact local affine wreath projection. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow10QuotientSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoPairedEightAffineTops
open PrimitiveAffineDegreeTwoTwoAffineSixteenRow10WreathTop

theorem model_normal_generators :
    ∀ N : Subgroup Model, N.Normal →
      ∃ x : Fin 2 → Model, Subgroup.normalClosure (Set.range x) = N := by
  exact AffineModel.wreath_normal_generating_tuples R
    PrimitiveAffineDegreeTwoPairedEightRow19AffineTop.irreducible
    firstVector firstVector_ne_zero (by decide)
    PrimitiveAffineDegreeTwoPairedEightRow19LinearWreath.wreath_normal_generating_pairs

theorem top_normal_generators (N : Subgroup Top) (hN : N.Normal) :
    ∃ x : Fin 2 → Top, Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective modelEquiv.toMonoidHom modelEquiv.surjective
    model_normal_generators N hN

theorem topSocle (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples top_normal_generators N.1

noncomputable def family :
    DegreeTwoTwoAffineSixteenInterfaces.row10.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoTwoAffineSixteenInterfaces.row10.normalRegistry topSocle

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow10QuotientSocles
end SymmetricSubgroupAsymptotics

end
