import SymmetricSubgroupAsymptotics.AffineWreathNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow4WreathTop
import SymmetricSubgroupAsymptotics.PrimePairWreathNormalGenerators
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

/-! All original row4 normal quotients inherit the two-generator bound
through the exact local affine wreath projection. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow4QuotientSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoPairedEightAffineTops
open PrimitiveAffineDegreeTwoTwoAffineSixteenRow4WreathTop

theorem model_normal_generators :
    ∀ N : Subgroup Model, N.Normal →
      ∃ x : Fin 2 → Model, Subgroup.normalClosure (Set.range x) = N := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : IsSimpleGroup R := Row18.linearGroup_isSimpleGroup
  exact AffineModel.wreath_normal_generating_tuples R Row18.irreducible
    firstVector firstVector_ne_zero (by decide)
    (PrimePairWreathNormalGenerators.of_prime_card 7 Row18.linearGroup_card)

theorem top_normal_generators (N : Subgroup Top) (hN : N.Normal) :
    ∃ x : Fin 2 → Top, Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective modelEquiv.toMonoidHom modelEquiv.surjective
    model_normal_generators N hN

theorem topSocle (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples top_normal_generators N.1

noncomputable def family :
    DegreeTwoTwoAffineSixteenInterfaces.row4.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoTwoAffineSixteenInterfaces.row4.normalRegistry topSocle

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow4QuotientSocles
end SymmetricSubgroupAsymptotics

end
