import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRows8And9SingerTops
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

/-! Every normal quotient of the exact retained row8 and row9 tops has
socle normal-generator bound two. The original normal registries remain
the owners of the quotient family. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRows8And9QuotientSocles

open PrimitiveAffineDegreeTwoTwoAffineSixteenRows8And9SingerTops

theorem top_normal_generators (twisted : Bool)
    (N : Subgroup (Top twisted)) (hN : N.Normal) :
    ∃ x : Fin 2 → Top twisted, Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective (modelEquiv twisted).toMonoidHom
    (modelEquiv twisted).surjective (model_normal_generators twisted) N hN

theorem topSocle (twisted : Bool)
    (N : {N : Subgroup (Top twisted) // N.Normal}) :
    SocleNormalGeneratorBound (Top twisted ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (top_normal_generators twisted) N.1

noncomputable def family (twisted : Bool) :
    (row twisted).normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    (row twisted).normalRegistry (topSocle twisted)

end PrimitiveAffineDegreeTwoTwoAffineSixteenRows8And9QuotientSocles
end SymmetricSubgroupAsymptotics

end
