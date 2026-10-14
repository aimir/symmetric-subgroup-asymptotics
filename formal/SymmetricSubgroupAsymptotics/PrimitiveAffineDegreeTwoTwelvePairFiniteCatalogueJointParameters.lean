import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueGlobalFunctions
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueJointParametersRows1To50
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueJointParametersRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueJointParametersRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueJointParametersRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueJointParametersRows201To250
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueJointParametersRows251To301

/-! The six literal joint parameter pairs used by the 301 generated rows. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelvePairFiniteCatalogue

theorem joint_parameters : ∀ j : Fin 301, branch j = .joint →
    (kappa j, sectionCap j) ∈ degreeTwoTwelvePairJointParameters := by
  refine Fin.addCases (m := 50) (n := 251) ?_ ?_
  · intro j h
    have hj : branchRows1To50 j = .joint := by
      simpa [branch] using h
    simpa [kappa, sectionCap] using jointParametersRows1To50 j hj
  · refine Fin.addCases (m := 50) (n := 201) ?_ ?_
    · intro j h
      have hj : branchRows51To100 j = .joint := by
        simpa [branch] using h
      simpa [kappa, sectionCap] using jointParametersRows51To100 j hj
    · refine Fin.addCases (m := 50) (n := 151) ?_ ?_
      · intro j h
        have hj : branchRows101To150 j = .joint := by
          simpa [branch] using h
        simpa [kappa, sectionCap] using jointParametersRows101To150 j hj
      · refine Fin.addCases (m := 50) (n := 101) ?_ ?_
        · intro j h
          have hj : branchRows151To200 j = .joint := by
            simpa [branch] using h
          simpa [kappa, sectionCap] using jointParametersRows151To200 j hj
        · refine Fin.addCases (m := 50) (n := 51) ?_ ?_
          · intro j h
            have hj : branchRows201To250 j = .joint := by
              simpa [branch] using h
            simpa [kappa, sectionCap] using jointParametersRows201To250 j hj
          · intro j h
            have hj : branchRows251To301 j = .joint := by
              simpa [branch] using h
            simpa [kappa, sectionCap] using jointParametersRows251To301 j hj

end DegreeTwoTwelvePairFiniteCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
