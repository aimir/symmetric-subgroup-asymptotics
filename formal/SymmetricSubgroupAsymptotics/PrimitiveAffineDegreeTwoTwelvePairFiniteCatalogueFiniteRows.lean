import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueGlobalFunctions

/-! Final finite interfaces and row records assembled from checked chunks. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelvePairFiniteCatalogue

noncomputable def finiteInterface : Fin 301 → DegreeTwoPairTopFiniteInterface 12 :=
  Fin.addCases (m := 50) (n := 251) finiteInterfaceRows1To50 <|
    Fin.addCases (m := 50) (n := 201) finiteInterfaceRows51To100 <|
      Fin.addCases (m := 50) (n := 151) finiteInterfaceRows101To150 <|
        Fin.addCases (m := 50) (n := 101) finiteInterfaceRows151To200 <|
          Fin.addCases (m := 50) (n := 51) finiteInterfaceRows201To250
            finiteInterfaceRows251To301

noncomputable def row (j : Fin 301) : DegreeTwoTwelvePairTopRow where
  finite := finiteInterface j
  branch := branch j
  kappa := kappa j
  sectionCap := sectionCap j
  expectedProfiles :=
    match branch j with
    | .joint => degreeTwoTwelvePairJointProfiles (kappa j) (sectionCap j)
    | .core => degreeTwoTwelvePairExceptionalProfiles
    | .ternary => ∅
    | .paired => degreeTwoTwelvePairExceptionalProfiles
  expectedProfiles_eq := rfl

end DegreeTwoTwelvePairFiniteCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
