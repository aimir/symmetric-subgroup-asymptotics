import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueAssemblyRows1To50
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueAssemblyRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueAssemblyRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueAssemblyRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueAssemblyRows201To250
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueAssemblyRows251To301

/-! Global branch and parameter functions assembled from six checked chunks. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelvePairFiniteCatalogue

def branch : Fin 301 → DegreeTwoTwelvePairTopBranch :=
  Fin.addCases (m := 50) (n := 251) branchRows1To50 <|
    Fin.addCases (m := 50) (n := 201) branchRows51To100 <|
      Fin.addCases (m := 50) (n := 151) branchRows101To150 <|
        Fin.addCases (m := 50) (n := 101) branchRows151To200 <|
          Fin.addCases (m := 50) (n := 51) branchRows201To250
            branchRows251To301

def kappa : Fin 301 → ℕ :=
  Fin.addCases (m := 50) (n := 251) kappaRows1To50 <|
    Fin.addCases (m := 50) (n := 201) kappaRows51To100 <|
      Fin.addCases (m := 50) (n := 151) kappaRows101To150 <|
        Fin.addCases (m := 50) (n := 101) kappaRows151To200 <|
          Fin.addCases (m := 50) (n := 51) kappaRows201To250
            kappaRows251To301

def sectionCap : Fin 301 → ℕ :=
  Fin.addCases (m := 50) (n := 251) sectionCapRows1To50 <|
    Fin.addCases (m := 50) (n := 201) sectionCapRows51To100 <|
      Fin.addCases (m := 50) (n := 151) sectionCapRows101To150 <|
        Fin.addCases (m := 50) (n := 101) sectionCapRows151To200 <|
          Fin.addCases (m := 50) (n := 51) sectionCapRows201To250
            sectionCapRows251To301

end DegreeTwoTwelvePairFiniteCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
