import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150

/-! Chunk-local assembly data for count-twelve pair-top catalogue rows
101--150. Keeping these dispatchers behind an imported module prevents the
final catalogue from elaborating a 301-deep chain. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelvePairFiniteCatalogue

/-- Branch metadata for catalogue rows 101--150. -/
def branchRows101To150 : Fin 50 → DegreeTwoTwelvePairTopBranch :=
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .ternary <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .core <|
  Fin.cases .core <|
  Fin.cases .core <|
  Fin.cases .core <|
  Fin.cases .core <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.elim0

/-- Joint-profile first parameter for catalogue rows 101--150. -/
def kappaRows101To150 : Fin 50 → ℕ :=
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 3 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 3 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 3 <|
  Fin.cases 3 <|
  Fin.cases 3 <|
  Fin.cases 3 <|
  Fin.cases 3 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.elim0

/-- Joint-profile section cap for catalogue rows 101--150. -/
def sectionCapRows101To150 : Fin 50 → ℕ :=
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.elim0

/-- Concrete finite interfaces for catalogue rows 101--150. -/
noncomputable def finiteInterfaceRows101To150 : Fin 50 →
    DegreeTwoPairTopFiniteInterface 12 :=
  Fin.cases row101Interface <|
  Fin.cases row102Interface <|
  Fin.cases row103Interface <|
  Fin.cases row104Interface <|
  Fin.cases row105Interface <|
  Fin.cases row106Interface <|
  Fin.cases row107Interface <|
  Fin.cases row108Interface <|
  Fin.cases row109Interface <|
  Fin.cases row110Interface <|
  Fin.cases row111Interface <|
  Fin.cases row112Interface <|
  Fin.cases row113Interface <|
  Fin.cases row114Interface <|
  Fin.cases row115Interface <|
  Fin.cases row116Interface <|
  Fin.cases row117Interface <|
  Fin.cases row118Interface <|
  Fin.cases row119Interface <|
  Fin.cases row120Interface <|
  Fin.cases row121Interface <|
  Fin.cases row122Interface <|
  Fin.cases row123Interface <|
  Fin.cases row124Interface <|
  Fin.cases row125Interface <|
  Fin.cases row126Interface <|
  Fin.cases row127Interface <|
  Fin.cases row128Interface <|
  Fin.cases row129Interface <|
  Fin.cases row130Interface <|
  Fin.cases row131Interface <|
  Fin.cases row132Interface <|
  Fin.cases row133Interface <|
  Fin.cases row134Interface <|
  Fin.cases row135Interface <|
  Fin.cases row136Interface <|
  Fin.cases row137Interface <|
  Fin.cases row138Interface <|
  Fin.cases row139Interface <|
  Fin.cases row140Interface <|
  Fin.cases row141Interface <|
  Fin.cases row142Interface <|
  Fin.cases row143Interface <|
  Fin.cases row144Interface <|
  Fin.cases row145Interface <|
  Fin.cases row146Interface <|
  Fin.cases row147Interface <|
  Fin.cases row148Interface <|
  Fin.cases row149Interface <|
  Fin.cases row150Interface <|
  Fin.elim0

end DegreeTwoTwelvePairFiniteCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
