import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50

/-! Chunk-local assembly data for count-twelve pair-top catalogue rows
1--50. Keeping these dispatchers behind an imported module prevents the
final catalogue from elaborating a 301-deep chain. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelvePairFiniteCatalogue

/-- Branch metadata for catalogue rows 1--50. -/
def branchRows1To50 : Fin 50 → DegreeTwoTwelvePairTopBranch :=
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
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .core <|
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
  Fin.cases .core <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.elim0

/-- Joint-profile first parameter for catalogue rows 1--50. -/
def kappaRows1To50 : Fin 50 → ℕ :=
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 3 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
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
  Fin.cases 1 <|
  Fin.cases 3 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 3 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 3 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.elim0

/-- Joint-profile section cap for catalogue rows 1--50. -/
def sectionCapRows1To50 : Fin 50 → ℕ :=
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 3 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 3 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.elim0

/-- Concrete finite interfaces for catalogue rows 1--50. -/
noncomputable def finiteInterfaceRows1To50 : Fin 50 →
    DegreeTwoPairTopFiniteInterface 12 :=
  Fin.cases row1Interface <|
  Fin.cases row2Interface <|
  Fin.cases row3Interface <|
  Fin.cases row4Interface <|
  Fin.cases row5Interface <|
  Fin.cases row6Interface <|
  Fin.cases row7Interface <|
  Fin.cases row8Interface <|
  Fin.cases row9Interface <|
  Fin.cases row10Interface <|
  Fin.cases row11Interface <|
  Fin.cases row12Interface <|
  Fin.cases row13Interface <|
  Fin.cases row14Interface <|
  Fin.cases row15Interface <|
  Fin.cases row16Interface <|
  Fin.cases row17Interface <|
  Fin.cases row18Interface <|
  Fin.cases row19Interface <|
  Fin.cases row20Interface <|
  Fin.cases row21Interface <|
  Fin.cases row22Interface <|
  Fin.cases row23Interface <|
  Fin.cases row24Interface <|
  Fin.cases row25Interface <|
  Fin.cases row26Interface <|
  Fin.cases row27Interface <|
  Fin.cases row28Interface <|
  Fin.cases row29Interface <|
  Fin.cases row30Interface <|
  Fin.cases row31Interface <|
  Fin.cases row32Interface <|
  Fin.cases row33Interface <|
  Fin.cases row34Interface <|
  Fin.cases row35Interface <|
  Fin.cases row36Interface <|
  Fin.cases row37Interface <|
  Fin.cases row38Interface <|
  Fin.cases row39Interface <|
  Fin.cases row40Interface <|
  Fin.cases row41Interface <|
  Fin.cases row42Interface <|
  Fin.cases row43Interface <|
  Fin.cases row44Interface <|
  Fin.cases row45Interface <|
  Fin.cases row46Interface <|
  Fin.cases row47Interface <|
  Fin.cases row48Interface <|
  Fin.cases row49Interface <|
  Fin.cases row50Interface <|
  Fin.elim0

end DegreeTwoTwelvePairFiniteCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
