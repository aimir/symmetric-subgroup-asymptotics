import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! Chunk-local assembly data for count-twelve pair-top catalogue rows
201--250. Keeping these dispatchers behind an imported module prevents the
final catalogue from elaborating a 301-deep chain. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelvePairFiniteCatalogue

/-- Branch metadata for catalogue rows 201--250. -/
def branchRows201To250 : Fin 50 → DegreeTwoTwelvePairTopBranch :=
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
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .joint <|
  Fin.cases .paired <|
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
  Fin.elim0

/-- Joint-profile first parameter for catalogue rows 201--250. -/
def kappaRows201To250 : Fin 50 → ℕ :=
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 3 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 3 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 3 <|
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
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 3 <|
  Fin.cases 3 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 3 <|
  Fin.cases 2 <|
  Fin.cases 4 <|
  Fin.cases 3 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 3 <|
  Fin.cases 2 <|
  Fin.cases 3 <|
  Fin.elim0

/-- Joint-profile section cap for catalogue rows 201--250. -/
def sectionCapRows201To250 : Fin 50 → ℕ :=
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
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
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
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
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 2 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.cases 1 <|
  Fin.elim0

/-- Concrete finite interfaces for catalogue rows 201--250. -/
noncomputable def finiteInterfaceRows201To250 : Fin 50 →
    DegreeTwoPairTopFiniteInterface 12 :=
  Fin.cases row201Interface <|
  Fin.cases row202Interface <|
  Fin.cases row203Interface <|
  Fin.cases row204Interface <|
  Fin.cases row205Interface <|
  Fin.cases row206Interface <|
  Fin.cases row207Interface <|
  Fin.cases row208Interface <|
  Fin.cases row209Interface <|
  Fin.cases row210Interface <|
  Fin.cases row211Interface <|
  Fin.cases row212Interface <|
  Fin.cases row213Interface <|
  Fin.cases row214Interface <|
  Fin.cases row215Interface <|
  Fin.cases row216Interface <|
  Fin.cases row217Interface <|
  Fin.cases row218Interface <|
  Fin.cases row219Interface <|
  Fin.cases row220Interface <|
  Fin.cases row221Interface <|
  Fin.cases row222Interface <|
  Fin.cases row223Interface <|
  Fin.cases row224Interface <|
  Fin.cases row225Interface <|
  Fin.cases row226Interface <|
  Fin.cases row227Interface <|
  Fin.cases row228Interface <|
  Fin.cases row229Interface <|
  Fin.cases row230Interface <|
  Fin.cases row231Interface <|
  Fin.cases row232Interface <|
  Fin.cases row233Interface <|
  Fin.cases row234Interface <|
  Fin.cases row235Interface <|
  Fin.cases row236Interface <|
  Fin.cases row237Interface <|
  Fin.cases row238Interface <|
  Fin.cases row239Interface <|
  Fin.cases row240Interface <|
  Fin.cases row241Interface <|
  Fin.cases row242Interface <|
  Fin.cases row243Interface <|
  Fin.cases row244Interface <|
  Fin.cases row245Interface <|
  Fin.cases row246Interface <|
  Fin.cases row247Interface <|
  Fin.cases row248Interface <|
  Fin.cases row249Interface <|
  Fin.cases row250Interface <|
  Fin.elim0

end DegreeTwoTwelvePairFiniteCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
