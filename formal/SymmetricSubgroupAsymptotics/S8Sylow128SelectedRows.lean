import SymmetricSubgroupAsymptotics.S8Sylow128LeftCosets
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop17CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop8CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop10CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop24CatalogueBinding

/-! Selected literal target rows for the128-subgroup adjunction pilot.
Coverage is not a premise or theorem of this file; later ordinary-word
certificates must establish it for each of the sixteen double-coset roots. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.S8Sylow128SelectedRows

def rows : Fin 5 → Subgroup (Equiv.Perm (Fin 8)) :=
  ![S8Sylow128LeftCosets.H,
    PrimitiveAffineEightTop17CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop8CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop10CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop24CatalogueBinding.catalogueAction]

end SymmetricSubgroupAsymptotics.S8Sylow128SelectedRows

end
