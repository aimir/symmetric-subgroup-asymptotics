import SymmetricSubgroupAsymptotics.S8Sylow128LiteralModels
import SymmetricSubgroupAsymptotics.S8Sylow128AdjunctionRoot1
import SymmetricSubgroupAsymptotics.S8Sylow128AdjunctionRoot5
import SymmetricSubgroupAsymptotics.S8Sylow128AdjunctionRoot6

/-! Exact point-conjugacy bindings for the four selected actual H128
overgroup candidates. The nontrivial bindings use bidirectional ordinary
words on the actual root adjunctions, not group-order recognition. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.S8Sylow128CanonicalAnchorBindings

open S8Sylow128LeftCosets FiniteSubgroupAdjunctionCoverage

theorem row_one_conjugated :
    MulAut.conj S8Sylow128AdjunctionRoot5.conjugator •
      S8Sylow128LiteralModels.rows 1 = S8Sylow128SelectedRows.rows 1 := by
  rw [S8Sylow128LiteralModels.rows_eq_adjoin]
  change MulAut.conj S8Sylow128AdjunctionRoot5.conjugator •
    (H ⊔ Subgroup.closure {representatives (S8Sylow128DoubleCosets.roots 5)}) =
      Subgroup.closure (Set.range PrimitiveAffineEightTop17CatalogueBinding.catalogueGenerators)
  exact adjoin_eq_of_words _ _ _ _ S8Sylow128AdjunctionRoot5.certificate

theorem row_two_conjugated :
    MulAut.conj S8Sylow128AdjunctionRoot6.conjugator •
      S8Sylow128LiteralModels.rows 2 = S8Sylow128SelectedRows.rows 3 := by
  rw [S8Sylow128LiteralModels.rows_eq_adjoin]
  change MulAut.conj S8Sylow128AdjunctionRoot6.conjugator •
    (H ⊔ Subgroup.closure {representatives (S8Sylow128DoubleCosets.roots 6)}) =
      Subgroup.closure (Set.range PrimitiveAffineEightTop10CatalogueBinding.catalogueGenerators)
  exact adjoin_eq_of_words _ _ _ _ S8Sylow128AdjunctionRoot6.certificate

theorem row_three_conjugated :
    MulAut.conj S8Sylow128AdjunctionRoot1.conjugator •
      S8Sylow128LiteralModels.rows 3 = S8Sylow128SelectedRows.rows 4 := by
  rw [S8Sylow128LiteralModels.rows_eq_adjoin]
  change MulAut.conj S8Sylow128AdjunctionRoot1.conjugator •
    (H ⊔ Subgroup.closure {representatives (S8Sylow128DoubleCosets.roots 1)}) =
      Subgroup.closure (Set.range PrimitiveAffineEightTop24CatalogueBinding.catalogueGenerators)
  exact adjoin_eq_of_words _ _ _ _ S8Sylow128AdjunctionRoot1.certificate

theorem binding (i : Fin 4) :
    Covered S8Sylow128SelectedRows.rows (S8Sylow128LiteralModels.rows i) := by
  fin_cases i
  · refine ⟨0, 1, ?_⟩
    change MulAut.conj (1 : Ambient) • S8Sylow128LiteralModels.rows 0 =
      S8Sylow128SelectedRows.rows 0
    rw [S8Sylow128LiteralModels.row_zero]
    change MulAut.conj (1 : Ambient) • H = H
    simp only [map_one, one_smul]
  · exact ⟨1, _, row_one_conjugated⟩
  · exact ⟨3, _, row_two_conjugated⟩
  · exact ⟨4, _, row_three_conjugated⟩

end SymmetricSubgroupAsymptotics.S8Sylow128CanonicalAnchorBindings

end
