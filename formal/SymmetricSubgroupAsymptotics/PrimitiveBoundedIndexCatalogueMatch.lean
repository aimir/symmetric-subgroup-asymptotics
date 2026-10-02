import SymmetricSubgroupAsymptotics.PrimitiveBoundedIndexReceipt
import SymmetricSubgroupAsymptotics.PrimitiveOuterLogProfile

/-!
# Exact bounded primitive row matching

This lightweight layer contains the row/profile correspondence.  It stays
separate from the final pre-E7 exhaustion so the finite receipt can be checked
without loading the full recurrence stack.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Exact correspondence between one literal outer-log profile and one row of
the kernel-checked bounded primitive receipt. -/
structure PrimitiveBoundedIndexCatalogueMatch
    {L : Type} [Group L] {r : ℕ}
    (C : PrimitiveSemisimpleOuterLogProfile L r) where
  row : Fin 116
  degree_eq : (primitiveBoundedIndexRow row).degree = r
  outerOrder_eq : (primitiveBoundedIndexRow row).outerOrder = C.outerOrder

namespace PrimitiveBoundedIndexCatalogueMatch

variable {L : Type} [Group L] {r : ℕ}
  {C : PrimitiveSemisimpleOuterLogProfile L r}
  (M : PrimitiveBoundedIndexCatalogueMatch C)

include M

theorem index_bound : 2 * C.outerOrder ≤ r := by
  let row := PrimitiveBoundedIndexCatalogueMatch.row M
  calc
    2 * C.outerOrder = 2 * (primitiveBoundedIndexRow row).outerOrder := by
      rw [PrimitiveBoundedIndexCatalogueMatch.outerOrder_eq M]
    _ ≤ (primitiveBoundedIndexRow row).degree :=
      primitiveBoundedIndexRow_bound row
    _ = r := PrimitiveBoundedIndexCatalogueMatch.degree_eq M

end PrimitiveBoundedIndexCatalogueMatch

/-- Resolution of the bounded one-factor branch. -/
inductive PrimitiveBoundedIndexCatalogueResolution
    {L : Type} [Group L] {r : ℕ}
    (C : PrimitiveSemisimpleOuterLogProfile L r) : Type where
  | direct (index_bound : 2 * C.outerOrder ≤ r)
  | catalogue (catalogueMatch : PrimitiveBoundedIndexCatalogueMatch C)

namespace PrimitiveBoundedIndexCatalogueResolution

variable {L : Type} [Group L] {r : ℕ}
  {C : PrimitiveSemisimpleOuterLogProfile L r}

theorem index_bound (R : PrimitiveBoundedIndexCatalogueResolution C) :
    2 * C.outerOrder ≤ r := by
  cases R with
  | direct h => exact h
  | catalogue M => exact M.index_bound

end PrimitiveBoundedIndexCatalogueResolution

/-- Natural outer-log data in which every bounded one-factor branch is either
closed directly or matched to an exact finite row. -/
structure PrimitiveSemisimpleCatalogueCertificateData
    (L : Type) [Group L] (r : ℕ) where
  profile : PrimitiveSemisimpleOuterLogProfile L r
  boundedMatch : profile.factorCount = 1 → profile.leastIndex < 30 →
    PrimitiveBoundedIndexCatalogueResolution profile

end SymmetricSubgroupAsymptotics

end
