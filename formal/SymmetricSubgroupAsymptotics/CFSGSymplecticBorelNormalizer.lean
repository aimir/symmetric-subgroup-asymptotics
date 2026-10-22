import SymmetricSubgroupAsymptotics.CFSGMatrixFlagUnipotentNormal
import SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotentNormalizer

/-! The actual C-Borel is exactly the actual unipotent normalizer. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices

theorem borel_le_normalizer_unipotent (K : Type) [Field K] (n : ℕ) :
    borel K n ≤ Subgroup.normalizer
      (unipotent K n : Set (elementaryRootGroup K n)) := by
  intro g hg
  apply (CFSGMatrixFlagSubgroups.unipotentUnits (K := K) (flagEquiv n)).le_normalizer_comap
    (elementaryRootGroup K n).subtype
  exact CFSGMatrixFlagSubgroups.borelUnits_le_normalizer_unipotentUnits (flagEquiv n) hg

theorem normalizer_unipotent_eq_borel (K : Type) [Field K] (r : ℕ) (hr : 0 < r) :
    Subgroup.normalizer (unipotent K (r + 1) : Set (elementaryRootGroup K (r + 1))) =
      borel K (r + 1) :=
  le_antisymm (normalizer_unipotent_le_borel K r hr) (borel_le_normalizer_unipotent K (r + 1))

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
