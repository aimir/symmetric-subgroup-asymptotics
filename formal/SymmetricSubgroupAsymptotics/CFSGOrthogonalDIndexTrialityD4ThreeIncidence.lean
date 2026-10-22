import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ThreeExtensions
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2LineIncidence

/-! Each actual singular three-space above the original D4 root plane
has precisely its displayed two maximal extensions. This is local
incidence on the original quadratic space, not triality recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexTrialityD2Coordinates CFSGOrthogonalDIndexTailCoordinates
variable (K : Type) [Field K]

theorem extension_le_extension_iff (L N : Submodule K (Index 2 → K)) :
    extension K L ≤ extension K N ↔ L ≤ N := by
  constructor
  · intro h z hz
    have hh := h (twiceTail_mem_extension K L z hz)
    simpa only [twiceTail_leftInverse] using hh.2.2
  · intro h x hx
    exact ⟨hx.1, hx.2.1, h hx.2.2⟩

theorem threeExtension_le_column_iff (p q u : RulingParameters K) :
    (threeExtensionRulingEquiv K (p, q)).val ≤ (columnMaximalExtension K u).val ↔ p = u := by
  change extension K ((segreLine K (p, q)).val.map
      (determinantCoordinates K).symm.toLinearMap) ≤
    extension K ((columnPlane K u.rep).map (determinantCoordinates K).symm.toLinearMap) ↔ _
  rw [extension_le_extension_iff,
    Submodule.map_le_map_iff_of_injective (determinantCoordinates K).symm.injective,
    segreLine_le_columnPlane_iff]

theorem threeExtension_le_row_iff (p q v : RulingParameters K) :
    (threeExtensionRulingEquiv K (p, q)).val ≤ (rowMaximalExtension K v).val ↔ q = v := by
  change extension K ((segreLine K (p, q)).val.map
      (determinantCoordinates K).symm.toLinearMap) ≤
    extension K ((rowPlane K v.rep).map (determinantCoordinates K).symm.toLinearMap) ↔ _
  rw [extension_le_extension_iff,
    Submodule.map_le_map_iff_of_injective (determinantCoordinates K).symm.injective,
    segreLine_le_rowPlane_iff]

theorem threeExtension_le_maximal_iff (p q : RulingParameters K) (M : MaximalExtensions K) :
    (threeExtensionRulingEquiv K (p, q)).val ≤ M.val ↔
      M = columnMaximalExtension K p ∨ M = rowMaximalExtension K q := by
  obtain ⟨t, rfl⟩ := (maximalExtensionRulingEquiv K).surjective M
  cases t with
  | inl u =>
    change _ ≤ (columnMaximalExtension K u).val ↔
      columnMaximalExtension K u = columnMaximalExtension K p ∨
        columnMaximalExtension K u = rowMaximalExtension K q
    rw [threeExtension_le_column_iff]
    constructor
    · rintro rfl
      exact Or.inl rfl
    · rintro (h | h)
      · exact ((columnMaximalExtension_injective K) h).symm
      · exact False.elim (columnMaximalExtension_ne_rowMaximalExtension K u q h)
  | inr v =>
    change _ ≤ (rowMaximalExtension K v).val ↔
      rowMaximalExtension K v = columnMaximalExtension K p ∨
        rowMaximalExtension K v = rowMaximalExtension K q
    rw [threeExtension_le_row_iff]
    constructor
    · rintro rfl
      exact Or.inr rfl
    · rintro (h | h)
      · exact False.elim (columnMaximalExtension_ne_rowMaximalExtension K p v h.symm)
      · exact ((rowMaximalExtension_injective K) h).symm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
