import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4MaximalExtensions

/-! Two opposite actual extension families meet in exactly a singular
three-space containing the original root plane. This is the literal
local incidence used by the D4 triality residue. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexTrialityD2Coordinates
variable (K : Type) [Field K]

theorem extension_inf (L N : Submodule K (Index 2 → K)) :
    extension K (L ⊓ N) = extension K L ⊓ extension K N := by
  ext x
  constructor
  · intro hx
    exact ⟨⟨hx.1, hx.2.1, hx.2.2.1⟩, ⟨hx.1, hx.2.1, hx.2.2.2⟩⟩
  · rintro ⟨hx, hy⟩
    exact ⟨hx.1, hx.2.1, ⟨hx.2.2, hy.2.2⟩⟩

theorem original_column_row_inf_finrank (u v : Fin 2 → K) (hu : u ≠ 0) (hv : v ≠ 0) :
    Module.finrank K ↥(originalColumnPlane K u ⊓ originalRowPlane K v) = 1 := by
  have hh := (determinantCoordinates K).symm.finrank_map_eq (columnPlane K u ⊓ rowPlane K v)
  rw [Submodule.map_inf _ (determinantCoordinates K).symm.injective] at hh
  exact hh.trans (column_inf_row_finrank K u v hu hv)

theorem column_row_maximal_inf_finrank (p q : RulingParameters K) :
    Module.finrank K ↥((columnMaximalExtension K p).val ⊓ (rowMaximalExtension K q).val) = 3 := by
  change Module.finrank K ↥(extension K (originalColumnPlane K p.rep) ⊓
    extension K (originalRowPlane K q.rep)) = 3
  rw [← extension_inf, extension_finrank,
    original_column_row_inf_finrank K p.rep q.rep p.rep_nonzero q.rep_nonzero]

theorem rootPlane_le_column_row_inf (p q : RulingParameters K) :
    rootPlane K ≤ (columnMaximalExtension K p).val ⊓ (rowMaximalExtension K q).val :=
  le_inf (columnMaximalExtension K p).property.2.2 (rowMaximalExtension K q).property.2.2

theorem column_row_inf_singular (p q : RulingParameters K) :
    ∀ x ∈ (columnMaximalExtension K p).val ⊓ (rowMaximalExtension K q).val,
      splitQuadraticForm K 4 x = 0 :=
  fun x hx => (columnMaximalExtension K p).property.2.1 x hx.1

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
