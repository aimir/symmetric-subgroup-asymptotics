import SymmetricSubgroupAsymptotics.TraceyRefinedAffineInput

/-!
The refined Tracey input already contains the half-dimension and logarithmic
induced-module bounds. These implications remove redundant assumptions at
the publication boundary; the refined published input remains an assumption.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.TraceyRefinedInducedModuleInput

/-- Pad the common refined tuple to the natural half-dimension bound. -/
theorem affineHalf (hTracey : TraceyRefinedInducedModuleInput) :
    TraceyAffineHalfInducedModuleInput := by
  intro p _ G _ _ Hsub hindex V _ _ _ rho
  obtain ⟨H, hbounds, hgen⟩ := hTracey p G Hsub hindex V rho
  apply uniformSubrepresentationGeneratorBound_mono _ hgen
  apply (Nat.le_div_iff_mul_le Nat.zero_lt_two).2
  have hreal : (H : ℝ) * 2 ≤
      (Module.finrank (ZMod p) V : ℝ) * Hsub.index :=
    (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hbounds.half
  exact_mod_cast hreal

/-- The common refined tuple supplies the older logarithmic existential
bound for every literal subrepresentation of the same induction. -/
theorem affine (hTracey : TraceyRefinedInducedModuleInput) :
    TraceyAffineInducedModuleInput := by
  intro p _ G _ _ Hsub hindex V _ _ _ rho M
  obtain ⟨H, hbounds, hgen⟩ := hTracey p G Hsub hindex V rho
  refine ⟨H, ?_, hgen M⟩
  exact_mod_cast hbounds.logarithmic

end SymmetricSubgroupAsymptotics.TraceyRefinedInducedModuleInput
