import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveGraph

/-! An actual invertible block-upper matrix fixes the literal positive
space. No classical-group identification is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveInvariant
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexPositiveGraph
variable (K : Type) [Field K]

theorem positive_fixed_of_lower_left_zero (r : ℕ) (g : (Mat K r)ˣ)
    (hg : ∀ i j : Fin r, (g : Mat K r) (Sum.inr i) (Sum.inl j) = 0) :
    (positiveSpace K r).map (ambientLinearEquiv K r g).toLinearMap = positiveSpace K r := by
  have hle : (positiveSpace K r).map (ambientLinearEquiv K r g).toLinearMap ≤
      positiveSpace K r := by
    rintro x ⟨y, hy, rfl⟩ i
    change ((g : Mat K r) *ᵥ y) (Sum.inr i) = 0
    change (∑ j : Index r, (g : Mat K r) (Sum.inr i) j * y j) = 0
    rw [Fintype.sum_sum_type]
    have hp : (∑ j : Fin r, (g : Mat K r) (Sum.inr i) (Sum.inl j) * y (Sum.inl j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hg i j, zero_mul]
    have hn : (∑ j : Fin r, (g : Mat K r) (Sum.inr i) (Sum.inr j) * y (Sum.inr j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hy j, mul_zero]
    rw [hp, hn, add_zero]
  apply Submodule.eq_of_le_of_finrank_le hle
  simpa only [LinearEquiv.finrank_map_eq] using
    (le_rfl : Module.finrank K (positiveSpace K r) ≤ Module.finrank K (positiveSpace K r))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveInvariant
