import SymmetricSubgroupAsymptotics.MarkerForwardRow

/-! The complete numerical marker kernel as a single forward row indexed
by the original degree. This is the row estimate used by the ordinary
recurrence interface; the physical comparison is a separate theorem. -/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.MarkerDegreeForwardRow

local instance fibreFinite (N epsilon D : ℕ) :
    Finite (MarkerGeometry.DefectFibre N epsilon D) :=
  Finite.of_injective MarkerGeometry.profileCode MarkerGeometry.profileCode_injective

def kernel (n m : ℕ) : ℝ := MarkerForwardRow.kernel (halfDegree n) (parity n) m

theorem degree_identity (n : ℕ) : 2 * halfDegree n + parity n = n := by
  unfold halfDegree parity
  omega

theorem kernel_nonneg (n m : ℕ) : 0 ≤ kernel n m :=
  MarkerForwardRow.kernel_nonneg _ _ _

theorem kernel_eq_zero_of_le (n m : ℕ) (h : n ≤ m) : kernel n m = 0 := by
  apply MarkerForwardRow.kernel_eq_zero_of_source_le
  simpa only [degree_identity] using h

theorem row_sum_eq (n : ℕ) :
    (∑ m ∈ Finset.range n, kernel n m) =
      MarkerNormalizedRow.positiveDefectRow (halfDegree n) (parity n) := by
  simpa only [degree_identity, kernel] using
    MarkerForwardRow.row_sum_eq (halfDegree n) (parity n)

theorem weighted_sum_eq (n : ℕ) (a : ℕ → ℝ) :
    (∑ m ∈ Finset.range n, kernel n m * a m) =
      ∑ D ∈ Finset.Icc 1 (halfDegree n),
        ∑ s : MarkerGeometry.DefectFibre (halfDegree n) (parity n) D,
          MarkerNormalizedKernel.profileKernel s.val * a (2 * s.val.M) := by
  simpa only [degree_identity, kernel] using
    MarkerForwardRow.weighted_sum_eq (halfDegree n) (parity n) a

/-- One exponential row estimate in the original degree, at both parities.
No boundedness of the later ordinary target counts is assumed. -/
theorem eventually_row_le :
    ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.range n, kernel n m) ≤
        (2 : ℝ) ^ (1 / 20 : ℝ) * (2 : ℝ) ^ (-(n : ℝ) / 20) := by
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp MarkerForwardRow.eventually_both_parities
  filter_upwards [eventually_ge_atTop (2 * N0)] with n hn
  have hhalf : N0 ≤ halfDegree n := by unfold halfDegree; omega
  have hparity : parity n ≤ 1 := by unfold parity; omega
  have hrow := hN0 (halfDegree n) hhalf (parity n) hparity
  have hreal : (n : ℝ) ≤ 2 * (halfDegree n : ℝ) + 1 := by
    have hnat := degree_identity n
    exact_mod_cast (show n ≤ 2 * halfDegree n + 1 by omega)
  calc
    _ ≤ (2 : ℝ) ^ (-(halfDegree n : ℝ) / 10) := by
      simpa only [degree_identity, kernel] using hrow
    _ ≤ _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith

end SymmetricSubgroupAsymptotics.MarkerDegreeForwardRow
