import SymmetricSubgroupAsymptotics.MarkerNormalizedRow

/-! Regrouping the complete positive-defect numerical marker row by its
actual lower target degree. Every state is counted once. No bound on the
target sequence, and no physical counting comparison, is assumed here. -/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.MarkerForwardRow

open MarkerGeometry MarkerNormalizedKernel MarkerNormalizedRow

local instance fibreFinite (N epsilon D : ℕ) : Finite (DefectFibre N epsilon D) :=
  Finite.of_injective profileCode profileCode_injective

theorem target_lt_source {N epsilon D : ℕ} (s : DefectFibre N epsilon D)
    (hD : 1 ≤ D) : 2 * s.val.M < 2 * N + epsilon := by
  have hdegree := s.val.degree_balance
  have hd := s.property
  omega

/-- Sum of the literal state weights having the given target degree. -/
def kernel (N epsilon m : ℕ) : ℝ :=
  ∑ D ∈ Finset.Icc 1 N, ∑ s : DefectFibre N epsilon D,
    if 2 * s.val.M = m then profileKernel s.val else 0

theorem kernel_nonneg (N epsilon m : ℕ) : 0 ≤ kernel N epsilon m := by
  unfold kernel
  apply Finset.sum_nonneg
  intro D _
  apply Finset.sum_nonneg
  intro s _
  split_ifs
  · exact profileKernel_nonneg s.val
  · exact le_rfl

theorem kernel_eq_zero_of_source_le (N epsilon m : ℕ) (hm : 2 * N + epsilon ≤ m) :
    kernel N epsilon m = 0 := by
  unfold kernel
  apply Finset.sum_eq_zero
  intro D hD
  apply Finset.sum_eq_zero
  intro s _
  have hs := target_lt_source s (Finset.mem_Icc.mp hD).1
  exact if_neg (by omega)

/-- Exact weighted regrouping; the target sequence is arbitrary. -/
theorem weighted_sum_eq (N epsilon : ℕ) (a : ℕ → ℝ) :
    (∑ m ∈ Finset.range (2 * N + epsilon), kernel N epsilon m * a m) =
      ∑ D ∈ Finset.Icc 1 N, ∑ s : DefectFibre N epsilon D,
        profileKernel s.val * a (2 * s.val.M) := by
  unfold kernel
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hs : 2 * s.val.M ∈ Finset.range (2 * N + epsilon) :=
    Finset.mem_range.mpr (target_lt_source s (Finset.mem_Icc.mp hD).1)
  simp only [ite_mul, zero_mul]
  simp [hs]

theorem row_sum_eq (N epsilon : ℕ) :
    (∑ m ∈ Finset.range (2 * N + epsilon), kernel N epsilon m) =
      positiveDefectRow N epsilon := by
  simpa only [mul_one, positiveDefectRow, defectKernel] using
    weighted_sum_eq N epsilon (fun _ => 1)

theorem eventually_both_parities :
    ∀ᶠ N : ℕ in atTop, ∀ epsilon : ℕ, epsilon ≤ 1 →
      (∑ m ∈ Finset.range (2 * N + epsilon), kernel N epsilon m) ≤
        (2 : ℝ) ^ (-(N : ℝ) / 10) := by
  filter_upwards [MarkerNormalizedRow.eventually_both_parities] with N hN
  intro epsilon hepsilon
  rw [row_sum_eq]
  exact hN epsilon hepsilon

end SymmetricSubgroupAsymptotics.MarkerForwardRow
