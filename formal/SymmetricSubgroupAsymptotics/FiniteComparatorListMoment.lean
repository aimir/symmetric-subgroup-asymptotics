import Mathlib.Analysis.MeanInequalitiesPow
import SymmetricSubgroupAsymptotics.GrowingQuotientTransferNumerics

/-!
# Moments of a finite average of complete quotient statistics

The exceptional local-five owner retains a literal finite list of
comparators.  Its useful statistic is their arithmetic mean.  Jensen's
inequality and the simultaneous quotient-graph injection show that this
mean has the same subgroup moment as one comparator of the common faithful
degree.  No maximum and no deduplication of isomorphic list entries occurs.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {κ : Type*} [Fintype κ] {v : ℕ}

/-- The literal arithmetic mean of a finite comparator list. -/
def finiteComparatorListStatistic
    (Q : κ → Subgroup (Equiv.Perm (Fin v))) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) : ℝ :=
  (∑ k : κ, completeQuotientWeight (R := Q k) J) / Nat.card κ

theorem finiteComparatorListStatistic_nonneg
    (Q : κ → Subgroup (Equiv.Perm (Fin v))) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    0 ≤ finiteComparatorListStatistic Q J := by
  unfold finiteComparatorListStatistic
  exact div_nonneg (Finset.sum_nonneg fun k _ =>
    completeQuotientWeight_nonneg (R := Q k) J) (Nat.cast_nonneg _)

variable [Nonempty κ]

/-- A literal finite average has the same `q`-th moment bound as any one
faithful degree-`v` comparator in the list. -/
theorem finiteComparatorListStatistic_moment_le
    (Q : κ → Subgroup (Equiv.Perm (Fin v))) (b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        finiteComparatorListStatistic Q J ^ q) ≤
      (subgroupCount (b + q * v) : ℝ) := by
  have hmpos : (0 : ℝ) < Nat.card κ := by
    exact_mod_cast Nat.card_pos (α := κ)
  have hweight : ∀ k ∈ (Finset.univ : Finset κ),
      0 ≤ (1 / (Nat.card κ : ℝ)) := by
    intro _ _
    exact (one_div_nonneg.mpr hmpos.le)
  have hweight_sum :
      ∑ k ∈ (Finset.univ : Finset κ), (1 / (Nat.card κ : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card,
      nsmul_eq_mul]
    field_simp
  have hjensen (J : Subgroup (Equiv.Perm (Fin b))) :
      finiteComparatorListStatistic Q J ^ q ≤
        ∑ k : κ, (1 / (Nat.card κ : ℝ)) *
          completeQuotientWeight (R := Q k) J ^ q := by
    have h := Real.pow_arith_mean_le_arith_mean_pow
      (Finset.univ : Finset κ)
      (fun _ => 1 / (Nat.card κ : ℝ))
      (fun k => completeQuotientWeight (R := Q k) J)
      hweight hweight_sum
      (fun k _ => completeQuotientWeight_nonneg (R := Q k) J) q
    simpa [finiteComparatorListStatistic, div_eq_inv_mul,
      Finset.mul_sum] using h
  calc
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        finiteComparatorListStatistic Q J ^ q) ≤
        ∑ J : Subgroup (Equiv.Perm (Fin b)),
          ∑ k : κ, (1 / (Nat.card κ : ℝ)) *
            completeQuotientWeight (R := Q k) J ^ q :=
      Finset.sum_le_sum (fun J _ => hjensen J)
    _ = ∑ k : κ, (1 / (Nat.card κ : ℝ)) *
          ∑ J : Subgroup (Equiv.Perm (Fin b)),
            completeQuotientWeight (R := Q k) J ^ q := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
    _ ≤ ∑ _k : κ, (1 / (Nat.card κ : ℝ)) *
          (subgroupCount (b + q * v) : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left
        (completeQuotientWeight_moment_le (Q k).subtype
          Subtype.val_injective b q) (by positivity)
    _ = (subgroupCount (b + q * v) : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card,
        nsmul_eq_mul]
      field_simp

end SymmetricSubgroupAsymptotics

end
