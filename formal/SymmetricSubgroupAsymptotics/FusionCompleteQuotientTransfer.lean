import SymmetricSubgroupAsymptotics.FusionFiniteMenu
import SymmetricSubgroupAsymptotics.GrowingQuotientTransferNumerics

/-!
# Whole-axis physical transfer through a complete quotient comparator

The local envelope in the growing-parameter theorem is a bound on the sum
over every literal normal axis of one original action.  This module performs
that sum before the hot/cold split, applies the complete quotient moment on
the unchanged source, and retains the original physical normalizer divisor.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- The complete surviving quotient-map fibre over one unchanged source,
summed over every literal normal axis of the original action. -/
def fusionCompleteSourceSum {w b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) : ℝ :=
  ∑ N : {N : Subgroup U // N.Normal}, fusionSurvivingEpiCount U P N J

theorem fusionCompleteSourceSum_nonneg {w b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    0 ≤ fusionCompleteSourceSum U P J := by
  unfold fusionCompleteSourceSum
  apply Finset.sum_nonneg
  intro N _
  unfold fusionSurvivingEpiCount
  exact Nat.cast_nonneg _

/-- Whole-axis physical hot/cold transfer.  The comparator need not be a
quotient of `U`: only its faithful action and the stated complete-fibre
envelope are used. -/
theorem fusionPhysical_completeQuotient_bound
    {R : Type*} [Group R] [Finite R] {w v b q : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (ρR : R →* Equiv.Perm (Fin v)) (hρR : Function.Injective ρR)
    (D t : ℝ) (hD : 0 ≤ D) (ht : 0 < t) (hq : 1 ≤ q)
    (henvelope : ∀ J,
      fusionCompleteSourceSum U P J ≤
        D * completeQuotientWeight (R := R) J) :
    (Nat.card
        (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) ≤
      ((b + w).factorial : ℝ) /
          ((b.factorial : ℝ) *
            (Nat.card
              (Subgroup.normalizer
                (U : Set (Equiv.Perm (Fin w)))) : ℝ)) *
        (D / t ^ (q - 1) * (subgroupCount (b + q * v) : ℝ) +
          (subgroupCount b : ℝ) * D * t) := by
  have hlocal := fusion_hot_cold_sum_le
    (fusionCompleteSourceSum U P)
    (completeQuotientWeight (R := R))
    hD ht (completeQuotientWeight_nonneg (R := R)) henvelope hq
    (completeQuotientWeight_moment_le ρR hρR b q)
  have hphysical := fusionPhysical_original_weight U P hP
  simp only [Fintype.card_fin, Nat.add_comm w b] at hphysical
  apply hphysical.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  push_cast
  rw [Finset.sum_comm]
  simpa only [fusionCompleteSourceSum, subgroupCount,
    Nat.card_eq_fintype_card] using hlocal

/-- Benchmark-normalized form of the whole-axis transfer. -/
theorem fusionPhysical_completeQuotient_normalized_bound
    {R : Type*} [Group R] [Finite R] {w v b q : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (ρR : R →* Equiv.Perm (Fin v)) (hρR : Function.Injective ρR)
    (D t : ℝ) (hD : 0 ≤ D) (ht : 0 < t) (hq : 1 ≤ q)
    (henvelope : ∀ J,
      fusionCompleteSourceSum U P J ≤
        D * completeQuotientWeight (R := R) J) :
    (Nat.card
        (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + w) ≤
      ((((b + w).factorial : ℝ) / (b.factorial : ℝ)) /
          (Nat.card
            (Subgroup.normalizer
              (U : Set (Equiv.Perm (Fin w)))) : ℝ)) /
          exactBenchmark (b + w) *
        (D / t ^ (q - 1) * (subgroupCount (b + q * v) : ℝ) +
          (subgroupCount b : ℝ) * D * t) := by
  have h := fusionPhysical_completeQuotient_bound U P hP ρR hρR D t hD ht hq henvelope
  have hbench := exactBenchmark_pos (b + w)
  apply (div_le_div_of_nonneg_right h hbench.le).trans_eq
  field_simp

end SymmetricSubgroupAsymptotics

end
