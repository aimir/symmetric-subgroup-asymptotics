import SymmetricSubgroupAsymptotics.GrowingQuotientHotKernel

/-!
# Physical transfer for estimates already summed over complete sources

Rank-tail arguments must keep the source temperature visible until after the
sum over all complete sources.  Their output is therefore a bound on

`sum J, fusionCompleteSourceSum U P J`

rather than a pointwise envelope for each `J`.  This file transfers that
bound through the original action normalizer and exact benchmark without
reopening or independently maximizing any normal axis or source fibre.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- An estimate already summed over every literal complete source gives the
physical original-weight bound with the original action divisor. -/
theorem fusionPhysical_summedSource_normalized_bound
    {w b : ℕ} (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P) (B : ℝ)
    (hsum : (∑ J : Subgroup (Equiv.Perm (Fin b)),
      fusionCompleteSourceSum U P J) ≤ B) :
    (Nat.card
        (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + w) ≤
      growingQuotientNormalizedPointing b w
        (Nat.card (Subgroup.normalizer
          (U : Set (Equiv.Perm (Fin w)))) : ℝ) * B := by
  let A : ℝ := Nat.card
    (Subgroup.normalizer (U : Set (Equiv.Perm (Fin w))))
  let point : ℝ := growingQuotientNormalizedPointing b w A
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
      (U : Set (Equiv.Perm (Fin w)))))
  have hpoint : 0 ≤ point := by
    dsimp [point]
    unfold growingQuotientNormalizedPointing
    exact div_nonneg
      (div_nonneg (div_nonneg (by positivity) (by positivity)) hA.le)
      (exactBenchmark_pos (b + w)).le
  have hphysical := fusionPhysical_original_weight U P hP
  simp only [Fintype.card_fin, Nat.add_comm w b] at hphysical
  have hnormalized :
      (Nat.card
          (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
          exactBenchmark (b + w) ≤
        point *
          (∑ J : Subgroup (Equiv.Perm (Fin b)),
            fusionCompleteSourceSum U P J) := by
    have hbench := exactBenchmark_pos (b + w)
    have hdiv := div_le_div_of_nonneg_right hphysical hbench.le
    convert hdiv using 1
    simp only [fusionCompleteSourceSum, Nat.cast_sum]
    rw [Finset.sum_comm]
    unfold fusionSurvivingEpiCount
    dsimp [point, growingQuotientNormalizedPointing, A]
    ring
  exact hnormalized.trans (mul_le_mul_of_nonneg_left hsum hpoint)

end SymmetricSubgroupAsymptotics

end
