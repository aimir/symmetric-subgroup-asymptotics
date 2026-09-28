import SymmetricSubgroupAsymptotics.C1NumericalRows
import SymmetricSubgroupAsymptotics.FusionWidthPhysical

/-!
# Original-weight consumers for the bounded c=1 owners

This file is the numerical interface between a fixed-source owner theorem and
the physical fusion recurrence.  The owner theorem sums over every literal
normal axis of the original action for one complete source.  The result below
then sums over complete sources, divides by the original action normalizer,
and installs the corresponding `C1EarlierRow` without changing the source or
the action weight.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- A fixed-source estimate already summed over every normal subgroup of the
original bounded action feeds the advertised c=1 row.  The factor `b+1` is
charged once, outside the normal-axis sum; the remaining source sum is exactly
`subgroupCount b`. -/
theorem c1EarlierPhysical_owner_bound (r : C1EarlierRow)
    (U : Subgroup (Equiv.Perm (Fin (c1EarlierWidth r)))) (b : ℕ)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P) (D : ℝ)
    (hsource : ∀ J : Subgroup (Equiv.Perm (Fin b)),
      (∑ N : {N : Subgroup U // N.Normal},
        fusionSurvivingEpiCount U P N J) ≤
          D * ((b : ℝ) + 1) * (2 : ℝ) ^ (c1EarlierExponent r * b)) :
    (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + c1EarlierWidth r) ≤
      c1EarlierKernel b r D
          (Nat.card (Subgroup.normalizer
            (U : Set (Equiv.Perm (Fin (c1EarlierWidth r))))) : ℝ) *
        ((subgroupCount b : ℝ) / exactBenchmark b) := by
  let a : ℝ := Nat.card (Subgroup.normalizer
    (U : Set (Equiv.Perm (Fin (c1EarlierWidth r)))))
  let q : ℝ := (((b + c1EarlierWidth r).factorial : ℝ) /
      ((b.factorial : ℝ) * a)) / exactBenchmark (b + c1EarlierWidth r)
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
      (U : Set (Equiv.Perm (Fin (c1EarlierWidth r))))))
  have hq : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (by positivity) (exactBenchmark_pos _).le
  have hphysical := div_le_div_of_nonneg_right
    (fusionPhysical_original_weight U P hP)
    (exactBenchmark_pos (b + c1EarlierWidth r)).le
  have hnorm :
      (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
          exactBenchmark (b + c1EarlierWidth r) ≤
        q * ∑ N : {N : Subgroup U // N.Normal},
          ∑ J : Subgroup (Equiv.Perm (Fin b)),
            fusionSurvivingEpiCount U P N J := by
    convert hphysical using 1
    simp only [Fintype.card_fin, Nat.cast_sum]
    unfold q a fusionSurvivingEpiCount
    ring
  calc
    _ ≤ q * ∑ N : {N : Subgroup U // N.Normal},
        ∑ J : Subgroup (Equiv.Perm (Fin b)),
          fusionSurvivingEpiCount U P N J := hnorm
    _ = q * ∑ J : Subgroup (Equiv.Perm (Fin b)),
        ∑ N : {N : Subgroup U // N.Normal},
          fusionSurvivingEpiCount U P N J := by rw [Finset.sum_comm]
    _ ≤ q * ∑ _J : Subgroup (Equiv.Perm (Fin b)),
        D * ((b : ℝ) + 1) * (2 : ℝ) ^ (c1EarlierExponent r * b) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun J _ => hsource J) hq
    _ = c1EarlierKernel b r D a *
        ((subgroupCount b : ℝ) / exactBenchmark b) := by
      rw [Finset.sum_const]
      simp only [Finset.card_univ, nsmul_eq_mul, Fintype.card_eq_nat_card]
      unfold c1EarlierKernel fusionWidthColdKernel fusionWidthPointingRatio
      dsimp [a, q]
      unfold subgroupCount
      field_simp [ne_of_gt ha, ne_of_gt (exactBenchmark_pos b),
        ne_of_gt (exactBenchmark_pos (b + c1EarlierWidth r))]

end SymmetricSubgroupAsymptotics
