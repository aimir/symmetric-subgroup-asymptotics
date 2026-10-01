import SymmetricSubgroupAsymptotics.FiniteComparatorListMoment
import SymmetricSubgroupAsymptotics.GrowingQuotientAdditiveTail

/-!
# Physical transfer for a finite comparator-list statistic

The growing quotient argument only needs a nonnegative source statistic and
its simultaneous moments.  This file records that general form and applies
it to the literal arithmetic mean of a finite comparator list.  It is the
missing transfer used by the historical `fiveExc` owner.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- Whole-axis hot/cold transfer through an arbitrary nonnegative statistic
with the same degree-`v` moment bound as a complete quotient count. -/
theorem fusionPhysical_statistic_normalized_bound
    {w v b q : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (W : Subgroup (Equiv.Perm (Fin b)) → ℝ)
    (hW : ∀ J, 0 ≤ W J)
    (hmoment : (∑ J : Subgroup (Equiv.Perm (Fin b)), W J ^ q) ≤
      (subgroupCount (b + q * v) : ℝ))
    (D t : ℝ) (hD : 0 ≤ D) (ht : 0 < t) (hq : 1 ≤ q)
    (henvelope : ∀ J, fusionCompleteSourceSum U P J ≤ D * W J) :
    (Nat.card
        (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + w) ≤
      growingQuotientNormalizedPointing b w
          (Nat.card (Subgroup.normalizer
            (U : Set (Equiv.Perm (Fin w)))) : ℝ) *
        (D / t ^ (q - 1) * (subgroupCount (b + q * v) : ℝ) +
          (subgroupCount b : ℝ) * D * t) := by
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
  have hsum := fusion_hot_cold_sum_le
    (fusionCompleteSourceSum U P) W hD ht hW henvelope hq hmoment
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
  apply hnormalized.trans
  dsimp [A, point]
  exact mul_le_mul_of_nonneg_left (by
    simpa only [subgroupCount] using hsum) hpoint

/-- The statistic transfer with a source-independent additive tail.  The
tail remains a separate cold row and is never inserted into the statistic's
hot set. -/
theorem fusionPhysical_statistic_additiveTail_normalized_bound
    {w v b q : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (W : Subgroup (Equiv.Perm (Fin b)) → ℝ)
    (hW : ∀ J, 0 ≤ W J)
    (hmoment : (∑ J : Subgroup (Equiv.Perm (Fin b)), W J ^ q) ≤
      (subgroupCount (b + q * v) : ℝ))
    (D T t : ℝ) (hD : 0 ≤ D)
    (ht : 0 < t) (hq : 1 ≤ q)
    (henvelope : ∀ J,
      fusionCompleteSourceSum U P J ≤ D * W J + T) :
    (Nat.card
        (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + w) ≤
      growingQuotientNormalizedPointing b w
          (Nat.card (Subgroup.normalizer
            (U : Set (Equiv.Perm (Fin w)))) : ℝ) *
        (D / t ^ (q - 1) * (subgroupCount (b + q * v) : ℝ) +
          (subgroupCount b : ℝ) * D * t +
          (subgroupCount b : ℝ) * T) := by
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
  have hmain := fusion_hot_cold_sum_le
    (fun J : Subgroup (Equiv.Perm (Fin b)) => D * W J)
    W hD ht hW (fun _ => le_rfl) hq hmoment
  have hsum :
      (∑ J : Subgroup (Equiv.Perm (Fin b)),
          fusionCompleteSourceSum U P J) ≤
        (D / t ^ (q - 1) * (subgroupCount (b + q * v) : ℝ) +
          (subgroupCount b : ℝ) * D * t) +
          (subgroupCount b : ℝ) * T := by
    calc
      _ ≤ ∑ J : Subgroup (Equiv.Perm (Fin b)), (D * W J + T) :=
        Finset.sum_le_sum (fun J _ => henvelope J)
      _ = (∑ J : Subgroup (Equiv.Perm (Fin b)), D * W J) +
          (subgroupCount b : ℝ) * T := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_eq_nat_card, subgroupCount]
      _ ≤ _ := by
        have hm : (∑ J : Subgroup (Equiv.Perm (Fin b)), D * W J) ≤
            D / t ^ (q - 1) * (subgroupCount (b + q * v) : ℝ) +
              (subgroupCount b : ℝ) * D * t := by
          simpa only [subgroupCount] using hmain
        linarith
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
  apply hnormalized.trans
  dsimp [A, point]
  exact mul_le_mul_of_nonneg_left hsum hpoint

/-- Kernel form of the general statistic transfer. -/
theorem fusionPhysical_statistic_kernel_bound
    {w v b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (W : Subgroup (Equiv.Perm (Fin b)) → ℝ)
    (hW : ∀ J, 0 ≤ W J)
    (hmoment : ∀ q,
      (∑ J : Subgroup (Equiv.Perm (Fin b)), W J ^ q) ≤
        (subgroupCount (b + q * v) : ℝ))
    (D delta c : ℝ) (hD : 0 ≤ D)
    (henvelope : ∀ J, fusionCompleteSourceSum U P J ≤ D * W J) :
    (Nat.card
        (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + w) ≤
      growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
          b w v D
          (Nat.card (Subgroup.normalizer
            (U : Set (Equiv.Perm (Fin w)))) : ℝ)
          0 delta c +
        fusionWidthColdKernel b w D
          (Nat.card (Subgroup.normalizer
            (U : Set (Equiv.Perm (Fin w)))) : ℝ)
          c * ordinarySubgroupRatio b := by
  let q := growingQuotientMoment delta (v : ℝ) (b : ℝ)
  let A : ℝ := Nat.card
    (Subgroup.normalizer (U : Set (Equiv.Perm (Fin w))))
  have hq : 1 ≤ q := growingQuotientMoment_pos delta (v : ℝ) (b : ℝ)
  have ht := growingQuotientThreshold_pos c b
  have hbound := fusionPhysical_statistic_normalized_bound
    U P hP W hW (hmoment q) D (growingQuotientThreshold c b)
      hD ht hq henvelope
  change _ ≤
    growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
        b w v D A 0 delta c +
      fusionWidthColdKernel b w D A c * ordinarySubgroupRatio b
  calc
    _ ≤ growingQuotientNormalizedPointing b w A *
        (D / growingQuotientThreshold c b ^ (q - 1) *
            (subgroupCount (b + q * v) : ℝ) +
          (subgroupCount b : ℝ) * D * growingQuotientThreshold c b) := by
      simpa only [q, A] using hbound
    _ = growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
          b w v D A 0 delta c +
        fusionWidthColdKernel b w D A c * ordinarySubgroupRatio b := by
      rw [mul_add]
      rw [show growingQuotientNormalizedPointing b w A *
          (D / growingQuotientThreshold c b ^ (q - 1) *
            (subgroupCount (b + q * v) : ℝ)) =
          growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
            b w v D A 0 delta c by
        simpa only [q, growingQuotientGraphDegree, zero_mul,
          Real.rpow_zero, mul_one] using
          growingQuotient_hot_identity
            (fun n => (subgroupCount n : ℝ)) b w v D A 0 delta c]
      rw [show growingQuotientNormalizedPointing b w A *
          ((subgroupCount b : ℝ) * D * growingQuotientThreshold c b) =
          fusionWidthColdKernel b w D A c * ordinarySubgroupRatio b by
        simpa only [ordinarySubgroupRatio, zero_add, zero_mul,
          Real.rpow_zero, mul_one] using
          (growingQuotient_cold_identity (subgroupCount b : ℝ)
            b w D A 0 c)]

/-- Kernel form with the independent tail retained as a second cold row. -/
theorem fusionPhysical_statistic_additiveTail_kernel_bound
    {w v b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (W : Subgroup (Equiv.Perm (Fin b)) → ℝ)
    (hW : ∀ J, 0 ≤ W J)
    (hmoment : ∀ q,
      (∑ J : Subgroup (Equiv.Perm (Fin b)), W J ^ q) ≤
        (subgroupCount (b + q * v) : ℝ))
    (D T theta delta c : ℝ) (hD : 0 ≤ D)
    (henvelope : ∀ J,
      fusionCompleteSourceSum U P J ≤
        D * W J + T * (2 : ℝ) ^ (theta * b)) :
    (Nat.card
        (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + w) ≤
      growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
          b w v D
          (Nat.card (Subgroup.normalizer
            (U : Set (Equiv.Perm (Fin w)))) : ℝ)
          0 delta c +
        fusionWidthColdKernel b w D
          (Nat.card (Subgroup.normalizer
            (U : Set (Equiv.Perm (Fin w)))) : ℝ)
          c * ordinarySubgroupRatio b +
        fusionWidthColdKernel b w T
          (Nat.card (Subgroup.normalizer
            (U : Set (Equiv.Perm (Fin w)))) : ℝ)
          theta * ordinarySubgroupRatio b := by
  let q := growingQuotientMoment delta (v : ℝ) (b : ℝ)
  let A : ℝ := Nat.card
    (Subgroup.normalizer (U : Set (Equiv.Perm (Fin w))))
  have hq : 1 ≤ q := growingQuotientMoment_pos delta (v : ℝ) (b : ℝ)
  have ht := growingQuotientThreshold_pos c b
  have hbound := fusionPhysical_statistic_additiveTail_normalized_bound
    U P hP W hW (hmoment q) D
      (T * (2 : ℝ) ^ (theta * b))
      (growingQuotientThreshold c b) hD ht hq henvelope
  change _ ≤
    growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
        b w v D A 0 delta c +
      fusionWidthColdKernel b w D A c * ordinarySubgroupRatio b +
      fusionWidthColdKernel b w T A theta * ordinarySubgroupRatio b
  calc
    _ ≤ growingQuotientNormalizedPointing b w A *
        (D / growingQuotientThreshold c b ^ (q - 1) *
            (subgroupCount (b + q * v) : ℝ) +
          (subgroupCount b : ℝ) * D * growingQuotientThreshold c b +
          (subgroupCount b : ℝ) *
            (T * (2 : ℝ) ^ (theta * b))) := by
      simpa only [q, A] using hbound
    _ = growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
          b w v D A 0 delta c +
        fusionWidthColdKernel b w D A c * ordinarySubgroupRatio b +
        fusionWidthColdKernel b w T A theta * ordinarySubgroupRatio b := by
      rw [mul_add, mul_add]
      rw [show growingQuotientNormalizedPointing b w A *
          (D / growingQuotientThreshold c b ^ (q - 1) *
            (subgroupCount (b + q * v) : ℝ)) =
          growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
            b w v D A 0 delta c by
        simpa only [q, growingQuotientGraphDegree, zero_mul,
          Real.rpow_zero, mul_one] using
          growingQuotient_hot_identity
            (fun n => (subgroupCount n : ℝ)) b w v D A 0 delta c]
      rw [show growingQuotientNormalizedPointing b w A *
          ((subgroupCount b : ℝ) * D * growingQuotientThreshold c b) =
          fusionWidthColdKernel b w D A c * ordinarySubgroupRatio b by
        simpa only [ordinarySubgroupRatio, zero_add, zero_mul,
          Real.rpow_zero, mul_one] using
          (growingQuotient_cold_identity (subgroupCount b : ℝ)
            b w D A 0 c)]
      rw [show growingQuotientNormalizedPointing b w A *
          ((subgroupCount b : ℝ) * (T * (2 : ℝ) ^ (theta * b))) =
          fusionWidthColdKernel b w T A theta * ordinarySubgroupRatio b by
        simpa only [ordinarySubgroupRatio, growingQuotientThreshold,
          zero_add, add_zero, zero_mul, Real.rpow_zero, mul_one, mul_assoc] using
          (growingQuotient_cold_identity (subgroupCount b : ℝ)
            b w T A theta 0)]

/-- The finite arithmetic mean of literal degree-`v` comparators supplies
the statistic and all of its moments automatically. -/
theorem fusionPhysical_finiteComparatorList_kernel_bound
    {κ : Type*} [Fintype κ] [Nonempty κ] {w v b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (Q : κ → Subgroup (Equiv.Perm (Fin v)))
    (D delta c : ℝ) (hD : 0 ≤ D)
    (henvelope : ∀ J,
      fusionCompleteSourceSum U P J ≤
        D * finiteComparatorListStatistic Q J) :
    (Nat.card
        (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + w) ≤
      growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
          b w v D
          (Nat.card (Subgroup.normalizer
            (U : Set (Equiv.Perm (Fin w)))) : ℝ)
          0 delta c +
        fusionWidthColdKernel b w D
          (Nat.card (Subgroup.normalizer
            (U : Set (Equiv.Perm (Fin w)))) : ℝ)
          c * ordinarySubgroupRatio b :=
  fusionPhysical_statistic_kernel_bound U P hP
    (finiteComparatorListStatistic Q)
    (finiteComparatorListStatistic_nonneg Q)
    (finiteComparatorListStatistic_moment_le Q b)
    D delta c hD henvelope

/-- Finite-list specialization with an independent additive cold tail. -/
theorem fusionPhysical_finiteComparatorList_additiveTail_kernel_bound
    {κ : Type*} [Fintype κ] [Nonempty κ] {w v b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (Q : κ → Subgroup (Equiv.Perm (Fin v)))
    (D T theta delta c : ℝ) (hD : 0 ≤ D)
    (henvelope : ∀ J,
      fusionCompleteSourceSum U P J ≤
        D * finiteComparatorListStatistic Q J +
          T * (2 : ℝ) ^ (theta * b)) :
    (Nat.card
        (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + w) ≤
      growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
          b w v D
          (Nat.card (Subgroup.normalizer
            (U : Set (Equiv.Perm (Fin w)))) : ℝ)
          0 delta c +
        fusionWidthColdKernel b w D
          (Nat.card (Subgroup.normalizer
            (U : Set (Equiv.Perm (Fin w)))) : ℝ)
          c * ordinarySubgroupRatio b +
        fusionWidthColdKernel b w T
          (Nat.card (Subgroup.normalizer
            (U : Set (Equiv.Perm (Fin w)))) : ℝ)
          theta * ordinarySubgroupRatio b :=
  fusionPhysical_statistic_additiveTail_kernel_bound U P hP
    (finiteComparatorListStatistic Q)
    (finiteComparatorListStatistic_nonneg Q)
    (finiteComparatorListStatistic_moment_le Q b)
    D T theta delta c hD henvelope

end SymmetricSubgroupAsymptotics

end
