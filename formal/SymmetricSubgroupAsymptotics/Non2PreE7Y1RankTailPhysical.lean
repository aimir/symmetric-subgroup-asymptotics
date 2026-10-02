import SymmetricSubgroupAsymptotics.FusionPhysicalSummedSource
import SymmetricSubgroupAsymptotics.Non2PreE7Y1RankTailInstance

/-!
# Physical Y1 row with the index-three binary rank tail retained

The cold and hot complete-source terms remain correlated until after the
sum over literal sources.  Physical pointing then installs the original
width-eight action and its normalizer exactly once.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Kernel transfer when the comparator and cold tail are controlled only
after summing over complete sources, with one further correlated exceptional
term.  This is the honest interface for a hot/cold source split whose hot
part has already been counted by a separate moment. -/
theorem fusionPhysical_growingQuotient_additiveTail_summedExceptional_kernel_bound
    {R : Type*} [Group R] [Finite R] {w v b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (rhoR : R →* Equiv.Perm (Fin v)) (hrhoR : Function.Injective rhoR)
    (D T eta theta delta c E : ℝ) (hD : 0 ≤ D)
    (hsum : (∑ J : Subgroup (Equiv.Perm (Fin b)),
        fusionCompleteSourceSum U P J) ≤
      (∑ J : Subgroup (Equiv.Perm (Fin b)),
        ((D * (2 : ℝ) ^ (eta * b)) *
            completeQuotientWeight (R := R) J +
          T * (2 : ℝ) ^ (theta * b))) + E) :
    (Nat.card
        (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + w) ≤
      growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
          b w v D
          (Nat.card
            (Subgroup.normalizer
              (U : Set (Equiv.Perm (Fin w)))) : ℝ)
          eta delta c +
        fusionWidthColdKernel b w D
          (Nat.card
            (Subgroup.normalizer
              (U : Set (Equiv.Perm (Fin w)))) : ℝ)
          (eta + c) * ((subgroupCount b : ℝ) / exactBenchmark b) +
        fusionWidthColdKernel b w T
          (Nat.card
            (Subgroup.normalizer
              (U : Set (Equiv.Perm (Fin w)))) : ℝ)
          theta * ((subgroupCount b : ℝ) / exactBenchmark b) +
        growingQuotientNormalizedPointing b w
          (Nat.card
            (Subgroup.normalizer
              (U : Set (Equiv.Perm (Fin w)))) : ℝ) * E := by
  let q := growingQuotientMoment delta (v : ℝ) (b : ℝ)
  let A : ℝ := Nat.card
    (Subgroup.normalizer (U : Set (Equiv.Perm (Fin w))))
  let point : ℝ := growingQuotientNormalizedPointing b w A
  have hq : 1 ≤ q := growingQuotientMoment_pos delta (v : ℝ) (b : ℝ)
  have hmain : 0 ≤ D * (2 : ℝ) ^ (eta * b) :=
    mul_nonneg hD (by positivity)
  have ht := growingQuotientThreshold_pos c b
  have hsplit := fusion_hot_cold_sum_le
    (fun J : Subgroup (Equiv.Perm (Fin b)) =>
      (D * (2 : ℝ) ^ (eta * b)) * completeQuotientWeight (R := R) J)
    (completeQuotientWeight (R := R)) hmain ht
    (completeQuotientWeight_nonneg (R := R))
    (fun J => le_rfl) hq
    (completeQuotientWeight_moment_le rhoR hrhoR b q)
  have hbase :
      (∑ J : Subgroup (Equiv.Perm (Fin b)),
        ((D * (2 : ℝ) ^ (eta * b)) *
            completeQuotientWeight (R := R) J +
          T * (2 : ℝ) ^ (theta * b))) ≤
        D * (2 : ℝ) ^ (eta * b) /
              growingQuotientThreshold c b ^ (q - 1) *
              (subgroupCount (b + q * v) : ℝ) +
          (subgroupCount b : ℝ) * D * (2 : ℝ) ^ (eta * b) *
              growingQuotientThreshold c b +
          (subgroupCount b : ℝ) * T * (2 : ℝ) ^ (theta * b) := by
    rw [Finset.sum_add_distrib]
    have hsplit' :
        (∑ J : Subgroup (Equiv.Perm (Fin b)),
          (D * (2 : ℝ) ^ (eta * b)) *
            completeQuotientWeight (R := R) J) ≤
          D * (2 : ℝ) ^ (eta * b) /
                growingQuotientThreshold c b ^ (q - 1) *
                (subgroupCount (b + q * v) : ℝ) +
            (subgroupCount b : ℝ) *
              (D * (2 : ℝ) ^ (eta * b)) *
                growingQuotientThreshold c b := by
      simpa only [subgroupCount] using hsplit
    have htail :
        (∑ _J : Subgroup (Equiv.Perm (Fin b)),
          T * (2 : ℝ) ^ (theta * b)) =
          (subgroupCount b : ℝ) * T * (2 : ℝ) ^ (theta * b) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_eq_nat_card, subgroupCount]
      ring
    rw [htail]
    nlinarith
  have htotal := hsum.trans (add_le_add hbase (le_refl E))
  have hphysical := fusionPhysical_summedSource_normalized_bound
    U P hP _ htotal
  change _ ≤
    growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
        b w v D A eta delta c +
      fusionWidthColdKernel b w D A (eta + c) *
        ((subgroupCount b : ℝ) / exactBenchmark b) +
      fusionWidthColdKernel b w T A theta *
        ((subgroupCount b : ℝ) / exactBenchmark b) + point * E
  calc
    _ ≤ point *
        ((D * (2 : ℝ) ^ (eta * b) /
              growingQuotientThreshold c b ^ (q - 1) *
              (subgroupCount (b + q * v) : ℝ) +
          (subgroupCount b : ℝ) * D * (2 : ℝ) ^ (eta * b) *
              growingQuotientThreshold c b +
          (subgroupCount b : ℝ) * T * (2 : ℝ) ^ (theta * b)) + E) := by
      simpa only [point] using hphysical
    _ = point *
          (D * (2 : ℝ) ^ (eta * b) /
              growingQuotientThreshold c b ^ (q - 1) *
              (subgroupCount (b + q * v) : ℝ)) +
        point *
          ((subgroupCount b : ℝ) * D * (2 : ℝ) ^ (eta * b) *
              growingQuotientThreshold c b) +
        point *
          ((subgroupCount b : ℝ) * T * (2 : ℝ) ^ (theta * b)) +
        point * E := by ring
    _ = _ := by
      rw [show point *
          (D * (2 : ℝ) ^ (eta * b) /
              growingQuotientThreshold c b ^ (q - 1) *
              (subgroupCount (b + q * v) : ℝ)) =
            growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
              b w v D A eta delta c by
        simpa only [point, q, growingQuotientGraphDegree] using
          growingQuotient_hot_identity
            (fun n => (subgroupCount n : ℝ))
            b w v D A eta delta c]
      rw [show point *
          ((subgroupCount b : ℝ) * D * (2 : ℝ) ^ (eta * b) *
              growingQuotientThreshold c b) =
            fusionWidthColdKernel b w D A (eta + c) *
              ((subgroupCount b : ℝ) / exactBenchmark b) by
        simpa only [point] using
          (growingQuotient_cold_identity (subgroupCount b : ℝ)
            b w D A eta c)]
      rw [show point *
          ((subgroupCount b : ℝ) * T * (2 : ℝ) ^ (theta * b)) =
            fusionWidthColdKernel b w T A theta *
              ((subgroupCount b : ℝ) / exactBenchmark b) by
        simpa only [point, growingQuotientThreshold, zero_mul, Real.rpow_zero,
          mul_one, add_zero] using
          (growingQuotient_cold_identity (subgroupCount b : ℝ)
            b w T A theta 0)]



namespace PreE7Y1RankTailCertificate

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (C : PreE7Y1RankTailCertificate w i)

/-- The Y1 certificate gives a physical original-weight row without a
pointwise-in-source envelope. -/
theorem physical_normalized_bound
    (b : ℕ)
    (P : Subgroup
      (preE7NonPairAction w i × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural (preE7NonPairAction w i) P) :
    (Nat.card (FusionOrbitFamily (preE7NonPairAction w i)
        (FusionAcceptedOrbitPredicate (preE7NonPairAction w i) P)) : ℝ) /
        exactBenchmark (b + w) ≤
      growingQuotientNormalizedPointing b w
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w i :
              Set (Equiv.Perm (Fin w)))) : ℝ) *
        (C.coldConstant * (1 + b) *
              (2 : ℝ) ^ ((153 / 200 : ℝ) * b) *
              (subgroupCount b : ℝ) +
          C.normalCount * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
            ((Nat.factorial b : ℝ) *
              ((2 : ℝ) ^
                  (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
                (subgroupCount
                  (b + 2 * rankTail51Tilt b) : ℝ)))) := by
  exact fusionPhysical_summedSource_normalized_bound
    (preE7NonPairAction w i) P hP _ (C.summed b P)

end PreE7Y1RankTailCertificate

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
