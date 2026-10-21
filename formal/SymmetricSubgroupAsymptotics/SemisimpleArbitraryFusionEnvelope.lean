import SymmetricSubgroupAsymptotics.Non2PreE7CompleteSourceComparator

/-! The correlated semisimple source bound is independent of the fusion
survival predicate. In particular a surviving regular C3 elsewhere in the
literal complement does not prevent using the same semisimple comparator.
The complete sum over the original normal axes is bounded only once. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics

namespace SemisimpleNormalChart

/-- No local owner exclusion or no-C3 predicate is needed by the actual
outer-fibre estimate. -/
theorem fusionCompleteSourceSum_le {w b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (E : Subgroup U) [E.Normal] (C : SemisimpleNormalChart E)
    (P : Subgroup (U×Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionCompleteSourceSum U P J ≤
      completeQuotientWeight (R := U⧸E) J *
        C.outerFactor (Real.logb 2 (Nat.card J)) := by
  have hs : fusionCompleteSourceSum U P J ≤
      ∑ N : {N : Subgroup U // N.Normal},
        (Nat.card (GroupEpimorphism J (U⧸N.1)) : ℝ) := by
    unfold fusionCompleteSourceSum
    exact Finset.sum_le_sum (fun N _ =>
      fusionSurvivingEpiCount_le_groupEpimorphism_card U P N J)
  exact hs.trans (by
    simpa only [completeQuotientWeight,completeQuotientCount,Nat.cast_sum]
      using C.outerSum_le (J := J))

end SemisimpleNormalChart

namespace Non2UnipotentPrefixFiniteMenu.PreE7SemisimpleCompleteSourceData

variable {family : PreE7NoPairNoC3EarlierOwnerFamily}
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (D : PreE7SemisimpleCompleteSourceData family w i)

/-- The exact complete-source estimate of the existing certificate holds
for every predicate on the original deleted subgroup, without changing its
normal axes or requiring containment in the older broad owner predicate. -/
theorem arbitrary_predicate_source_bound (b : ℕ)
    (P : Subgroup (preE7NonPairAction w i×Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionCompleteSourceSum (preE7NonPairAction w i) P J ≤
      (D.coefficient b*(2 : ℝ)^(D.eta*b))*
        completeQuotientWeight (R := preE7NonPairAction w i⧸D.E) J := by
  have h := D.chart.fusionCompleteSourceSum_le (preE7NonPairAction w i) D.E P J
  have hfactor := D.outer_bound b J
  have hweight : 0≤completeQuotientWeight
      (R := preE7NonPairAction w i⧸D.E) J := completeQuotientWeight_nonneg J
  exact h.trans (by
    calc
      _ ≤ completeQuotientWeight (R := preE7NonPairAction w i⧸D.E) J *
          (D.coefficient b*(2 : ℝ)^(D.eta*b)) :=
        mul_le_mul_of_nonneg_left hfactor hweight
      _ = _ := by ring)

/-- The same hot/cold transfer works for every natural surviving predicate.
The coefficient is not multiplied by the number of original normal axes. -/
theorem arbitrary_predicate_kernel_bound (b : ℕ)
    (P : Subgroup (preE7NonPairAction w i×Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural (preE7NonPairAction w i) P) :
    (Nat.card (FusionOrbitFamily (preE7NonPairAction w i)
      (FusionAcceptedOrbitPredicate (preE7NonPairAction w i) P)) : ℝ) /
      exactBenchmark (b+w) ≤
    growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
      b w D.v (D.coefficient b)
      (Nat.card (Subgroup.normalizer
        (preE7NonPairAction w i : Set (Equiv.Perm (Fin w)))) : ℝ)
      D.eta D.delta D.cutoff +
    fusionWidthColdKernel b w (D.coefficient b)
      (Nat.card (Subgroup.normalizer
        (preE7NonPairAction w i : Set (Equiv.Perm (Fin w)))) : ℝ)
      D.alpha * ((subgroupCount b : ℝ)/exactBenchmark b) := by
  have h := fusionPhysical_growingQuotient_additiveTail_kernel_bound
    (preE7NonPairAction w i) P hP D.action D.action_injective
    (D.coefficient b) 0 D.eta D.theta D.delta D.cutoff
    (D.coefficient_nonneg b) le_rfl (by
      intro J
      simpa only [zero_mul,add_zero] using D.arbitrary_predicate_source_bound b P J)
  simpa only [D.alpha_eq,fusionWidthColdKernel,zero_mul,mul_zero,zero_div,add_zero]
    using h

end Non2UnipotentPrefixFiniteMenu.PreE7SemisimpleCompleteSourceData
end SymmetricSubgroupAsymptotics
