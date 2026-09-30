import SymmetricSubgroupAsymptotics.SemisimpleOuterFibre
import SymmetricSubgroupAsymptotics.Non2PreE7NoPairNoC3EarlierComparators
import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailSource
import SymmetricSubgroupAsymptotics.TrivialQuotientComparator

/-!
# Comparator certificates from a semisimple normal layer

The semisimple outer-fibre theorem bounds the complete sum over all literal
normal quotients of an action `U` by the complete quotient weight of `U/E`
times the simple-factor outer product.  This file turns that joint statement
into the per-axis envelope expected by the pre-`E7` owner catalogue.  The
same literal `E`, quotient, normal axes, and source subgroup are retained.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Source data for a semisimple owner whose quotient has a concrete
faithful permutation action.  `coefficient` is allowed to retain the exact
simple-factor product; the only estimate requested here is its uniform
linear-in-source exponent. -/
structure PreE7SemisimpleOuterSourceData
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  template_eq : family.template = .semisimple
  E : Subgroup (preE7NonPairAction w i)
  [E_normal : E.Normal]
  chart : SemisimpleNormalChart E
  v : ℕ
  action : (preE7NonPairAction w i ⧸ E) →* Equiv.Perm (Fin v)
  action_injective : Function.Injective action
  coefficient : ℕ → ℝ
  eta : ℝ
  delta : ℝ
  cutoff : ℝ
  alpha : ℝ
  theta : ℝ
  alpha_eq : alpha = eta + cutoff
  coefficient_nonneg : ∀ b, 0 ≤ coefficient b
  coefficient_total_bound : ∀ b,
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
        (fun _ => coefficient b) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  outer_bound : ∀ b (J : Subgroup (Equiv.Perm (Fin b))),
    chart.outerFactor (Real.logb 2 (Nat.card J)) ≤
      coefficient b * (2 : ℝ) ^ (eta * b)

attribute [instance] PreE7SemisimpleOuterSourceData.E_normal

namespace PreE7SemisimpleOuterSourceData

variable {family : PreE7NoPairNoC3EarlierOwnerFamily}
  {w : ℕ} {i : PreE7NonPairActionClass w}
  (D : PreE7SemisimpleOuterSourceData family w i)

/-- The retained count on any one normal axis is bounded by the joint
semisimple outer fibre.  Using the joint sum here is intentional: it avoids
choosing or forgetting the induced quotient axis of `U/E`. -/
theorem broad_axis_envelope (b : ℕ)
    (N : {N : Subgroup (preE7NonPairAction w i) // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount (preE7NonPairAction w i)
        (preE7NoPairNoC3BroadActionPredicate w i b) N J ≤
      (D.coefficient b * (2 : ℝ) ^ (D.eta * b)) *
        completeQuotientWeight
          (R := preE7NonPairAction w i ⧸ D.E) J := by
  let U := preE7NonPairAction w i
  have hsurvive := fusionSurvivingEpiCount_le_groupEpimorphism_card U
    (preE7NoPairNoC3BroadActionPredicate w i b) N J
  have hsingle :
      (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) ≤
        ∑ M : {M : Subgroup U // M.Normal},
          (Nat.card (GroupEpimorphism J (U ⧸ M.1)) : ℝ) := by
    exact Finset.single_le_sum
      (f := fun M : {M : Subgroup U // M.Normal} ↦
        (Nat.card (GroupEpimorphism J (U ⧸ M.1)) : ℝ))
      (fun M _ => Nat.cast_nonneg _) (Finset.mem_univ N)
  have houter := D.chart.outerSum_le (J := J)
  have hfactor := D.outer_bound b J
  have hweight : 0 ≤ completeQuotientWeight
      (R := U ⧸ D.E) J := completeQuotientWeight_nonneg J
  calc
    fusionSurvivingEpiCount U
        (preE7NoPairNoC3BroadActionPredicate w i b) N J ≤
        (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) := hsurvive
    _ ≤ ∑ M : {M : Subgroup U // M.Normal},
          (Nat.card (GroupEpimorphism J (U ⧸ M.1)) : ℝ) := hsingle
    _ ≤ completeQuotientWeight (R := U ⧸ D.E) J *
          D.chart.outerFactor (Real.logb 2 (Nat.card J)) := by
      simpa only [U, completeQuotientWeight, completeQuotientCount,
        Nat.cast_sum] using houter
    _ ≤ completeQuotientWeight (R := U ⧸ D.E) J *
          (D.coefficient b * (2 : ℝ) ^ (D.eta * b)) :=
      mul_le_mul_of_nonneg_left hfactor hweight
    _ = (D.coefficient b * (2 : ℝ) ^ (D.eta * b)) *
          completeQuotientWeight (R := U ⧸ D.E) J := by ring

/-- A semisimple outer source gives the common earlier-action comparator
certificate with zero additive tail. -/
noncomputable def certificate :
    PreE7EarlierActionComparatorCertificate family w i where
  R := preE7NonPairAction w i ⧸ D.E
  groupR := inferInstance
  finiteR := inferInstance
  v := D.v
  action := D.action
  action_injective := D.action_injective
  C := fun b _ => D.coefficient b
  tailCoefficient := fun _ _ => 0
  eta := D.eta
  delta := D.delta
  cutoff := D.cutoff
  alpha := D.alpha
  theta := D.theta
  alpha_eq := D.alpha_eq
  coefficient_nonneg := fun b _ => D.coefficient_nonneg b
  tail_nonneg := fun _ _ => le_rfl
  broad_axis_envelope := by
    intro b N J
    simpa only [zero_mul, add_zero] using D.broad_axis_envelope b N J

end PreE7SemisimpleOuterSourceData

/-! ## Direct semisimple envelopes without a quotient action -/

/-- Some semisimple sources, notably `SS` and `SNS`, bound the whole outer
quotient weight directly and never assign a faithful permutation action to
`U/E`.  This is the faithful formal shape of that argument.  The comparator
is trivial, while `combined_bound` keeps the complete literal quotient sum
and the semisimple outer factor multiplied together. -/
structure PreE7SemisimpleDirectSourceData
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  template_eq : family.template = .semisimple
  E : Subgroup (preE7NonPairAction w i)
  [E_normal : E.Normal]
  chart : SemisimpleNormalChart E
  v : ℕ
  coefficient : ℕ → ℝ
  eta : ℝ
  delta : ℝ
  cutoff : ℝ
  alpha : ℝ
  theta : ℝ
  alpha_eq : alpha = eta + cutoff
  coefficient_nonneg : ∀ b, 0 ≤ coefficient b
  coefficient_total_bound : ∀ b,
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
        (fun _ => coefficient b) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  combined_bound : ∀ b (J : Subgroup (Equiv.Perm (Fin b))),
    completeQuotientWeight
        (R := preE7NonPairAction w i ⧸ E) J *
      chart.outerFactor (Real.logb 2 (Nat.card J)) ≤
        coefficient b * (2 : ℝ) ^ (eta * b)

attribute [instance] PreE7SemisimpleDirectSourceData.E_normal

namespace PreE7SemisimpleDirectSourceData

variable {family : PreE7NoPairNoC3EarlierOwnerFamily}
  {w : ℕ} {i : PreE7NonPairActionClass w}
  (D : PreE7SemisimpleDirectSourceData family w i)

/-- A direct semisimple source gives a common earlier-owner certificate with
the trivial complete comparator. -/
noncomputable def certificate :
    PreE7EarlierActionComparatorCertificate family w i where
  R := PUnit
  groupR := inferInstance
  finiteR := inferInstance
  v := D.v
  action := 1
  action_injective := fun _ _ _ => Subsingleton.elim _ _
  C := fun b _ => D.coefficient b
  tailCoefficient := fun _ _ => 0
  eta := D.eta
  delta := D.delta
  cutoff := D.cutoff
  alpha := D.alpha
  theta := D.theta
  alpha_eq := D.alpha_eq
  coefficient_nonneg := fun b _ => D.coefficient_nonneg b
  tail_nonneg := fun _ _ => le_rfl
  broad_axis_envelope := by
    intro b N J
    rw [completeQuotientWeight_eq_one_of_subsingleton (R := PUnit) J]
    let U := preE7NonPairAction w i
    have hsurvive := fusionSurvivingEpiCount_le_groupEpimorphism_card U
      (preE7NoPairNoC3BroadActionPredicate w i b) N J
    have hsingle :
        (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) ≤
          ∑ M : {M : Subgroup U // M.Normal},
            (Nat.card (GroupEpimorphism J (U ⧸ M.1)) : ℝ) := by
      exact Finset.single_le_sum
        (f := fun M : {M : Subgroup U // M.Normal} ↦
          (Nat.card (GroupEpimorphism J (U ⧸ M.1)) : ℝ))
        (fun M _ => Nat.cast_nonneg _) (Finset.mem_univ N)
    have houter := D.chart.outerSum_le (J := J)
    have hcombined := D.combined_bound b J
    calc
      fusionSurvivingEpiCount U
          (preE7NoPairNoC3BroadActionPredicate w i b) N J ≤
          (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) := hsurvive
      _ ≤ ∑ M : {M : Subgroup U // M.Normal},
            (Nat.card (GroupEpimorphism J (U ⧸ M.1)) : ℝ) := hsingle
      _ ≤ completeQuotientWeight (R := U ⧸ D.E) J *
            D.chart.outerFactor (Real.logb 2 (Nat.card J)) := by
        simpa only [U, completeQuotientWeight, completeQuotientCount,
          Nat.cast_sum] using houter
      _ ≤ D.coefficient b * (2 : ℝ) ^ (D.eta * b) := hcombined
      _ = (D.coefficient b * (2 : ℝ) ^ (D.eta * b)) * 1 +
          0 * (2 : ℝ) ^ (D.theta * b) := by ring

end PreE7SemisimpleDirectSourceData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
