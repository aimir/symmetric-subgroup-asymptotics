import SymmetricSubgroupAsymptotics.Non2PreE7NumericalEarlierPackage
import SymmetricSubgroupAsymptotics.SemisimpleOuterFibre

/-!
# Direct complete-source comparators for pre-E7 owners

Some owner arguments bound the complete sum over all literal normal axes in
one correlated inequality.  Turning such an inequality into a per-axis
bound and then summing the same majorant over the axes loses exactly the
correlation the proof established.  This module installs the complete-source
inequality directly in the physical local certificate.

The semisimple constructor is the main application.  Its outer-fibre theorem
already bounds the complete quotient weight of `U` by the weight of `U/E`
times one simple-factor product.  That product is now paid once.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- A comparator estimate for the complete literal normal-axis sum on one
action.  This is the source-level analogue of
`PreE7EarlierActionComparatorCertificate`, but its conclusion is correlated
before the normal-axis sum. -/
structure PreE7CompleteSourceComparatorCertificate
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  R : Type
  [groupR : Group R]
  [finiteR : Finite R]
  v : ℕ
  action : R →* Equiv.Perm (Fin v)
  action_injective : Function.Injective action
  D : ℕ → ℝ
  T : ℕ → ℝ
  eta : ℝ
  delta : ℝ
  cutoff : ℝ
  alpha : ℝ
  theta : ℝ
  alpha_eq : alpha = eta + cutoff
  D_nonneg : ∀ b, 0 ≤ D b
  T_nonneg : ∀ b, 0 ≤ T b
  broad_source_envelope : ∀ b (J : Subgroup (Equiv.Perm (Fin b))),
    fusionCompleteSourceSum (preE7NonPairAction w i)
        (preE7NoPairNoC3BroadActionPredicate w i b) J ≤
      (D b * (2 : ℝ) ^ (eta * b)) *
          completeQuotientWeight (R := R) J +
        T b * (2 : ℝ) ^ (theta * b)

attribute [instance]
  PreE7CompleteSourceComparatorCertificate.groupR
  PreE7CompleteSourceComparatorCertificate.finiteR

namespace PreE7CompleteSourceComparatorCertificate

variable {family : PreE7NoPairNoC3EarlierOwnerFamily}
  {w : ℕ} {i : PreE7NonPairActionClass w}

/-- A complete-source comparator gives the same physical hot/cold row as a
pointwise comparator, without repeating its coefficient over normal axes. -/
noncomputable def localCertificate
    (C : PreE7CompleteSourceComparatorCertificate family w i) :
    PreE7EarlierLocalCertificate family w i where
  D := C.D
  T := C.T
  X := fun _ => 0
  v := C.v
  eta := C.eta
  delta := C.delta
  cutoff := C.cutoff
  alpha := C.alpha
  theta := C.theta
  alpha_eq := C.alpha_eq
  D_nonneg := C.D_nonneg
  T_nonneg := C.T_nonneg
  local_bound := by
    intro b P hP hPbroad
    have hsource (J : Subgroup (Equiv.Perm (Fin b))) :
        fusionCompleteSourceSum (preE7NonPairAction w i) P J ≤
          (C.D b * (2 : ℝ) ^ (C.eta * b)) *
              completeQuotientWeight (R := C.R) J +
            C.T b * (2 : ℝ) ^ (C.theta * b) := by
      calc
        fusionCompleteSourceSum (preE7NonPairAction w i) P J ≤
            fusionCompleteSourceSum (preE7NonPairAction w i)
              (preE7NoPairNoC3BroadActionPredicate w i b) J := by
          unfold fusionCompleteSourceSum
          exact Finset.sum_le_sum (fun N _ =>
            fusionSurvivingEpiCount_mono hPbroad N J)
        _ ≤ _ := C.broad_source_envelope b J
    have h := fusionPhysical_growingQuotient_additiveTail_kernel_bound
      (preE7NonPairAction w i) P hP C.action C.action_injective
      (C.D b) (C.T b) C.eta C.theta C.delta C.cutoff
      (C.D_nonneg b) (C.T_nonneg b) hsource
    simpa only [C.alpha_eq, add_zero] using h

/-- The exceptional scalar of a complete-source comparator is zero. -/
noncomputable def localPackage
    (C : PreE7CompleteSourceComparatorCertificate family w i) :
    PreE7EarlierLocalPackage family w i where
  certificate := C.localCertificate
  exceptional := fun _ =>
    { threshold := 0
      rate := 1
      constant := 1
      rate_pos := by norm_num
      constant_pos := by norm_num
      bound := by simp [localCertificate] }
  exceptional_support := Or.inl rfl

end PreE7CompleteSourceComparatorCertificate

/-- Numerical data for a direct complete-source comparator. -/
structure PreE7CompleteSourceNumericalData
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  certificate : PreE7CompleteSourceComparatorCertificate family w i
  parameters : PreE7CharacterEntryParameters preE7CharacterRho w
    certificate.v certificate.eta certificate.delta certificate.cutoff
    certificate.alpha certificate.theta
  main_total_bound : ∀ b,
    certificate.D b ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  tail_total_bound : ∀ b,
    certificate.T b ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

/-- Direct complete-source data is a numerically complete earlier-owner
package and can enter the existing disjoint catalogue unchanged. -/
noncomputable def PreE7CompleteSourceNumericalData.toPackage
    {family : PreE7NoPairNoC3EarlierOwnerFamily}
    {w : ℕ} {i : PreE7NonPairActionClass w}
  (D : PreE7CompleteSourceNumericalData family w i) :
    PreE7EarlierNumericalPackage family w i where
  package := D.certificate.localPackage
  parameters := D.parameters
  main_total_growth := .inl D.main_total_bound
  tail_total_bound := D.tail_total_bound

/-! ## Semisimple outer-fibre constructor -/

/-- A semisimple normal layer whose quotient has a concrete faithful
comparator action.  The coefficient bounds the one outer-factor product,
not one copy of that product for every normal subgroup of the action. -/
structure PreE7SemisimpleCompleteSourceData
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) where
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
  parameters : PreE7CharacterEntryParameters preE7CharacterRho w v eta
    delta cutoff alpha theta
  coefficient_bound : ∀ b,
    coefficient b ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  outer_bound : ∀ b (J : Subgroup (Equiv.Perm (Fin b))),
    chart.outerFactor (Real.logb 2 (Nat.card J)) ≤
      coefficient b * (2 : ℝ) ^ (eta * b)

attribute [instance] PreE7SemisimpleCompleteSourceData.E_normal

namespace PreE7SemisimpleCompleteSourceData

variable {family : PreE7NoPairNoC3EarlierOwnerFamily}
  {w : ℕ} {i : PreE7NonPairActionClass w}
  (D : PreE7SemisimpleCompleteSourceData family w i)

/-- The exact semisimple outer-fibre inequality, retained at the complete
normal-axis level. -/
noncomputable def certificate :
    PreE7CompleteSourceComparatorCertificate family w i where
  R := preE7NonPairAction w i ⧸ D.E
  groupR := inferInstance
  finiteR := inferInstance
  v := D.v
  action := D.action
  action_injective := D.action_injective
  D := D.coefficient
  T := fun _ => 0
  eta := D.eta
  delta := D.delta
  cutoff := D.cutoff
  alpha := D.alpha
  theta := D.theta
  alpha_eq := D.alpha_eq
  D_nonneg := D.coefficient_nonneg
  T_nonneg := fun _ => le_rfl
  broad_source_envelope := by
    intro b J
    let U := preE7NonPairAction w i
    have hsurvive :
        fusionCompleteSourceSum U
            (preE7NoPairNoC3BroadActionPredicate w i b) J ≤
          ∑ N : {N : Subgroup U // N.Normal},
            (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) := by
      unfold fusionCompleteSourceSum
      exact Finset.sum_le_sum (fun N _ =>
        fusionSurvivingEpiCount_le_groupEpimorphism_card U
          (preE7NoPairNoC3BroadActionPredicate w i b) N J)
    have houter := D.chart.outerSum_le (J := J)
    have hfactor := D.outer_bound b J
    have hweight : 0 ≤ completeQuotientWeight
        (R := U ⧸ D.E) J := completeQuotientWeight_nonneg J
    calc
      fusionCompleteSourceSum U
          (preE7NoPairNoC3BroadActionPredicate w i b) J ≤
          ∑ N : {N : Subgroup U // N.Normal},
            (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) := hsurvive
      _ ≤ completeQuotientWeight (R := U ⧸ D.E) J *
            D.chart.outerFactor (Real.logb 2 (Nat.card J)) := by
        simpa only [U, completeQuotientWeight, completeQuotientCount,
          Nat.cast_sum] using houter
      _ ≤ completeQuotientWeight (R := U ⧸ D.E) J *
            (D.coefficient b * (2 : ℝ) ^ (D.eta * b)) :=
        mul_le_mul_of_nonneg_left hfactor hweight
      _ = (D.coefficient b * (2 : ℝ) ^ (D.eta * b)) *
            completeQuotientWeight (R := U ⧸ D.E) J +
          0 * (2 : ℝ) ^ (D.theta * b) := by ring

/-- Numerical package with the correlated semisimple sum paid once. -/
noncomputable def numericalData :
    PreE7CompleteSourceNumericalData family w i where
  certificate := D.certificate
  parameters := D.parameters
  main_total_bound := D.coefficient_bound
  tail_total_bound := fun _ => by positivity

end PreE7SemisimpleCompleteSourceData

/-- Direct semisimple data for cases where the quotient weight and the
simple-factor product have already been bounded together.  The comparator is
trivial, and the whole correlated bound is still paid only once. -/
structure PreE7SemisimpleDirectCompleteSourceData
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) where
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
  parameters : PreE7CharacterEntryParameters preE7CharacterRho w v eta
    delta cutoff alpha theta
  coefficient_bound : ∀ b,
    coefficient b ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  combined_bound : ∀ b (J : Subgroup (Equiv.Perm (Fin b))),
    completeQuotientWeight
        (R := preE7NonPairAction w i ⧸ E) J *
      chart.outerFactor (Real.logb 2 (Nat.card J)) ≤
        coefficient b * (2 : ℝ) ^ (eta * b)

attribute [instance] PreE7SemisimpleDirectCompleteSourceData.E_normal

namespace PreE7SemisimpleDirectCompleteSourceData

variable {family : PreE7NoPairNoC3EarlierOwnerFamily}
  {w : ℕ} {i : PreE7NonPairActionClass w}
  (D : PreE7SemisimpleDirectCompleteSourceData family w i)

noncomputable def certificate :
    PreE7CompleteSourceComparatorCertificate family w i where
  R := PUnit
  groupR := inferInstance
  finiteR := inferInstance
  v := D.v
  action := 1
  action_injective := fun _ _ _ => Subsingleton.elim _ _
  D := D.coefficient
  T := fun _ => 0
  eta := D.eta
  delta := D.delta
  cutoff := D.cutoff
  alpha := D.alpha
  theta := D.theta
  alpha_eq := D.alpha_eq
  D_nonneg := D.coefficient_nonneg
  T_nonneg := fun _ => le_rfl
  broad_source_envelope := by
    intro b J
    rw [completeQuotientWeight_eq_one_of_subsingleton (R := PUnit) J]
    let U := preE7NonPairAction w i
    have hsurvive :
        fusionCompleteSourceSum U
            (preE7NoPairNoC3BroadActionPredicate w i b) J ≤
          ∑ N : {N : Subgroup U // N.Normal},
            (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) := by
      unfold fusionCompleteSourceSum
      exact Finset.sum_le_sum (fun N _ =>
        fusionSurvivingEpiCount_le_groupEpimorphism_card U
          (preE7NoPairNoC3BroadActionPredicate w i b) N J)
    have houter := D.chart.outerSum_le (J := J)
    calc
      fusionCompleteSourceSum U
          (preE7NoPairNoC3BroadActionPredicate w i b) J ≤
          ∑ N : {N : Subgroup U // N.Normal},
            (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) := hsurvive
      _ ≤ completeQuotientWeight (R := U ⧸ D.E) J *
            D.chart.outerFactor (Real.logb 2 (Nat.card J)) := by
        simpa only [U, completeQuotientWeight, completeQuotientCount,
          Nat.cast_sum] using houter
      _ ≤ D.coefficient b * (2 : ℝ) ^ (D.eta * b) :=
        D.combined_bound b J
      _ = (D.coefficient b * (2 : ℝ) ^ (D.eta * b)) * 1 +
          0 * (2 : ℝ) ^ (D.theta * b) := by ring

noncomputable def numericalData :
    PreE7CompleteSourceNumericalData family w i where
  certificate := D.certificate
  parameters := D.parameters
  main_total_bound := D.coefficient_bound
  tail_total_bound := fun _ => by positivity

end PreE7SemisimpleDirectCompleteSourceData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
