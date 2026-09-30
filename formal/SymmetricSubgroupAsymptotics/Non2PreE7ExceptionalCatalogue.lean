import SymmetricSubgroupAsymptotics.Non2PreE7NoPairNoC3EarlierComparators
import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailPhysical

/-!
# Unified ordinary and source-summed pre-E7 owner certificates

The ordinary pre-`E7` catalogue records a pointwise complete-source
comparator on every normal axis.  The three binary-rank-tail families only
admit their useful estimate after summing over all complete sources.  They
therefore cannot honestly inhabit the old pointwise certificate type.

This file gives both conclusions one physical target.  An ordinary
certificate is summed over its literal normal axes and passed through the
usual hot/cold transfer.  A source-summed certificate puts that already
correlated physical estimate in the exceptional scalar.  The resulting
action predicate can be used by the existing certificate-retaining owner
cover without asserting a false pointwise envelope.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- A fully physical local certificate on one earlier-owner action.  The
first three terms are the ordinary comparator and additive-tail rows.  `X`
is reserved for estimates which are valid only after summing over complete
sources.  The conclusion is stable under restriction of the broad source,
which is exactly what the first-owner predicate requires. -/
structure PreE7EarlierLocalCertificate
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  D : ℕ → ℝ
  T : ℕ → ℝ
  X : ℕ → ℝ
  v : ℕ
  eta : ℝ
  delta : ℝ
  cutoff : ℝ
  alpha : ℝ
  theta : ℝ
  alpha_eq : alpha = eta + cutoff
  D_nonneg : ∀ b, 0 ≤ D b
  T_nonneg : ∀ b, 0 ≤ T b
  local_bound : ∀ (b : ℕ)
      (P : Subgroup
        (preE7NonPairAction w i × Equiv.Perm (Fin b)) → Prop),
    FusionOrbitNatural (preE7NonPairAction w i) P →
    (∀ H, P H → preE7NoPairNoC3BroadActionPredicate w i b H) →
    (Nat.card (FusionOrbitFamily (preE7NonPairAction w i)
        (FusionAcceptedOrbitPredicate (preE7NonPairAction w i) P)) : ℝ) /
        exactBenchmark (b + w) ≤
      (growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
          b w v (D b)
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w i : Set (Equiv.Perm (Fin w)))) : ℝ)
          eta delta cutoff +
        fusionWidthColdKernel b w (D b)
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w i : Set (Equiv.Perm (Fin w)))) : ℝ)
          alpha * ordinarySubgroupRatio b +
        fusionWidthColdKernel b w (T b)
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w i : Set (Equiv.Perm (Fin w)))) : ℝ)
          theta * ordinarySubgroupRatio b) + X b

namespace PreE7EarlierLocalCertificate

variable {family : PreE7NoPairNoC3EarlierOwnerFamily}
  {w : ℕ} {i : PreE7NonPairActionClass w}

/-- Every honest pointwise comparator certificate gives a unified local
certificate with zero exceptional scalar. -/
noncomputable def ofComparator
    (C : PreE7EarlierActionComparatorCertificate family w i) :
    PreE7EarlierLocalCertificate family w i where
  D := fun b =>
    fusionAxisEnvelopeTotal (preE7NonPairAction w i) (C.C b)
  T := fun b =>
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
      (C.tailCoefficient b)
  X := fun _ => 0
  v := C.v
  eta := C.eta
  delta := C.delta
  cutoff := C.cutoff
  alpha := C.alpha
  theta := C.theta
  alpha_eq := C.alpha_eq
  D_nonneg := fun b =>
    fusionAxisEnvelopeTotal_nonneg _ _ (C.coefficient_nonneg b)
  T_nonneg := fun b =>
    fusionAxisEnvelopeTotal_nonneg _ _ (C.tail_nonneg b)
  local_bound := by
    intro b P hP hPbroad
    let D : ℝ := fusionAxisEnvelopeTotal
      (preE7NonPairAction w i) (C.C b)
    let T : ℝ := fusionAxisEnvelopeTotal
      (preE7NonPairAction w i) (C.tailCoefficient b)
    have hsource (J : Subgroup (Equiv.Perm (Fin b))) :
        fusionCompleteSourceSum (preE7NonPairAction w i) P J ≤
          (D * (2 : ℝ) ^ (C.eta * b)) *
              completeQuotientWeight (R := C.R) J +
            T * (2 : ℝ) ^ (C.theta * b) := by
      unfold fusionCompleteSourceSum D T fusionAxisEnvelopeTotal
      calc
        _ ≤ ∑ N,
            ((C.C b N * (2 : ℝ) ^ (C.eta * b)) *
                completeQuotientWeight (R := C.R) J +
              C.tailCoefficient b N * (2 : ℝ) ^ (C.theta * b)) :=
          Finset.sum_le_sum (fun N _ =>
            (fusionSurvivingEpiCount_mono hPbroad N J).trans
              (C.broad_axis_envelope b N J))
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_mul]
    have h := fusionPhysical_growingQuotient_additiveTail_kernel_bound
      (preE7NonPairAction w i) P hP C.action C.action_injective
      D T C.eta C.theta C.delta C.cutoff
      (fusionAxisEnvelopeTotal_nonneg _ _ (C.coefficient_nonneg b))
      (fusionAxisEnvelopeTotal_nonneg _ _ (C.tail_nonneg b)) hsource
    simpa only [D, T, C.alpha_eq, add_zero] using h

end PreE7EarlierLocalCertificate

/-! ## The B6 source-summed instance -/

/-- The harmless comparator parameters attached to a B6 exceptional cell.
The ordinary coefficients are zero, so these parameters only keep the global
parameter record uniform.  They are chosen to satisfy the global
`rho = 1/8192` window at the forced width `w = 12`. -/
def preE7B6ExceptionalDelta : ℝ := preE7CharacterRho * 12 / 2

def preE7B6ExceptionalCutoff : ℝ :=
  (1 : ℝ) / 8 + preE7B6ExceptionalDelta / 2

/-- The already source-summed B6 physical right-hand side. -/
def preE7B6ExceptionalScalar {w : ℕ} {i : PreE7NonPairActionClass w}
    (C : PreE7B6RankTailCertificate w i) (b : ℕ) : ℝ :=
  growingQuotientNormalizedPointing b w
      (Nat.card (Subgroup.normalizer
        (preE7NonPairAction w i : Set (Equiv.Perm (Fin w)))) : ℝ) *
    (C.coldConstant * (1 + b) *
          (2 : ℝ) ^ ((4 / 3 : ℝ) * b) * (subgroupCount b : ℝ) +
      C.normalCount * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
        ((2 : ℝ) ^
            (-((b6RankTailExponent b : ℝ) * (13 / 50) * b)) *
          (subgroupCount
            (b + 2 * b6RankTailExponent b) : ℝ)))

/-- B6 inhabits the unified catalogue through its correlated source sum,
with both ordinary coefficients set to zero. -/
noncomputable def PreE7EarlierLocalCertificate.ofB6
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (C : PreE7B6RankTailCertificate w i) :
    PreE7EarlierLocalCertificate .b6 w i where
  D := fun _ => 0
  T := fun _ => 0
  X := preE7B6ExceptionalScalar C
  v := 1
  eta := 0
  delta := preE7B6ExceptionalDelta
  cutoff := preE7B6ExceptionalCutoff
  alpha := preE7B6ExceptionalCutoff
  theta := 0
  alpha_eq := by simp
  D_nonneg := fun _ => le_rfl
  T_nonneg := fun _ => le_rfl
  local_bound := by
    intro b P hP _hPbroad
    have h := C.physical_normalized_bound b P hP
    simpa only [preE7B6ExceptionalScalar, growingQuotientHotKernel,
      fusionWidthColdKernel, zero_div, mul_zero, zero_mul, add_zero,
      zero_add] using h

/-- The action predicate used by the mixed catalogue.  It means that the
displayed original action carries a valid physical certificate of the family
named by the owner label. -/
def preE7NoPairNoC3EarlierLocalFamilyAction
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) : Prop :=
  Nonempty (PreE7EarlierLocalCertificate family w i)

/-- Any ordinary action certificate is accepted by the mixed catalogue. -/
theorem preE7EarlierLocalFamilyAction_ofComparator
    {family : PreE7NoPairNoC3EarlierOwnerFamily}
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (C : PreE7EarlierActionComparatorCertificate family w i) :
    preE7NoPairNoC3EarlierLocalFamilyAction family w i :=
  ⟨.ofComparator C⟩

/-- Any B6 rank-tail certificate is accepted by the mixed catalogue without
being coerced to a pointwise complete-source estimate. -/
theorem preE7EarlierLocalFamilyAction_ofB6
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (C : PreE7B6RankTailCertificate w i) :
    preE7NoPairNoC3EarlierLocalFamilyAction .b6 w i :=
  ⟨.ofB6 C⟩

/-- The mixed certified first-owner predicate still restricts to the broad
source.  This proof uses only the structural part of the first-owner
predicate and is independent of which local estimate certified the action. -/
theorem preE7NoPairNoC3LocalCertifiedFirstOwnerPredicate_implies_broad
    (w : ℕ)
    (j : PreE7NonPairFirstOwnerIndex
      (preE7NoPairNoC3EarlierOwnerCount + 1) w)
    (b : ℕ)
    (H : Subgroup
      (preE7NonPairFirstOwnerAction w j × Equiv.Perm (Fin b))) :
    preE7NoPairNoC3CertifiedFirstOwnerPredicate
        preE7NoPairNoC3EarlierLocalFamilyAction w j b H →
      preE7NoPairNoC3BroadActionPredicate w j.2 b H := by
  rintro ⟨⟨⟨hordinary, _howner⟩, hnoC3⟩, _hselected⟩
  exact ⟨hordinary, hnoC3⟩

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
