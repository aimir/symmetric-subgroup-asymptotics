import SymmetricSubgroupAsymptotics.Non2PreE7NoPairNoC3EarlierComparators
import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailPhysical
import SymmetricSubgroupAsymptotics.GrowingQuotientAdditiveExceptional

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

/-- The genuinely exceptional B6 rank-tail scalar.  The cold source term is
installed separately in the ordinary cold row. -/
def preE7B6ExceptionalScalar {w : ℕ} {i : PreE7NonPairActionClass w}
    (C : PreE7B6RankTailCertificate w i) (b : ℕ) : ℝ :=
  growingQuotientNormalizedPointing b w
      (Nat.card (Subgroup.normalizer
        (preE7NonPairAction w i : Set (Equiv.Perm (Fin w)))) : ℝ) *
    (C.normalCount * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
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
  T := fun b => C.coldConstant * (1 + b)
  X := preE7B6ExceptionalScalar C
  v := 1
  eta := 0
  delta := preE7B6ExceptionalDelta
  cutoff := preE7B6ExceptionalCutoff
  alpha := preE7B6ExceptionalCutoff
  theta := 4 / 3
  alpha_eq := by simp
  D_nonneg := fun _ => le_rfl
  T_nonneg := fun b => mul_nonneg C.coldConstant_nonneg (by positivity)
  local_bound := by
    intro b P hP _hPbroad
    have h := C.physical_normalized_bound b P hP
    have hcold := growingQuotient_cold_identity (subgroupCount b : ℝ)
      b w (C.coldConstant * (1 + b))
      (Nat.card (Subgroup.normalizer
        (preE7NonPairAction w i : Set (Equiv.Perm (Fin w)))) : ℝ)
      (4 / 3) 0
    rw [show (4 / 3 : ℝ) + 0 = 4 / 3 by ring] at hcold
    simp only [growingQuotientThreshold, zero_mul, Real.rpow_zero,
      mul_one] at hcold
    have hhotzero : growingQuotientHotKernel
        (fun n => (subgroupCount n : ℝ)) b w 1 0
        (Nat.card (Subgroup.normalizer
          (preE7NonPairAction w i : Set (Equiv.Perm (Fin w)))) : ℝ)
        0 preE7B6ExceptionalDelta preE7B6ExceptionalCutoff = 0 := by
      simp [growingQuotientHotKernel]
    have hcoldzero : fusionWidthColdKernel b w 0
        (Nat.card (Subgroup.normalizer
          (preE7NonPairAction w i : Set (Equiv.Perm (Fin w)))) : ℝ)
        preE7B6ExceptionalCutoff = 0 := by
      simp [fusionWidthColdKernel]
    simp only [preE7B6ExceptionalScalar, hhotzero, hcoldzero, zero_add]
    rw [ordinarySubgroupRatio, ← hcold]
    calc
      _ ≤ growingQuotientNormalizedPointing b w
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w i : Set (Equiv.Perm (Fin w)))) : ℝ) *
          (C.coldConstant * (1 + b) *
                (2 : ℝ) ^ ((4 / 3 : ℝ) * b) *
                (subgroupCount b : ℝ) +
            C.normalCount * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
              ((2 : ℝ) ^
                  (-((b6RankTailExponent b : ℝ) * (13 / 50) * b)) *
                (subgroupCount
                  (b + 2 * b6RankTailExponent b) : ℝ))) := h
      _ = _ := by ring

/-- A local physical certificate together with the numerical decay of its
source-summed exceptional term.  The coarse subgroup estimate remains an
explicit published input. -/
structure PreE7EarlierLocalPackage
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  certificate : PreE7EarlierLocalCertificate family w i
  exceptional : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)) →
    ExponentialScalarBound certificate.X
  exceptional_support : certificate.X = 0 ∨ w ≤ 12288

/-- Every ordinary certificate has identically zero exceptional scalar. -/
noncomputable def PreE7EarlierLocalPackage.ofComparator
    {family : PreE7NoPairNoC3EarlierOwnerFamily}
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (C : PreE7EarlierActionComparatorCertificate family w i) :
    PreE7EarlierLocalPackage family w i where
  certificate := .ofComparator C
  exceptional := fun _ =>
    { threshold := 0
      rate := 1
      constant := 1
      rate_pos := by norm_num
      constant_pos := by norm_num
      bound := by simp [PreE7EarlierLocalCertificate.ofComparator] }
  exceptional_support := Or.inl rfl

/-- The action predicate used by the mixed catalogue.  It means that the
displayed original action carries a valid physical certificate and decay
certificate of the family named by the owner label. -/
def preE7NoPairNoC3EarlierLocalFamilyAction
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) : Prop :=
  Nonempty (PreE7EarlierLocalPackage family w i)

/-- Any ordinary action certificate is accepted by the mixed catalogue. -/
theorem preE7EarlierLocalFamilyAction_ofComparator
    {family : PreE7NoPairNoC3EarlierOwnerFamily}
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (C : PreE7EarlierActionComparatorCertificate family w i) :
    preE7NoPairNoC3EarlierLocalFamilyAction family w i :=
  ⟨.ofComparator C⟩

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
