import SymmetricSubgroupAsymptotics.Non2PreE7ExceptionalCatalogue
import SymmetricSubgroupAsymptotics.Non2PreE7NoPairNoC3ExceptionalInterface
import SymmetricSubgroupAsymptotics.GrowingQuotientExceptionalAggregation
import SymmetricSubgroupAsymptotics.Non2PreE7EmptyCellNumerics

/-!
# Assemble the mixed pre-E7 owner catalogue

This file installs unified ordinary/source-summed certificates in the
certificate-retaining first-owner cover.  A matching earlier action uses its
physical certificate.  A nonmatching owner/action pair is an empty family.
Only the final residual owner is delegated to the retained joint-cell lane.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- One exact local row on a cell of the mixed certified cover. -/
structure PreE7NoPairNoC3LocalExceptionalChoice
    (w : ℕ)
    (j : PreE7NonPairFirstOwnerIndex
      (preE7NoPairNoC3EarlierOwnerCount + 1) w) where
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
  exceptional : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)) →
    ExponentialScalarBound X
  exceptional_support : X = 0 ∨ w ≤ 12288
  local_bound : ∀ b,
    (Nat.card (FusionOrbitFamily
        (preE7NonPairFirstOwnerAction w j)
        (FusionAcceptedOrbitPredicate
          (preE7NonPairFirstOwnerAction w j)
          (preE7NoPairNoC3CertifiedFirstOwnerPredicate
            preE7NoPairNoC3EarlierLocalFamilyAction w j b))) : ℝ) /
        exactBenchmark (b + w) ≤
      (growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
          b w v (D b)
          (Nat.card (Subgroup.normalizer
            (preE7NonPairFirstOwnerAction w j :
              Set (Equiv.Perm (Fin w)))) : ℝ)
          eta delta cutoff +
        fusionWidthColdKernel b w (D b)
          (Nat.card (Subgroup.normalizer
            (preE7NonPairFirstOwnerAction w j :
              Set (Equiv.Perm (Fin w)))) : ℝ)
          alpha * ordinarySubgroupRatio b +
        fusionWidthColdKernel b w (T b)
          (Nat.card (Subgroup.normalizer
            (preE7NonPairFirstOwnerAction w j :
              Set (Equiv.Perm (Fin w)))) : ℝ)
          theta * ordinarySubgroupRatio b) + X b

namespace PreE7NoPairNoC3LocalExceptionalChoice

/-- Install a matching earlier-owner certificate on the exact local
first-owner predicate. -/
noncomputable def ofEarlierCertificate
    (k : Fin preE7NoPairNoC3EarlierOwnerCount)
    {w : ℕ} (U : PreE7NonPairActionClass w)
    (C : PreE7EarlierLocalPackage
      (preE7NoPairNoC3EarlierOwnerEquiv k) w U) :
    PreE7NoPairNoC3LocalExceptionalChoice w (k.castSucc, U) where
  D := C.certificate.D
  T := C.certificate.T
  X := C.certificate.X
  v := C.certificate.v
  eta := C.certificate.eta
  delta := C.certificate.delta
  cutoff := C.certificate.cutoff
  alpha := C.certificate.alpha
  theta := C.certificate.theta
  alpha_eq := C.certificate.alpha_eq
  D_nonneg := C.certificate.D_nonneg
  T_nonneg := C.certificate.T_nonneg
  exceptional := C.exceptional
  exceptional_support := C.exceptional_support
  local_bound := fun b => C.certificate.local_bound b _
    (preE7NoPairNoC3CertifiedFirstOwnerPredicate_natural _ w
      (k.castSucc, U) b)
    (preE7NoPairNoC3LocalCertifiedFirstOwnerPredicate_implies_broad
      w (k.castSucc, U) b)

/-- A nonmatching earlier owner/action cell is empty because the selected
action eligibility is a conjunct of the local predicate. -/
noncomputable def emptyEarlier
    (k : Fin preE7NoPairNoC3EarlierOwnerCount)
    {w : ℕ} (U : PreE7NonPairActionClass w)
    (hmissing : ¬ preE7NoPairNoC3EarlierLocalFamilyAction
      (preE7NoPairNoC3EarlierOwnerEquiv k) w U) :
    PreE7NoPairNoC3LocalExceptionalChoice w (k.castSucc, U) where
  D := fun _ => 0
  T := fun _ => 0
  X := fun _ => 0
  v := preE7EmptyCellDegree w
  eta := 0
  delta := preE7EmptyCellDelta w
  cutoff := preE7EmptyCellCutoff w
  alpha := preE7EmptyCellAlpha w
  theta := 0
  alpha_eq := by
    simp [preE7EmptyCellAlpha]
  D_nonneg := fun _ => le_rfl
  T_nonneg := fun _ => le_rfl
  exceptional := fun _ =>
    { threshold := 0
      rate := 1
      constant := 1
      rate_pos := by norm_num
      constant_pos := by norm_num
      bound := by simp }
  exceptional_support := Or.inl rfl
  local_bound := by
    intro b
    let U' := preE7NonPairFirstOwnerAction w (k.castSucc, U)
    let P := preE7NoPairNoC3CertifiedFirstOwnerPredicate
      preE7NoPairNoC3EarlierLocalFamilyAction w (k.castSucc, U) b
    haveI : IsEmpty (FusionOrbitFamily U'
        (FusionAcceptedOrbitPredicate U' P)) := by
      refine ⟨fun K => ?_⟩
      obtain ⟨_, ⟨⟨s, ⟨M, hM⟩⟩, rfl⟩⟩ := K
      obtain ⟨⟨H, hH⟩, rfl⟩ := hM
      exact hmissing
        ((preE7NoPairNoC3SelectedActionEligible_castSucc
          preE7NoPairNoC3EarlierLocalFamilyAction k U).mp hH.2.2)
    have hcard : Nat.card (FusionOrbitFamily U'
        (FusionAcceptedOrbitPredicate U' P)) = 0 := Nat.card_of_isEmpty
    change (Nat.card (FusionOrbitFamily U'
        (FusionAcceptedOrbitPredicate U' P)) : ℝ) /
          exactBenchmark (b + w) ≤ _
    rw [hcard]
    simp [growingQuotientHotKernel, fusionWidthColdKernel]

end PreE7NoPairNoC3LocalExceptionalChoice

/-- Select the actual earlier certificate, the empty row for a nonmatching
action, or the separately supplied terminal residual row. -/
noncomputable def preE7NoPairNoC3LocalExceptionalChoice
    (Residual : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NoPairNoC3LocalExceptionalChoice w
        (Fin.last preE7NoPairNoC3EarlierOwnerCount, U))
    (w : ℕ)
    (owner : Fin (preE7NoPairNoC3EarlierOwnerCount + 1))
    (U : PreE7NonPairActionClass w) :
    PreE7NoPairNoC3LocalExceptionalChoice w (owner, U) := by
  classical
  by_cases ho : owner.val < preE7NoPairNoC3EarlierOwnerCount
  · let k : Fin preE7NoPairNoC3EarlierOwnerCount := ⟨owner.val, ho⟩
    have howner : owner = k.castSucc := by
      apply Fin.ext
      rfl
    by_cases hC : preE7NoPairNoC3EarlierLocalFamilyAction
        (preE7NoPairNoC3EarlierOwnerEquiv k) w U
    · simpa only [howner] using
        (PreE7NoPairNoC3LocalExceptionalChoice.ofEarlierCertificate
          k U (Classical.choice hC))
    · simpa only [howner] using
        (PreE7NoPairNoC3LocalExceptionalChoice.emptyEarlier k U hC)
  · have howner : owner = Fin.last preE7NoPairNoC3EarlierOwnerCount :=
      Fin.eq_last_of_not_lt ho
    simpa only [howner] using Residual w U

/-- Assemble the mixed earlier-owner catalogue and terminal residual choices
into the abstract exceptional interface consumed by `T1`. -/
noncomputable def preE7NoPairNoC3_localExceptionalData_of_residual
    (Residual : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NoPairNoC3LocalExceptionalChoice w
        (Fin.last preE7NoPairNoC3EarlierOwnerCount, U)) :
    PreE7NoPairNoC3LocalExceptionalData
      preE7NoPairNoC3EarlierOwnerCount where
  P := preE7NoPairNoC3CertifiedFirstOwnerPredicate
    preE7NoPairNoC3EarlierLocalFamilyAction
  P_natural := preE7NoPairNoC3CertifiedFirstOwnerPredicate_natural _
  physical_cover :=
    preE7NoPairNoC3_certifiedOwnerOrResidual_physical_cover _
  D := fun w j =>
    (preE7NoPairNoC3LocalExceptionalChoice Residual w j.1 j.2).D
  T := fun w j =>
    (preE7NoPairNoC3LocalExceptionalChoice Residual w j.1 j.2).T
  X := fun w j =>
    (preE7NoPairNoC3LocalExceptionalChoice Residual w j.1 j.2).X
  A := fun w j => Nat.card (Subgroup.normalizer
    (preE7NonPairFirstOwnerAction w j : Set (Equiv.Perm (Fin w))))
  v := fun w j =>
    (preE7NoPairNoC3LocalExceptionalChoice Residual w j.1 j.2).v
  eta := fun w j =>
    (preE7NoPairNoC3LocalExceptionalChoice Residual w j.1 j.2).eta
  delta := fun w j =>
    (preE7NoPairNoC3LocalExceptionalChoice Residual w j.1 j.2).delta
  cutoff := fun w j =>
    (preE7NoPairNoC3LocalExceptionalChoice Residual w j.1 j.2).cutoff
  alpha := fun w j =>
    (preE7NoPairNoC3LocalExceptionalChoice Residual w j.1 j.2).alpha
  theta := fun w j =>
    (preE7NoPairNoC3LocalExceptionalChoice Residual w j.1 j.2).theta
  D_nonneg := fun w j =>
    (preE7NoPairNoC3LocalExceptionalChoice Residual w j.1 j.2).D_nonneg
  T_nonneg := fun w j =>
    (preE7NoPairNoC3LocalExceptionalChoice Residual w j.1 j.2).T_nonneg
  A_eq := fun _ _ => rfl
  local_bound := by
    intro n j
    let w : ℕ := j.1.1
    let C := preE7NoPairNoC3LocalExceptionalChoice Residual w j.2.1 j.2.2
    have hwn : w ≤ n := growingQuotientPhysicalWidth_le j
    have h := C.local_bound (n - w)
    rw [GrowingQuotientCanonicalFamily, fusionWidthCanonicalFamily_card]
    simpa only [w, C, Nat.sub_add_cancel hwn] using h

/-- The complete exceptional menu is exponentially small.  This conclusion
uses the explicit width support stored in every local package; it does not
turn a collection of unrelated, unbounded-width cell estimates into a
spurious uniform bound. -/
noncomputable def
    preE7NoPairNoC3_localExceptionalData_exceptionalTotal
    (Residual : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NoPairNoC3LocalExceptionalChoice w
        (Fin.last preE7NoPairNoC3EarlierOwnerCount, U))
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    ExponentialScalarBound
      (growingQuotientExceptionalTotal 3
        (preE7NoPairNoC3_localExceptionalData_of_residual Residual).X) := by
  apply exponentialScalarBound_growingQuotientExceptionalTotal 3 12288
  · intro w j
    exact (preE7NoPairNoC3LocalExceptionalChoice
      Residual w j.1 j.2).exceptional hcoarse
  · intro w j hw
    change (preE7NoPairNoC3LocalExceptionalChoice
      Residual w j.1 j.2).X = 0
    rcases (preE7NoPairNoC3LocalExceptionalChoice
      Residual w j.1 j.2).exceptional_support with hzero | hwidth
    · exact hzero
    · omega

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
