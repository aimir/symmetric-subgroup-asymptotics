import SymmetricSubgroupAsymptotics.Non2PreE7Y1RankTailPhysical
import SymmetricSubgroupAsymptotics.Non2PreE7RankTailSourceDichotomyClosure

/-!
# A raw summed source for the exceptional binary pair actions

The small binary-affine cells are sometimes controlled only after the
complete source has been split by a binary-rank test.  This file records the
result before physical pointing.  In particular it is the interface used by
the degree-three affine lane: a ternary elementary layer can be prepended to
the literal signed quotient while its pair-action source is still visible.

No action classification is present here.  A constructor must prove the
displayed complete-source sum on the literal original action.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The pre-padding finite-group form of a correlated pair estimate.  This
is intentionally stated for an arbitrary literal finite group `Q`, rather
than an action class.  It is the object required when `Q` is the actual
signed quotient of a ternary affine component and a new elementary layer is
to be prepended before physical pointing. -/
structure PreE7DegreeTwoPairQuotientSummedEnvelope
    (Q : Type) [Group Q] [Finite Q] : Type 1 where
  R : Type
  [groupR : Group R]
  [finiteR : Finite R]
  mainCoefficient : ℝ
  coldCoefficient : ℕ → ℝ
  eta : ℝ
  theta : ℝ
  mainCoefficient_nonneg : 0 ≤ mainCoefficient
  coldCoefficient_nonneg : ∀ b, 0 ≤ coldCoefficient b
  exceptionalRaw : ℕ → ℝ
  exceptionalRaw_nonneg : ∀ b, 0 ≤ exceptionalRaw b
  summed : ∀ b : ℕ,
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        completeQuotientWeight (R := Q) J) ≤
      ((∑ J : Subgroup (Equiv.Perm (Fin b)),
          ((mainCoefficient * (2 : ℝ) ^ (eta * b)) *
                completeQuotientWeight (R := R) J +
              coldCoefficient b * (2 : ℝ) ^ (theta * b))) +
          exceptionalRaw b)

attribute [instance]
  PreE7DegreeTwoPairQuotientSummedEnvelope.groupR
  PreE7DegreeTwoPairQuotientSummedEnvelope.finiteR

/-- A complete-source estimate before physical pointing.  The main term is
one complete quotient moment of `R`, the cold term is source independent,
and `exceptionalRaw` is already summed over the correlated hot sources. -/
structure PreE7DegreeTwoPairSummedSource
    (w : ℕ) (U : PreE7NonPairActionClass w) : Type 1 where
  R : Type
  [groupR : Group R]
  [finiteR : Finite R]
  v : ℕ
  action : R →* Equiv.Perm (Fin v)
  action_injective : Function.Injective action
  mainCoefficient : ℝ
  coldCoefficient : ℕ → ℝ
  eta : ℝ
  theta : ℝ
  mainCoefficient_nonneg : 0 ≤ mainCoefficient
  coldCoefficient_nonneg : ∀ b, 0 ≤ coldCoefficient b
  exceptionalRaw : ℕ → ℝ
  exceptionalRaw_nonneg : ∀ b, 0 ≤ exceptionalRaw b
  summed : ∀ (b : ℕ)
      (P : Subgroup (preE7NonPairAction w U × Equiv.Perm (Fin b)) → Prop),
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        fusionCompleteSourceSum (preE7NonPairAction w U) P J) ≤
      ((∑ J : Subgroup (Equiv.Perm (Fin b)),
          ((mainCoefficient * (2 : ℝ) ^ (eta * b)) *
                completeQuotientWeight (R := R) J +
              coldCoefficient b * (2 : ℝ) ^ (theta * b))) +
          exceptionalRaw b)

attribute [instance]
  PreE7DegreeTwoPairSummedSource.groupR
  PreE7DegreeTwoPairSummedSource.finiteR

namespace PreE7DegreeTwoPairSummedSource

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  (S : PreE7DegreeTwoPairSummedSource w U)

/-- The raw package gives the exact physical row, with the hot-source term
charged once after the sum over complete sources. -/
theorem physical_normalized_bound
    (b : ℕ)
    (P : Subgroup
      (preE7NonPairAction w U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural (preE7NonPairAction w U) P)
    (delta cutoff : ℝ) :
    (Nat.card (FusionOrbitFamily (preE7NonPairAction w U)
        (FusionAcceptedOrbitPredicate (preE7NonPairAction w U) P)) : ℝ) /
        exactBenchmark (b + w) ≤
      growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
          b w S.v S.mainCoefficient
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) : ℝ)
          S.eta delta cutoff +
        fusionWidthColdKernel b w S.mainCoefficient
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) : ℝ)
          (S.eta + cutoff) * ordinarySubgroupRatio b +
        fusionWidthColdKernel b w (S.coldCoefficient b)
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) : ℝ)
          S.theta * ordinarySubgroupRatio b +
        growingQuotientNormalizedPointing b w
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) : ℝ) *
          S.exceptionalRaw b := by
  have h :=
    fusionPhysical_growingQuotient_additiveTail_summedExceptional_kernel_bound
      (preE7NonPairAction w U) P hP S.action S.action_injective
      S.mainCoefficient (S.coldCoefficient b) S.eta S.theta delta cutoff
      (S.exceptionalRaw b) S.mainCoefficient_nonneg (S.summed b P)
  simpa only [ordinarySubgroupRatio] using h

/-- The normalized exceptional scalar attached to the raw source. -/
def exceptionalScalar (b : ℕ) : ℝ :=
  growingQuotientNormalizedPointing b w
      (Nat.card (Subgroup.normalizer
        (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) : ℝ) *
    S.exceptionalRaw b

/-- Numerical data which turns a raw pair source into the terminal row.  It
is deliberately separate from the source itself: the same raw package can
be prepended by the degree-three lane before these physical parameters are
chosen. -/
structure NumericalMargin : Type where
  D : ℕ → ℝ
  combinedEta : ℝ
  delta : ℝ
  cutoff : ℝ
  alpha : ℝ
  alpha_eq : alpha = combinedEta + cutoff
  D_nonneg : ∀ b, 0 ≤ D b
  width_upper : w ≤ 12288
  parameters : PreE7CharacterEntryParameters preE7CharacterRho w S.v combinedEta
    delta cutoff alpha 0
  total_growth : ∀ b,
    D b ≤ (2 : ℝ) ^
      (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  combined_summed : ∀ (b : ℕ)
      (P : Subgroup (preE7NonPairAction w U × Equiv.Perm (Fin b)) → Prop),
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        fusionCompleteSourceSum (preE7NonPairAction w U) P J) ≤
      ((∑ J : Subgroup (Equiv.Perm (Fin b)),
          ((D b * (2 : ℝ) ^ (combinedEta * b)) *
              completeQuotientWeight (R := S.R) J +
            0 * (2 : ℝ) ^ ((0 : ℝ) * b))) + S.exceptionalRaw b)
  exceptional : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)) →
    ExponentialScalarBound S.exceptionalScalar

/-- Numerical data retaining the source-independent cold term as the
additive continuation row.  The extra domination `T ≤ D` lets the global
terminal menu reuse the already proved main menu-mass bound without changing
the mathematical slopes of either term. -/
structure AdditiveNumericalMargin : Type where
  D : ℕ → ℝ
  T : ℕ → ℝ
  eta : ℝ
  theta : ℝ
  delta : ℝ
  cutoff : ℝ
  alpha : ℝ
  alpha_eq : alpha = eta + cutoff
  D_nonneg : ∀ b, 0 ≤ D b
  T_nonneg : ∀ b, 0 ≤ T b
  T_le_D : ∀ b, T b ≤ D b
  width_upper : w ≤ 12288
  parameters : PreE7CharacterEntryParameters preE7CharacterRho w S.v eta
    delta cutoff alpha theta
  total_growth : ∀ b,
    D b ≤ (2 : ℝ) ^
      (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  summed : ∀ (b : ℕ)
      (P : Subgroup (preE7NonPairAction w U × Equiv.Perm (Fin b)) → Prop),
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        fusionCompleteSourceSum (preE7NonPairAction w U) P J) ≤
      ((∑ J : Subgroup (Equiv.Perm (Fin b)),
          ((D b * (2 : ℝ) ^ (eta * b)) *
              completeQuotientWeight (R := S.R) J +
            T b * (2 : ℝ) ^ (theta * b))) + S.exceptionalRaw b)
  exceptional : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)) →
    ExponentialScalarBound S.exceptionalScalar

/-- Install an additive raw source without merging its two slopes. -/
noncomputable def toResidualChoiceAdditive
    (M : S.AdditiveNumericalMargin) :
    PreE7NumericalRankTailResidualChoice w U where
  D := M.D
  T := M.T
  v := S.v
  eta := M.eta
  delta := M.delta
  cutoff := M.cutoff
  alpha := M.alpha
  theta := M.theta
  X := S.exceptionalScalar
  alpha_eq := M.alpha_eq
  D_nonneg := M.D_nonneg
  T_nonneg := M.T_nonneg
  T_le_D := M.T_le_D
  parameters := M.parameters
  main_total_growth := .inl M.total_growth
  exceptional := M.exceptional
  exceptional_support := Or.inr M.width_upper
  local_bound := by
    intro b
    let P := preE7NoPairNoC3CertifiedFirstOwnerPredicate
      preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
      (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b
    have h :=
      fusionPhysical_growingQuotient_additiveTail_summedExceptional_kernel_bound
        (preE7NonPairAction w U) P
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate_natural _ w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b)
        S.action S.action_injective (M.D b) (M.T b) M.eta M.theta
        M.delta M.cutoff (S.exceptionalRaw b) (M.D_nonneg b)
        (M.summed b P)
    simpa [P, M.alpha_eq, exceptionalScalar,
      ordinarySubgroupRatio] using h

/-- Install the raw summed source as a concrete pre-`E7` residual row. -/
noncomputable def toResidualChoice
    (M : S.NumericalMargin) :
    PreE7NumericalRankTailResidualChoice w U where
  D := M.D
  T := fun _ => 0
  v := S.v
  eta := M.combinedEta
  delta := M.delta
  cutoff := M.cutoff
  alpha := M.alpha
  theta := 0
  X := S.exceptionalScalar
  alpha_eq := M.alpha_eq
  D_nonneg := M.D_nonneg
  T_nonneg := fun _ => le_rfl
  T_le_D := fun b => M.D_nonneg b
  parameters := M.parameters
  main_total_growth := .inl M.total_growth
  exceptional := M.exceptional
  exceptional_support := Or.inr (by
    exact M.width_upper)
  local_bound := by
    intro b
    let P := preE7NoPairNoC3CertifiedFirstOwnerPredicate
      preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
      (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b
    have h :=
      fusionPhysical_growingQuotient_additiveTail_summedExceptional_kernel_bound
        (preE7NonPairAction w U) P
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate_natural _ w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b)
        S.action S.action_injective (M.D b) 0 M.combinedEta 0
        M.delta M.cutoff (S.exceptionalRaw b) (M.D_nonneg b)
        (M.combined_summed b P)
    simpa [P, M.alpha_eq, exceptionalScalar,
      fusionWidthColdKernel, ordinarySubgroupRatio] using h

end PreE7DegreeTwoPairSummedSource

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
