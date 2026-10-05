import SymmetricSubgroupAsymptotics.Non2PreE7NumericalEarlierPackage
import SymmetricSubgroupAsymptotics.FusionCarrierWeightedIncidence
import SymmetricSubgroupAsymptotics.FusionCarrierYonedaTopFamily

/-!
# Numerical residual joint-top data

This module isolates the retained-cell and Yoneda-family interfaces used by
the final SNS2/rank-tail route.  They do not depend on the superseded
pointwise numerical exceptional catalogue or its older T1 closure.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

attribute [local instance] Fintype.ofFinite

/-- Joint top/Yoneda terminal data for the numerically certified catalogue. -/
structure PreE7NumericalResidualJointTopCellSourceData
    (w : ℕ) (U : PreE7NonPairActionClass w) where
  R : Type
  [groupR : Group R]
  [finiteR : Finite R]
  v : ℕ
  action : R →* Equiv.Perm (Fin v)
  action_injective : Function.Injective action
  C : ℕ → {N : Subgroup (preE7NonPairAction w U) // N.Normal} → ℝ
  eta : ℝ
  delta : ℝ
  cutoff : ℝ
  alpha : ℝ
  theta : ℝ
  alpha_eq : alpha = eta + cutoff
  coefficient_nonneg : ∀ b N, 0 ≤ C b N
  parameters : PreE7CharacterEntryParameters preE7CharacterRho w v eta
    delta cutoff alpha theta
  coefficient_total_bound : ∀ b,
    fusionAxisEnvelopeTotal (preE7NonPairAction w U) (C b) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  carrier : ∀ _b N, FusionAxisCarrier (preE7NonPairAction w U) N
  Accepted : ∀ b N,
    Subgroup ((carrier b N).checked.carrier × Equiv.Perm (Fin b)) → Prop
  accept_inverse : ∀ b N (J : Subgroup (Equiv.Perm (Fin b)))
      (γ : GroupEpimorphism J (carrier b N).checked.quotient),
    (carrier b N).checked.carrierInverseSurvival
        (carrier b N).source_eq
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate
          preE7NoPairNoC3EarlierNumericalFamilyAction w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b)
        (fusionQuotientGraph (carrier b N).checked.beta J γ.1) →
      Accepted b N
        (fusionQuotientGraph (carrier b N).checked.beta J γ.1)
  Cell : ∀ b
      (_N : {N : Subgroup (preE7NonPairAction w U) // N.Normal})
      (_J : Subgroup (Equiv.Perm (Fin b))), Type
  [cell_finite : ∀ b N J, Finite (Cell b N J)]
  cell : ∀ b N (J : Subgroup (Equiv.Perm (Fin b))),
    FusionCarrierAcceptedEpi (carrier b N).checked J (Accepted b N) →
      CompleteQuotientMap J R × Cell b N J
  fibreCost : ∀ b N (J : Subgroup (Equiv.Perm (Fin b))), Cell b N J → ℕ
  fibre_card : ∀ b N (J : Subgroup (Equiv.Perm (Fin b)))
      (d : CompleteQuotientMap J R) (a : Cell b N J),
    Nat.card {γ : FusionCarrierAcceptedEpi
        (carrier b N).checked J (Accepted b N) //
      cell b N J γ = (d, a)} ≤ fibreCost b N J a
  joint_capacity : ∀ b N (J : Subgroup (Equiv.Perm (Fin b))),
    (((∑ a : Cell b N J, fibreCost b N J a : ℕ)) : ℝ) ≤
      C b N * (2 : ℝ) ^ (eta * b)

attribute [instance]
  PreE7NumericalResidualJointTopCellSourceData.groupR
  PreE7NumericalResidualJointTopCellSourceData.finiteR
  PreE7NumericalResidualJointTopCellSourceData.cell_finite

/-- Concrete terminal input in which every accepted epimorphism selects one
member of a finite family of actual annihilator-aware Yoneda towers. -/
structure PreE7NumericalResidualYonedaTopFamilySourceData
    (w : ℕ) (U : PreE7NonPairActionClass w) where
  R : Type
  [groupR : Group R]
  [finiteR : Finite R]
  v : ℕ
  action : R →* Equiv.Perm (Fin v)
  action_injective : Function.Injective action
  C : ℕ → {N : Subgroup (preE7NonPairAction w U) // N.Normal} → ℝ
  eta : ℝ
  delta : ℝ
  cutoff : ℝ
  alpha : ℝ
  theta : ℝ
  alpha_eq : alpha = eta + cutoff
  coefficient_nonneg : ∀ b N, 0 ≤ C b N
  parameters : PreE7CharacterEntryParameters preE7CharacterRho w v eta
    delta cutoff alpha theta
  coefficient_total_bound : ∀ b,
    fusionAxisEnvelopeTotal (preE7NonPairAction w U) (C b) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  carrier : ∀ _b N, FusionAxisCarrier (preE7NonPairAction w U) N
  Accepted : ∀ b N,
    Subgroup ((carrier b N).checked.carrier × Equiv.Perm (Fin b)) → Prop
  accept_inverse : ∀ b N (J : Subgroup (Equiv.Perm (Fin b)))
      (γ : GroupEpimorphism J (carrier b N).checked.quotient),
    (carrier b N).checked.carrierInverseSurvival
        (carrier b N).source_eq
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate
          preE7NoPairNoC3EarlierNumericalFamilyAction w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b)
        (fusionQuotientGraph (carrier b N).checked.beta J γ.1) →
      Accepted b N
        (fusionQuotientGraph (carrier b N).checked.beta J γ.1)
  family : ∀ b N, AxisYonedaTopFamily (carrier b N) R
  select : ∀ b N (J : Subgroup (Equiv.Perm (Fin b))),
    FusionCarrierAcceptedEpi (carrier b N).checked J (Accepted b N) →
      (family b N).Index
  joint_capacity : ∀ b N (J : Subgroup (Equiv.Perm (Fin b))),
    (((∑ s : (family b N).Index,
      ((family b N).tower s).tower.capacity J : ℕ)) : ℝ) ≤
        C b N * (2 : ℝ) ^ (eta * b)

attribute [instance]
  PreE7NumericalResidualYonedaTopFamilySourceData.groupR
  PreE7NumericalResidualYonedaTopFamilySourceData.finiteR

/-- A finite selected family of actual Yoneda towers produces the weighted
joint cells consumed by the numerical T1 theorem. -/
noncomputable def
    PreE7NumericalResidualYonedaTopFamilySourceData.toJointTopCellSourceData
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (D : PreE7NumericalResidualYonedaTopFamilySourceData w U) :
    PreE7NumericalResidualJointTopCellSourceData w U where
  R := D.R
  groupR := D.groupR
  finiteR := D.finiteR
  v := D.v
  action := D.action
  action_injective := D.action_injective
  C := D.C
  eta := D.eta
  delta := D.delta
  cutoff := D.cutoff
  alpha := D.alpha
  theta := D.theta
  alpha_eq := D.alpha_eq
  coefficient_nonneg := D.coefficient_nonneg
  parameters := D.parameters
  coefficient_total_bound := D.coefficient_total_bound
  carrier := D.carrier
  Accepted := D.Accepted
  accept_inverse := D.accept_inverse
  Cell := fun b N J => (D.family b N).Flag (D.carrier b N) D.R J
  cell := fun b N J =>
    (D.family b N).cell (D.carrier b N) D.R J (D.Accepted b N)
      (D.select b N J)
  fibreCost := fun b N J =>
    (D.family b N).fibreCost (D.carrier b N) D.R J
  fibre_card := by
    intro b N J d a
    exact (D.family b N).cell_fibre_card_le
      (D.carrier b N) D.R J (D.Accepted b N) (D.select b N J) d a
  joint_capacity := by
    intro b N J
    have hsum := (D.family b N).sum_fibreCost_le_capacity
      (D.carrier b N) D.R J
    exact (Nat.cast_le.mpr hsum).trans (D.joint_capacity b N J)

/-- The joint incidence bounds one literal normal axis. -/
theorem PreE7NumericalResidualJointTopCellSourceData.axis_envelope
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (D : PreE7NumericalResidualJointTopCellSourceData w U)
    (b : ℕ)
    (N : {N : Subgroup (preE7NonPairAction w U) // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount (preE7NonPairAction w U)
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate
          preE7NoPairNoC3EarlierNumericalFamilyAction w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b) N J ≤
      (D.C b N * (2 : ℝ) ^ (D.eta * b)) *
        completeQuotientWeight (R := D.R) J := by
  let K := D.carrier b N
  exact K.survivingEpiCount_le_of_weightedRetainedCells
    J (D.Accepted b N) (D.accept_inverse b N J)
    (D.cell b N J) (D.fibreCost b N J) (D.fibre_card b N J)
    (D.C b N) D.eta (D.joint_capacity b N J)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
