import SymmetricSubgroupAsymptotics.FusionCarrierAnnihilatorYonedaIncidence
import SymmetricSubgroupAsymptotics.Non2PreE7NoPairNoC3EarlierComparators

/-!
# Terminal pre-E7 choices from reversible abelian towers

The certified earlier-owner cover delegates only its final branch to a
residual axis choice.  This file connects that branch to the retained-cell
Yoneda theorem.  For every literal original normal axis, a reversible carrier
keeps the original source and predicate, while an abelian tower retains the
restricted-transgression flags and bounds the remaining fibre.  A single
joint-capacity inequality then yields the exact terminal
`PreE7NoPairNoC3AxisComparatorChoice` consumed by the additive assembly.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Structural and numerical input for one terminal retained action.  The
carrier and tower may depend on the complement degree because the final
source predicate does; neither depends on an individual epimorphism. -/
structure PreE7ResidualAbelianTowerSourceData
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
  carrier : ∀ _b N, FusionAxisCarrier (preE7NonPairAction w U) N
  Accepted : ∀ b N,
    Subgroup ((carrier b N).checked.carrier × Equiv.Perm (Fin b)) → Prop
  accept_inverse : ∀ b N (J : Subgroup (Equiv.Perm (Fin b)))
      (γ : GroupEpimorphism J (carrier b N).checked.quotient),
    (carrier b N).checked.carrierInverseSurvival
        (carrier b N).source_eq
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate
          preE7NoPairNoC3EarlierFamilyAction w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b)
        (fusionQuotientGraph (carrier b N).checked.beta J γ.1) →
      Accepted b N
        (fusionQuotientGraph (carrier b N).checked.beta J γ.1)
  tower : ∀ b N, AxisYonedaTower (carrier b N) R
  joint_capacity : ∀ b N (J : Subgroup (Equiv.Perm (Fin b))),
    (((tower b N).tower.capacity J : ℕ) : ℝ) ≤
      C b N * (2 : ℝ) ^ (eta * b)

attribute [instance]
  PreE7ResidualAbelianTowerSourceData.groupR
  PreE7ResidualAbelianTowerSourceData.finiteR

/-- A retained abelian tower on every terminal axis gives the exact residual
choice used by the certified physical cover.  Its additive tail is zero. -/
noncomputable def PreE7NoPairNoC3AxisComparatorChoice.ofResidualAbelianTowers
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (D : PreE7ResidualAbelianTowerSourceData w U) :
    PreE7NoPairNoC3AxisComparatorChoice w
      (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) where
  R := D.R
  groupR := D.groupR
  finiteR := D.finiteR
  v := D.v
  action := D.action
  action_injective := D.action_injective
  C := D.C
  tailCoefficient := fun _ _ => 0
  eta := D.eta
  delta := D.delta
  cutoff := D.cutoff
  alpha := D.alpha
  theta := D.theta
  alpha_eq := D.alpha_eq
  coefficient_nonneg := D.coefficient_nonneg
  tail_nonneg := fun _ _ => le_rfl
  axis_envelope := by
    intro b N J
    let K := D.carrier b N
    let T := D.tower b N
    have hintrinsic :
        (Nat.card (FusionCarrierAcceptedEpi K.checked J (D.Accepted b N)) : ℝ) ≤
          (T.tower.capacity J : ℝ) *
            completeQuotientWeight (R := D.R) J :=
      fusionCarrierAcceptedEpi_card_le_abelianTower
        K.checked J (D.Accepted b N) T.M T.tower
    have horiginal := K.survivingEpiCount_le_of_intrinsic
      J (D.Accepted b N) (D.accept_inverse b N J) _ hintrinsic
    have hcapacity := D.joint_capacity b N J
    calc
      fusionSurvivingEpiCount (preE7NonPairFirstOwnerAction w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U))
          (preE7NoPairNoC3CertifiedFirstOwnerPredicate
            preE7NoPairNoC3EarlierFamilyAction w
            (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b) N J ≤
          (T.tower.capacity J : ℝ) *
            completeQuotientWeight (R := D.R) J := horiginal
      _ ≤ (D.C b N * (2 : ℝ) ^ (D.eta * b)) *
            completeQuotientWeight (R := D.R) J :=
        mul_le_mul_of_nonneg_right hcapacity
          (completeQuotientWeight_nonneg (R := D.R) J)
      _ = (D.C b N * (2 : ℝ) ^ (D.eta * b)) *
            completeQuotientWeight (R := D.R) J +
          0 * (2 : ℝ) ^ (D.theta * b) := by ring

/-- Assemble terminal tower data for every retained action into the full
certificate-retaining additive axis datum. -/
noncomputable def preE7NoPairNoC3_localAdditiveAxisData_of_residualAbelianTowers
    (D : ∀ w (U : PreE7NonPairActionClass w),
      PreE7ResidualAbelianTowerSourceData w U) :
    PreE7NoPairNoC3LocalAdditiveAxisData
      preE7NoPairNoC3EarlierOwnerCount :=
  preE7NoPairNoC3_localAdditiveAxisData_of_residual
    (fun _ _ =>
      PreE7NoPairNoC3AxisComparatorChoice.ofResidualAbelianTowers (D _ _))

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
