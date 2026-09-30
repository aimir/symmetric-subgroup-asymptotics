import SymmetricSubgroupAsymptotics.FusionCarrierWeightedIncidence
import SymmetricSubgroupAsymptotics.FusionCarrierYonedaTopFamily
import SymmetricSubgroupAsymptotics.Non2PreE7ResidualAbelianTowerChoice

/-!
# Joint top/Yoneda incidence for the terminal pre-E7 residual

The fixed-top Yoneda theorem is deliberately local: after a top is fixed it
retains the restricted-transgression flag and bounds the fibre below it.  A
terminal residual can have many possible tops, and multiplying the number of
tops by a worst-case fibre bound discards the numerical correlation needed by
the original-weight argument.

`PreE7ResidualJointTopCellSourceData` records the stronger object.  Every
accepted carrier epimorphism is sent simultaneously to a complete comparator
map and a finite cell.  The cell may contain the selected top, invariant
radical flags, extendible-character data, the derived-normal coordinate and
the restricted transgression datum.  Its fibre cost depends on the whole
cell, and the hypothesis bounds the single sum of those costs.  Thus top
selection and the Yoneda fibre are never estimated separately.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

attribute [local instance] Fintype.ofFinite

/-- Original-weight terminal data with one joint cost for every retained
top/Yoneda cell.  The cell type may depend on the literal source `J`; its cost
is summed once, before the complete quotient moment is used. -/
structure PreE7ResidualJointTopCellSourceData
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
  PreE7ResidualJointTopCellSourceData.groupR
  PreE7ResidualJointTopCellSourceData.finiteR
  PreE7ResidualJointTopCellSourceData.cell_finite

/-- Joint top/Yoneda cells give the exact terminal comparator choice consumed
by the certified pre-E7 cover.  The additive tail is zero because the whole
terminal contribution has been retained inside the joint incidence. -/
noncomputable def PreE7NoPairNoC3AxisComparatorChoice.ofResidualJointTopCells
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (D : PreE7ResidualJointTopCellSourceData w U) :
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
    have hmain :
        fusionSurvivingEpiCount (preE7NonPairAction w U)
            (preE7NoPairNoC3CertifiedFirstOwnerPredicate
              preE7NoPairNoC3EarlierFamilyAction w
              (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b) N J ≤
          (D.C b N * (2 : ℝ) ^ (D.eta * b)) *
            completeQuotientWeight (R := D.R) J :=
      K.survivingEpiCount_le_of_weightedRetainedCells
        J (D.Accepted b N) (D.accept_inverse b N J)
        (D.cell b N J) (D.fibreCost b N J) (D.fibre_card b N J)
        (D.C b N) D.eta (D.joint_capacity b N J)
    calc
      fusionSurvivingEpiCount
          (preE7NonPairFirstOwnerAction w
            (Fin.last preE7NoPairNoC3EarlierOwnerCount, U))
          (preE7NoPairNoC3CertifiedFirstOwnerPredicate
            preE7NoPairNoC3EarlierFamilyAction w
            (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b) N J ≤
        (D.C b N * (2 : ℝ) ^ (D.eta * b)) *
          completeQuotientWeight (R := D.R) J := hmain
      _ = (D.C b N * (2 : ℝ) ^ (D.eta * b)) *
            completeQuotientWeight (R := D.R) J +
          0 * (2 : ℝ) ^ (D.theta * b) := by ring

/-- Assemble joint terminal cells for every retained action into the full
certificate-retaining additive axis datum. -/
noncomputable def preE7NoPairNoC3_localAdditiveAxisData_of_residualJointTopCells
    (D : ∀ w (U : PreE7NonPairActionClass w),
      PreE7ResidualJointTopCellSourceData w U) :
    PreE7NoPairNoC3LocalAdditiveAxisData
      preE7NoPairNoC3EarlierOwnerCount :=
  preE7NoPairNoC3_localAdditiveAxisData_of_residual
    (fun _ _ ↦
      PreE7NoPairNoC3AxisComparatorChoice.ofResidualJointTopCells (D _ _))

/-! ## Compatibility with the fixed-top tower interface -/

/-- A fixed abelian Yoneda tower is a special case of joint cells: every flag
has the same tower fibre cost.  This constructor verifies that the weighted
interface strictly extends the already checked fixed-top theorem. -/
noncomputable def PreE7ResidualJointTopCellSourceData.ofAbelianTowers
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (D : PreE7ResidualAbelianTowerSourceData w U) :
    PreE7ResidualJointTopCellSourceData w U where
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
  carrier := D.carrier
  Accepted := D.Accepted
  accept_inverse := D.accept_inverse
  Cell := fun b N J ↦
    axisYonedaFlag (D.carrier b N) (some (D.tower b N)) J
  cell := fun b N J ↦
    axisYonedaCell (D.carrier b N) (some (D.tower b N)) J (D.Accepted b N)
  fibreCost := fun b N J _ ↦
    axisYonedaFibreBound (D.carrier b N) (some (D.tower b N)) J
      (D.Accepted b N)
  fibre_card := by
    intro b N J d a
    exact axisYonedaCell_fibre_card_le (D.carrier b N) (some (D.tower b N))
      J (D.Accepted b N) (d, a)
  joint_capacity := by
    intro b N J
    have hcap := axisYonedaCell_joint_capacity
      (D.carrier b N) (D.tower b N) J (D.Accepted b N)
    have hcast :
        (((Nat.card (axisYonedaFlag (D.carrier b N)
              (some (D.tower b N)) J) *
            axisYonedaFibreBound (D.carrier b N) (some (D.tower b N)) J
              (D.Accepted b N) : ℕ)) : ℝ) ≤
          D.C b N * (2 : ℝ) ^ (D.eta * b) :=
      (Nat.cast_le.mpr hcap).trans (D.joint_capacity b N J)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_eq_nat_card] using hcast

/-! ## Construction from a finite family of possible tops -/

/-- Concrete varying-top input.  Every accepted epimorphism selects one
member of a finite family of actual Yoneda towers on its reversible carrier.
The numerical hypothesis is already the correlated sum of the capacities of
those towers. -/
structure PreE7ResidualYonedaTopFamilySourceData
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
  family : ∀ b N, AxisYonedaTopFamily (carrier b N) R
  select : ∀ b N (J : Subgroup (Equiv.Perm (Fin b))),
    FusionCarrierAcceptedEpi (carrier b N).checked J (Accepted b N) →
      (family b N).Index
  joint_capacity : ∀ b N (J : Subgroup (Equiv.Perm (Fin b))),
    (((∑ s : (family b N).Index,
      ((family b N).tower s).tower.capacity J : ℕ)) : ℝ) ≤
        C b N * (2 : ℝ) ^ (eta * b)

attribute [instance]
  PreE7ResidualYonedaTopFamilySourceData.groupR
  PreE7ResidualYonedaTopFamilySourceData.finiteR

/-- A finite epimorphism-selected family of actual Yoneda tops produces the
joint weighted cells required by the terminal pre-E7 interface. -/
noncomputable def
    PreE7ResidualYonedaTopFamilySourceData.toJointTopCellSourceData
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (D : PreE7ResidualYonedaTopFamilySourceData w U) :
    PreE7ResidualJointTopCellSourceData w U where
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
  carrier := D.carrier
  Accepted := D.Accepted
  accept_inverse := D.accept_inverse
  Cell := fun b N J ↦ (D.family b N).Flag (D.carrier b N) D.R J
  cell := fun b N J ↦
    (D.family b N).cell (D.carrier b N) D.R J (D.Accepted b N)
      (D.select b N J)
  fibreCost := fun b N J ↦
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

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
