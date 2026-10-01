import SymmetricSubgroupAsymptotics.Non2PreE7NumericalExceptionalCatalogue
import SymmetricSubgroupAsymptotics.FusionCarrierWeightedIncidence
import SymmetricSubgroupAsymptotics.FusionCarrierYonedaTopFamily
import SymmetricSubgroupAsymptotics.T1ExceptionalClosure

/-!
# T1 from numerically complete joint terminal cells

The terminal source below retains the same original-weight joint cell used by
the Yoneda incidence theorem, now against the numerically certified earlier
catalogue.  It also carries the entry parameters and the single total
coefficient bound needed by the all-width aggregation.  No separate global
numerical certificate remains in the final application.
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

/-- Convert the terminal joint cells into the exact numerical row selected by
the global catalogue. -/
noncomputable def
    PreE7NoPairNoC3NumericalExceptionalChoice.ofResidualJointTopCells
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (D : PreE7NumericalResidualJointTopCellSourceData w U) :
    PreE7NoPairNoC3NumericalExceptionalChoice w
      (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) := by
  let Dmain : ℕ → ℝ := fun b =>
    fusionAxisEnvelopeTotal (preE7NonPairAction w U) (D.C b)
  exact
    { D := Dmain
      T := fun _ => 0
      X := fun _ => 0
      v := D.v
      eta := D.eta
      delta := D.delta
      cutoff := D.cutoff
      alpha := D.alpha
      theta := D.theta
      alpha_eq := D.alpha_eq
      D_nonneg := fun b =>
        fusionAxisEnvelopeTotal_nonneg _ _ (D.coefficient_nonneg b)
      T_nonneg := fun _ => le_rfl
      parameters := D.parameters
      main_total_bound := D.coefficient_total_bound
      tail_total_bound := fun _ => by positivity
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
        let P := preE7NoPairNoC3CertifiedFirstOwnerPredicate
          preE7NoPairNoC3EarlierNumericalFamilyAction w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b
        have hsource (J : Subgroup (Equiv.Perm (Fin b))) :
            fusionCompleteSourceSum (preE7NonPairAction w U) P J ≤
              (Dmain b * (2 : ℝ) ^ (D.eta * b)) *
                  completeQuotientWeight (R := D.R) J +
                0 * (2 : ℝ) ^ (D.theta * b) := by
          calc
            _ ≤ fusionAxisEnvelopeTotal (preE7NonPairAction w U) (D.C b) *
                ((2 : ℝ) ^ (D.eta * b) *
                  completeQuotientWeight (R := D.R) J) :=
              fusionCompleteSourceSum_le_axisEnvelopeTotal
                (preE7NonPairAction w U) P (D.C b)
                (fun J => (2 : ℝ) ^ (D.eta * b) *
                  completeQuotientWeight (R := D.R) J)
                (fun N J => by
                  simpa only [mul_assoc] using D.axis_envelope b N J) J
            _ = _ := by unfold Dmain; ring
        have h := fusionPhysical_growingQuotient_additiveTail_kernel_bound
          (preE7NonPairAction w U) P
          (preE7NoPairNoC3CertifiedFirstOwnerPredicate_natural _ w
            (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b)
          D.action D.action_injective (Dmain b) 0 D.eta D.theta D.delta
          D.cutoff
          (fusionAxisEnvelopeTotal_nonneg _ _ (D.coefficient_nonneg b))
          le_rfl hsource
        simpa only [P, Dmain, D.alpha_eq, add_zero] using h }

/-- Assemble terminal joint cells for every literal action. -/
noncomputable def preE7NoPairNoC3_numericalResidualChoices
    (D : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NumericalResidualJointTopCellSourceData w U) :
    ∀ w (U : PreE7NonPairActionClass w),
      PreE7NoPairNoC3NumericalExceptionalChoice w
        (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) :=
  fun _ _ =>
    PreE7NoPairNoC3NumericalExceptionalChoice.ofResidualJointTopCells (D _ _)

/-- Numerically complete earlier-owner packages and terminal joint cells close
T1; the global numerical certificate is constructed internally. -/
theorem T1_of_preE7_numerical_jointTopCell_data
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (D : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NumericalResidualJointTopCellSourceData w U)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) : T1 :=
  let Residual := preE7NoPairNoC3_numericalResidualChoices D
  T1_of_preE7_noPairNoC3_localExceptional_data
    hTracey hExceptional hChief hWeight hPrimitive h18 hKP
    (preE7NoPairNoC3_numericalExceptionalData Residual)
    (preE7NoPairNoC3_numericalExceptionalCertificate
      Residual hLMM hcoarse)
    hcoarse

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
