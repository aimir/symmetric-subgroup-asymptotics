import SymmetricSubgroupAsymptotics.GrowingMenuMassEntryCertificate
import SymmetricSubgroupAsymptotics.Non2PreE7MenuMassAggregation
import SymmetricSubgroupAsymptotics.Non2PreE7NonPairConcreteInterface

/-!
# Original-weight menu aggregation for the non-pair pre-E7 frontier

Restricting the pre-`E7` action index by four further no-frame conditions can
only decrease its cardinality.  Hence the same labelled transitive-action
input turns a uniform one-entry estimate into the complete original-weight
menu mass on the exact non-pair residual.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open RepeatedMarkerOwnerBound

theorem preE7NonPairActionClass_card_le_preE7 (w : ℕ) :
    Nat.card (PreE7NonPairActionClass w) ≤ Nat.card (PreE7ActionClass w) :=
  Finite.card_subtype_le _

/-- The exact non-pair first-owner index inherits the published
subquadratic action count. -/
theorem preE7NonPairFirstOwnerIndex_subquadratic
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput) (r : ℕ) :
    SubquadraticMenuIndexCount
      (fun w => PreE7NonPairFirstOwnerIndex (r + 1) w) := by
  intro ε hε
  obtain ⟨B, hB, hcount⟩ := hLMM ε hε
  refine ⟨((r + 1 : ℕ) : ℝ) * B, mul_nonneg (by positivity) hB, ?_⟩
  intro w
  have hnonpair : (Nat.card (PreE7NonPairActionClass w) : ℝ) ≤
      (Nat.card (PreE7ActionClass w) : ℝ) := by
    exact_mod_cast preE7NonPairActionClass_card_le_preE7 w
  have hpre : (Nat.card (PreE7ActionClass w) : ℝ) ≤
      (Nat.card (LabelledTransitiveSubgroup w) : ℝ) := by
    exact_mod_cast preE7ActionClass_card_le_labelled w
  calc
    (Nat.card (PreE7NonPairFirstOwnerIndex (r + 1) w) : ℝ) =
        ((r + 1 : ℕ) : ℝ) *
          (Nat.card (PreE7NonPairActionClass w) : ℝ) := by
      simp only [PreE7NonPairFirstOwnerIndex, Nat.card_prod,
        Nat.card_fin, Nat.cast_mul]
    _ ≤ ((r + 1 : ℕ) : ℝ) *
        (Nat.card (LabelledTransitiveSubgroup w) : ℝ) :=
      mul_le_mul_of_nonneg_left (hnonpair.trans hpre) (by positivity)
    _ ≤ ((r + 1 : ℕ) : ℝ) *
        (B * (2 : ℝ) ^ (ε * (w : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (hcount w) (by positivity)
    _ = (((r + 1 : ℕ) : ℝ) * B) *
        (2 : ℝ) ^ (ε * (w : ℝ) ^ 2) := by ring

abbrev preE7NonPairWeightedAxisEntry {r : ℕ}
    (D : PreE7NonPairOwnerComparatorData r)
    (w : ℕ) (i : PreE7NonPairFirstOwnerIndex (r + 1) w)
    (b : ℕ) : ℝ :=
  fusionAxisEnvelopeTotal
      (preE7NonPairFirstOwnerAction w i)
      (fusionOwnerCapacityCoefficient b
        (preE7NonPairFirstOwnerAction w i)
        (D.Owned w i b) (D.C w i b) (D.eta w i)) /
    (Nat.card (Subgroup.normalizer
      (preE7NonPairFirstOwnerAction w i :
        Set (Equiv.Perm (Fin w)))) : ℝ)

def PreE7NonPairPolynomialSubquadraticEntryMassBound {r : ℕ}
    (D : PreE7NonPairOwnerComparatorData r) : Prop :=
  PolynomialSubquadraticMenuEntryBound 3
    (fun w i b => fusionAxisEnvelopeTotal
      (preE7NonPairFirstOwnerAction w i)
      (fusionOwnerCapacityCoefficient b
        (preE7NonPairFirstOwnerAction w i)
        (D.Owned w i b) (D.C w i b) (D.eta w i)))
    (fun w i =>
      (Nat.card (Subgroup.normalizer
        (preE7NonPairFirstOwnerAction w i :
          Set (Equiv.Perm (Fin w)))) : ℝ))

def PreE7NonPairPolynomialSubquadraticAxisEnvelopeBound {r : ℕ}
    (D : PreE7NonPairOwnerComparatorData r) : Prop :=
  PolynomialSubquadraticMenuNumeratorBound 3
    (fun w i b => fusionAxisEnvelopeTotal
      (preE7NonPairFirstOwnerAction w i)
      (fusionOwnerCapacityCoefficient b
        (preE7NonPairFirstOwnerAction w i)
        (D.Owned w i b) (D.C w i b) (D.eta w i)))

theorem preE7NonPairEntryMassBound_of_axisEnvelopeBound
    {r : ℕ} (D : PreE7NonPairOwnerComparatorData r)
    (haxis : PreE7NonPairPolynomialSubquadraticAxisEnvelopeBound D) :
    PreE7NonPairPolynomialSubquadraticEntryMassBound D := by
  apply polynomialSubquadraticMenuEntryBound_of_numerator _ _
  · intro w i b
    apply fusionAxisEnvelopeTotal_nonneg
    intro N
    exact fusionOwnerCapacityCoefficient_nonneg
      (preE7NonPairFirstOwnerAction w i)
      (D.Owned w i b) (D.C w i b) (D.eta w i)
      (D.coefficient_nonneg w i b) N
  · intro w i
    exact_mod_cast (Nat.card_pos (α :=
      Subgroup.normalizer
        (preE7NonPairFirstOwnerAction w i :
          Set (Equiv.Perm (Fin w)))))
  · exact haxis

theorem preE7NonPairPolynomialSubquadraticMenuMassBound
    {r : ℕ} (D : PreE7NonPairOwnerComparatorData r)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hentry : PreE7NonPairPolynomialSubquadraticEntryMassBound D) :
    PolynomialSubquadraticMenuMassBound 3
      (fun w i b => fusionAxisEnvelopeTotal
        (preE7NonPairFirstOwnerAction w i)
        (fusionOwnerCapacityCoefficient b
          (preE7NonPairFirstOwnerAction w i)
          (D.Owned w i b) (D.C w i b) (D.eta w i)))
      (fun w i =>
        (Nat.card (Subgroup.normalizer
          (preE7NonPairFirstOwnerAction w i :
            Set (Equiv.Perm (Fin w)))) : ℝ)) :=
  polynomialSubquadraticMenuMassBound_of_index_entry _ _
    (preE7NonPairFirstOwnerIndex_subquadratic hLMM r) hentry

theorem preE7NonPairPolynomialSubquadraticMenuMassBound_of_axisEnvelope
    {r : ℕ} (D : PreE7NonPairOwnerComparatorData r)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (haxis : PreE7NonPairPolynomialSubquadraticAxisEnvelopeBound D) :
    PolynomialSubquadraticMenuMassBound 3
      (fun w i b => fusionAxisEnvelopeTotal
        (preE7NonPairFirstOwnerAction w i)
        (fusionOwnerCapacityCoefficient b
          (preE7NonPairFirstOwnerAction w i)
          (D.Owned w i b) (D.C w i b) (D.eta w i)))
      (fun w i =>
        (Nat.card (Subgroup.normalizer
          (preE7NonPairFirstOwnerAction w i :
            Set (Equiv.Perm (Fin w)))) : ℝ)) :=
  preE7NonPairPolynomialSubquadraticMenuMassBound D hLMM
    (preE7NonPairEntryMassBound_of_axisEnvelopeBound D haxis)

noncomputable def PreE7NonPairNumericalCertificate.ofEntryMass
    {r : ℕ} (D : PreE7NonPairOwnerComparatorData r)
    (rho : ℝ) (rho_pos : 0 < rho) (rho_le_eighth : rho ≤ 1 / 8)
    (parameters : GrowingQuotientParameterBound rho
      D.v D.eta D.delta D.cutoff D.alpha)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hentry : PreE7NonPairPolynomialSubquadraticEntryMassBound D) :
    PreE7NonPairNumericalCertificate D where
  rho := rho
  rho_pos := rho_pos
  rho_le_eighth := rho_le_eighth
  parameters := parameters
  menuMass := preE7NonPairPolynomialSubquadraticMenuMassBound D hLMM hentry

noncomputable def PreE7NonPairNumericalCertificate.ofAxisEnvelope
    {r : ℕ} (D : PreE7NonPairOwnerComparatorData r)
    (rho : ℝ) (rho_pos : 0 < rho) (rho_le_eighth : rho ≤ 1 / 8)
    (parameters : GrowingQuotientParameterBound rho
      D.v D.eta D.delta D.cutoff D.alpha)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (haxis : PreE7NonPairPolynomialSubquadraticAxisEnvelopeBound D) :
    PreE7NonPairNumericalCertificate D :=
  PreE7NonPairNumericalCertificate.ofEntryMass D rho rho_pos
    rho_le_eighth parameters hLMM
    (preE7NonPairEntryMassBound_of_axisEnvelopeBound D haxis)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
