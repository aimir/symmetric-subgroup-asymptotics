import SymmetricSubgroupAsymptotics.Non2PreE7NoPairNoC3ConcreteInterface
import SymmetricSubgroupAsymptotics.Non2PreE7NonPairMenuMassAggregation

/-!
# Original-weight menu aggregation for the no-pair/no-C3 pre-E7 frontier

The narrowed frontier has the same action index and original normalizer as the
non-pair frontier.  Hence its direct owner/retained-cell coefficients use the
same labelled-action count and the same one-entry-to-menu aggregation.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open RepeatedMarkerOwnerBound

abbrev preE7NoPairNoC3WeightedAxisEntry {r : ℕ}
    (D : PreE7NoPairNoC3OwnerData r)
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

def PreE7NoPairNoC3PolynomialSubquadraticEntryMassBound {r : ℕ}
    (D : PreE7NoPairNoC3OwnerData r) : Prop :=
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

def PreE7NoPairNoC3PolynomialSubquadraticAxisEnvelopeBound {r : ℕ}
    (D : PreE7NoPairNoC3OwnerData r) : Prop :=
  PolynomialSubquadraticMenuNumeratorBound 3
    (fun w i b => fusionAxisEnvelopeTotal
      (preE7NonPairFirstOwnerAction w i)
      (fusionOwnerCapacityCoefficient b
        (preE7NonPairFirstOwnerAction w i)
        (D.Owned w i b) (D.C w i b) (D.eta w i)))

theorem preE7NoPairNoC3EntryMassBound_of_axisEnvelopeBound
    {r : ℕ} (D : PreE7NoPairNoC3OwnerData r)
    (haxis : PreE7NoPairNoC3PolynomialSubquadraticAxisEnvelopeBound D) :
    PreE7NoPairNoC3PolynomialSubquadraticEntryMassBound D := by
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

theorem preE7NoPairNoC3PolynomialSubquadraticMenuMassBound
    {r : ℕ} (D : PreE7NoPairNoC3OwnerData r)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hentry : PreE7NoPairNoC3PolynomialSubquadraticEntryMassBound D) :
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

theorem preE7NoPairNoC3PolynomialSubquadraticMenuMassBound_of_axisEnvelope
    {r : ℕ} (D : PreE7NoPairNoC3OwnerData r)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (haxis : PreE7NoPairNoC3PolynomialSubquadraticAxisEnvelopeBound D) :
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
  preE7NoPairNoC3PolynomialSubquadraticMenuMassBound D hLMM
    (preE7NoPairNoC3EntryMassBound_of_axisEnvelopeBound D haxis)

noncomputable def PreE7NoPairNoC3NumericalCertificate.ofEntryMass
    {r : ℕ} (D : PreE7NoPairNoC3OwnerData r)
    (rho : ℝ) (rho_pos : 0 < rho) (rho_le_eighth : rho ≤ 1 / 8)
    (parameters : GrowingQuotientParameterBound rho
      D.v D.eta D.delta D.cutoff D.alpha)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hentry : PreE7NoPairNoC3PolynomialSubquadraticEntryMassBound D) :
    PreE7NoPairNoC3NumericalCertificate D where
  rho := rho
  rho_pos := rho_pos
  rho_le_eighth := rho_le_eighth
  parameters := parameters
  menuMass := preE7NoPairNoC3PolynomialSubquadraticMenuMassBound D hLMM hentry

noncomputable def PreE7NoPairNoC3NumericalCertificate.ofAxisEnvelope
    {r : ℕ} (D : PreE7NoPairNoC3OwnerData r)
    (rho : ℝ) (rho_pos : 0 < rho) (rho_le_eighth : rho ≤ 1 / 8)
    (parameters : GrowingQuotientParameterBound rho
      D.v D.eta D.delta D.cutoff D.alpha)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (haxis : PreE7NoPairNoC3PolynomialSubquadraticAxisEnvelopeBound D) :
    PreE7NoPairNoC3NumericalCertificate D :=
  PreE7NoPairNoC3NumericalCertificate.ofEntryMass D rho rho_pos
    rho_le_eighth parameters hLMM
    (preE7NoPairNoC3EntryMassBound_of_axisEnvelopeBound D haxis)


end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
