import SymmetricSubgroupAsymptotics.Non2PreE7NonPairNumericalClosure

/-!
# Concrete interface for the non-pair pre-E7 action consumers

These are the three packages which the remaining action exhaustion must
construct after both pair menus have been removed: the ordered owner-envelope
catalogue, rejected-axis reversible cells, and the uniform numerical
certificate.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open RepeatedMarkerOwnerBound

structure PreE7NonPairOwnerComparatorData (r : ℕ) where
  Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop
  earlier_natural : DegreeNaturalOwnerMenu Earlier
  R : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → Type
  [groupR : ∀ w i, Group (R w i)]
  [finiteR : ∀ w i, Finite (R w i)]
  Owned : ∀ w (i : PreE7NonPairFirstOwnerIndex (r + 1) w) (_b : ℕ),
    {N : Subgroup (preE7NonPairFirstOwnerAction w i) // N.Normal} → Prop
  C : ∀ w (i : PreE7NonPairFirstOwnerIndex (r + 1) w) (_b : ℕ),
    {N : Subgroup (preE7NonPairFirstOwnerAction w i) // N.Normal} → ℝ
  v : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℕ
  eta : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  delta : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  cutoff : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  alpha : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  action : ∀ w i, R w i →* Equiv.Perm (Fin (v w i))
  action_injective : ∀ w i, Function.Injective (action w i)
  coefficient_nonneg : ∀ w i b N, 0 ≤ C w i b N
  alpha_eq : ∀ w i, alpha w i = eta w i + cutoff w i
  owned_envelope : ∀ w i b N, Owned w i b N →
    ∀ J : Subgroup (Equiv.Perm (Fin b)),
      fusionSurvivingEpiCount (preE7NonPairFirstOwnerAction w i)
          (preE7NonPairFirstOwnerPredicate
            (ownerOrResidualEligible Earlier) w i b) N J ≤
        completeQuotientWeight (R := R w i) J

attribute [instance]
  PreE7NonPairOwnerComparatorData.groupR
  PreE7NonPairOwnerComparatorData.finiteR

structure PreE7NonPairRetainedCellData {r : ℕ}
    (D : PreE7NonPairOwnerComparatorData r) where
  carrier : ∀ w i N,
    FusionAxisCarrier (preE7NonPairFirstOwnerAction w i) N
  Accepted : ∀ w i b N,
    Subgroup ((carrier w i N).checked.carrier ×
      Equiv.Perm (Fin b)) → Prop
  accept_inverse : ∀ w i b N
      (J : Subgroup (Equiv.Perm (Fin b)))
      (gamma : GroupEpimorphism J (carrier w i N).checked.quotient),
    (carrier w i N).checked.carrierInverseSurvival
        (carrier w i N).source_eq
        (preE7NonPairFirstOwnerPredicate
          (ownerOrResidualEligible D.Earlier) w i b)
        (fusionQuotientGraph
          (carrier w i N).checked.beta J gamma.1) →
      Accepted w i b N
        (fusionQuotientGraph
          (carrier w i N).checked.beta J gamma.1)
  Flag : ∀ w (i : PreE7NonPairFirstOwnerIndex (r + 1) w) b
      (_N : {N : Subgroup
        (preE7NonPairFirstOwnerAction w i) // N.Normal})
      (_J : Subgroup (Equiv.Perm (Fin b))), Type
  [flag_finite : ∀ w i b N J, Finite (Flag w i b N J)]
  cell : ∀ w i b N (J : Subgroup (Equiv.Perm (Fin b))),
    FusionCarrierAcceptedEpi (carrier w i N).checked J
        (Accepted w i b N) →
      CompleteQuotientMap J (D.R w i) × Flag w i b N J
  fibreBound : ∀ w (i : PreE7NonPairFirstOwnerIndex (r + 1) w) b
      (_N : {N : Subgroup
        (preE7NonPairFirstOwnerAction w i) // N.Normal})
      (_J : Subgroup (Equiv.Perm (Fin b))), ℕ
  fibre_card : ∀ w i b N (J : Subgroup (Equiv.Perm (Fin b)))
      (x : CompleteQuotientMap J (D.R w i) × Flag w i b N J),
    Nat.card {gamma : FusionCarrierAcceptedEpi
        (carrier w i N).checked J (Accepted w i b N) //
      cell w i b N J gamma = x} ≤ fibreBound w i b N J
  joint_capacity : ∀ w i b N, ¬ D.Owned w i b N →
    ∀ J : Subgroup (Equiv.Perm (Fin b)),
      (Nat.card (Flag w i b N J) * fibreBound w i b N J : ℕ) ≤
        D.C w i b N * (2 : ℝ) ^ (D.eta w i * b)

attribute [instance] PreE7NonPairRetainedCellData.flag_finite

structure PreE7NonPairNumericalCertificate {r : ℕ}
    (D : PreE7NonPairOwnerComparatorData r) where
  rho : ℝ
  rho_pos : 0 < rho
  rho_le_eighth : rho ≤ 1 / 8
  parameters : GrowingQuotientParameterBound rho
    D.v D.eta D.delta D.cutoff D.alpha
  menuMass : PolynomialSubquadraticMenuMassBound 3
    (fun w i b => fusionAxisEnvelopeTotal
      (preE7NonPairFirstOwnerAction w i)
      (fusionOwnerCapacityCoefficient b
        (preE7NonPairFirstOwnerAction w i)
        (D.Owned w i b) (D.C w i b) (D.eta w i)))
    (fun w i =>
      (Nat.card (Subgroup.normalizer
        (preE7NonPairFirstOwnerAction w i :
          Set (Equiv.Perm (Fin w)))) : ℝ))

/-- Exact integration of the narrowed non-pair packages. -/
noncomputable def preE7NonPair_exponentialForwardEstimate_of_data
    {r : ℕ}
    (D : PreE7NonPairOwnerComparatorData r)
    (Cells : PreE7NonPairRetainedCellData D)
    (Numerics : PreE7NonPairNumericalCertificate D)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7NonPairResidualRatio :=
  preE7NonPair_exponentialForwardEstimate_of_axisOwnerOrRetainedCells
    D.Earlier D.earlier_natural D.R D.Owned D.C
    (fun w i =>
      (Nat.card (Subgroup.normalizer
        (preE7NonPairFirstOwnerAction w i :
          Set (Equiv.Perm (Fin w)))) : ℝ))
    D.v D.eta D.delta D.cutoff D.alpha D.action D.action_injective
    D.coefficient_nonneg (fun _ _ => rfl) D.alpha_eq D.owned_envelope
    Cells.carrier Cells.Accepted Cells.accept_inverse Cells.Flag
    (fun _ _ _ _ _ => inferInstance) Cells.cell Cells.fibreBound
    Cells.fibre_card Cells.joint_capacity Numerics.rho_pos
    Numerics.rho_le_eighth Numerics.parameters Numerics.menuMass hcoarse

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
