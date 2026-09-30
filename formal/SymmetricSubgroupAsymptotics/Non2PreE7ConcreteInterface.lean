import SymmetricSubgroupAsymptotics.Non2PreE7NumericalClosure

/-!
# Concrete interface for the pre-E7 action consumers

The numerical transfer theorem is already proved.  This file freezes the
three concrete packages which its action consumers must construct: the
ordered earlier-owner/comparator catalogue, the rejected-axis retained cells,
and the uniform numerical certificate.  These structures are integration
interfaces, not assumptions of the final theorem: the publication-facing
closure must construct them from the named action consumers and published
inputs.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open RepeatedMarkerOwnerBound

/-- The common data fixed by the concrete earlier-owner catalogue.  In
particular `C` and `eta` are shared verbatim with the rejected-axis capacity
package, preventing the structural and numerical branches from choosing
incompatible coefficients. -/
structure PreE7OwnerComparatorData (r : ℕ) where
  Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop
  earlier_natural : DegreeNaturalOwnerMenu Earlier
  R : ∀ w, PreE7FirstOwnerIndex (r + 1) w → Type
  [groupR : ∀ w i, Group (R w i)]
  [finiteR : ∀ w i, Finite (R w i)]
  Owned : ∀ w (i : PreE7FirstOwnerIndex (r + 1) w) (_b : ℕ),
    {N : Subgroup (preE7FirstOwnerAction w i) // N.Normal} → Prop
  C : ∀ w (i : PreE7FirstOwnerIndex (r + 1) w) (_b : ℕ),
    {N : Subgroup (preE7FirstOwnerAction w i) // N.Normal} → ℝ
  v : ∀ w, PreE7FirstOwnerIndex (r + 1) w → ℕ
  eta : ∀ w, PreE7FirstOwnerIndex (r + 1) w → ℝ
  delta : ∀ w, PreE7FirstOwnerIndex (r + 1) w → ℝ
  cutoff : ∀ w, PreE7FirstOwnerIndex (r + 1) w → ℝ
  alpha : ∀ w, PreE7FirstOwnerIndex (r + 1) w → ℝ
  action : ∀ w i, R w i →* Equiv.Perm (Fin (v w i))
  action_injective : ∀ w i, Function.Injective (action w i)
  coefficient_nonneg : ∀ w i b N, 0 ≤ C w i b N
  alpha_eq : ∀ w i, alpha w i = eta w i + cutoff w i
  owned_comparator : ∀ w i b N, Owned w i b N →
    FusionQuotientComparator (preE7FirstOwnerAction w i) N (R w i)

attribute [instance]
  PreE7OwnerComparatorData.groupR
  PreE7OwnerComparatorData.finiteR

/-- The reversible carrier and joint retained-flag/Yoneda capacity on every
axis rejected by the earlier-owner catalogue.  The cell map lands in the
same comparator and uses the same coefficient and exponent as the catalogue
above. -/
structure PreE7RetainedCellData {r : ℕ}
    (D : PreE7OwnerComparatorData r) where
  carrier : ∀ w i N, FusionAxisCarrier (preE7FirstOwnerAction w i) N
  Accepted : ∀ w i b N,
    Subgroup ((carrier w i N).checked.carrier ×
      Equiv.Perm (Fin b)) → Prop
  accept_inverse : ∀ w i b N
      (J : Subgroup (Equiv.Perm (Fin b)))
      (gamma : GroupEpimorphism J (carrier w i N).checked.quotient),
    (carrier w i N).checked.carrierInverseSurvival
        (carrier w i N).source_eq
        (preE7FirstOwnerPredicate
          (ownerOrResidualEligible D.Earlier) w i b)
        (fusionQuotientGraph
          (carrier w i N).checked.beta J gamma.1) →
      Accepted w i b N
        (fusionQuotientGraph
          (carrier w i N).checked.beta J gamma.1)
  Flag : ∀ w (i : PreE7FirstOwnerIndex (r + 1) w) b
      (_N : {N : Subgroup (preE7FirstOwnerAction w i) // N.Normal})
      (_J : Subgroup (Equiv.Perm (Fin b))), Type
  [flag_finite : ∀ w i b N J, Finite (Flag w i b N J)]
  cell : ∀ w i b N (J : Subgroup (Equiv.Perm (Fin b))),
    FusionCarrierAcceptedEpi (carrier w i N).checked J
        (Accepted w i b N) →
      CompleteQuotientMap J (D.R w i) × Flag w i b N J
  fibreBound : ∀ w (i : PreE7FirstOwnerIndex (r + 1) w) b
      (_N : {N : Subgroup (preE7FirstOwnerAction w i) // N.Normal})
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

attribute [instance] PreE7RetainedCellData.flag_finite

/-- The uniform margin and exact original-normalizer-weighted mass for the
same catalogue.  All action, normal-axis and cell data stay outside this
purely numerical certificate. -/
structure PreE7NumericalCertificate {r : ℕ}
    (D : PreE7OwnerComparatorData r) where
  rho : ℝ
  rho_pos : 0 < rho
  rho_le_eighth : rho ≤ 1 / 8
  parameters : GrowingQuotientParameterBound rho
    D.v D.eta D.delta D.cutoff D.alpha
  menuMass : PolynomialSubquadraticMenuMassBound 3
    (fun w i b => fusionAxisEnvelopeTotal
      (preE7FirstOwnerAction w i)
      (fusionOwnerCapacityCoefficient b
        (preE7FirstOwnerAction w i)
        (D.Owned w i b) (D.C w i b) (D.eta w i)))
    (fun w i =>
      (Nat.card (Subgroup.normalizer
        (preE7FirstOwnerAction w i :
          Set (Equiv.Perm (Fin w)))) : ℝ))

/-- Exact integration of the three concrete packages.  Consequently the
only remaining work is to construct these packages from the action consumers;
no transfer, pointing, axis summation or hot/cold estimate remains here. -/
noncomputable def preE7Unresolved_exponentialForwardEstimate_of_data
    {r : ℕ}
    (D : PreE7OwnerComparatorData r)
    (Cells : PreE7RetainedCellData D)
    (Numerics : PreE7NumericalCertificate D)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7UnresolvedOutsideRatio :=
  preE7Unresolved_exponentialForwardEstimate_of_axisOwnerOrRetainedCells
    D.Earlier D.earlier_natural D.R D.Owned D.C
    (fun w i =>
      (Nat.card (Subgroup.normalizer
        (preE7FirstOwnerAction w i :
          Set (Equiv.Perm (Fin w)))) : ℝ))
    D.v D.eta D.delta D.cutoff D.alpha D.action D.action_injective
    D.coefficient_nonneg (fun _ _ => rfl) D.alpha_eq D.owned_comparator
    Cells.carrier Cells.Accepted Cells.accept_inverse Cells.Flag
    (fun _ _ _ _ _ => inferInstance) Cells.cell Cells.fibreBound
    Cells.fibre_card Cells.joint_capacity Numerics.rho_pos
    Numerics.rho_le_eighth Numerics.parameters Numerics.menuMass hcoarse

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
