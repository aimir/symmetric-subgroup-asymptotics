import SymmetricSubgroupAsymptotics.Non2PreE7NoPairNoC3NumericalClosure

/-!
# Shared concrete interface for the final pre-E7 residual

The structural owner-envelope catalogue, its numerical decoration, and the
rejected-axis retained cells are separated so their proofs can be developed
in disjoint modules.  They retain the existing non-pair action and normal-axis
types; only the complete-source predicate carries the additional no-`C3`
filter.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Structural part of the earlier-owner catalogue.  Numerical exponents and
coefficients are deliberately absent so the owner-envelope and numerical proofs
can be developed independently after the catalogue itself is fixed. -/
structure PreE7NoPairNoC3EarlierComparatorCore (r : ℕ) where
  Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop
  earlier_natural : DegreeNaturalOwnerMenu Earlier
  R : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → Type
  [groupR : ∀ w i, Group (R w i)]
  [finiteR : ∀ w i, Finite (R w i)]
  Owned : ∀ w (i : PreE7NonPairFirstOwnerIndex (r + 1) w) (_b : ℕ),
    {N : Subgroup (preE7NonPairFirstOwnerAction w i) // N.Normal} → Prop
  v : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℕ
  action : ∀ w i, R w i →* Equiv.Perm (Fin (v w i))
  action_injective : ∀ w i, Function.Injective (action w i)
  owned_envelope : ∀ w i b N, Owned w i b N →
    ∀ J : Subgroup (Equiv.Perm (Fin b)),
      fusionSurvivingEpiCount (preE7NonPairFirstOwnerAction w i)
          (preE7NoPairNoC3FirstOwnerPredicate
            (ownerOrResidualEligible Earlier) w i b) N J ≤
        completeQuotientWeight (R := R w i) J

attribute [instance]
  PreE7NoPairNoC3EarlierComparatorCore.groupR
  PreE7NoPairNoC3EarlierComparatorCore.finiteR

/-- Numerical functions attached to one fixed structural catalogue. -/
structure PreE7NoPairNoC3OwnerNumerics {r : ℕ}
    (Core : PreE7NoPairNoC3EarlierComparatorCore r) where
  C : ∀ w (i : PreE7NonPairFirstOwnerIndex (r + 1) w) (_b : ℕ),
    {N : Subgroup (preE7NonPairFirstOwnerAction w i) // N.Normal} → ℝ
  eta : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  delta : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  cutoff : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  alpha : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ
  coefficient_nonneg : ∀ w i b N, 0 ≤ C w i b N
  alpha_eq : ∀ w i, alpha w i = eta w i + cutoff w i

/-- Complete owner-envelope datum for the narrowed no-pair/no-`C3` frontier. -/
structure PreE7NoPairNoC3OwnerData (r : ℕ) where
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
          (preE7NoPairNoC3FirstOwnerPredicate
            (ownerOrResidualEligible Earlier) w i b) N J ≤
        completeQuotientWeight (R := R w i) J

attribute [instance]
  PreE7NoPairNoC3OwnerData.groupR
  PreE7NoPairNoC3OwnerData.finiteR

/-- Reassemble the narrowed owner-envelope datum after its structural and
numerical halves have been proved. -/
noncomputable def PreE7NoPairNoC3EarlierComparatorCore.withNumerics
    {r : ℕ} (Core : PreE7NoPairNoC3EarlierComparatorCore r)
    (Numerics : PreE7NoPairNoC3OwnerNumerics Core) :
    PreE7NoPairNoC3OwnerData r where
  Earlier := Core.Earlier
  earlier_natural := Core.earlier_natural
  R := Core.R
  groupR := Core.groupR
  finiteR := Core.finiteR
  Owned := Core.Owned
  C := Numerics.C
  v := Core.v
  eta := Numerics.eta
  delta := Numerics.delta
  cutoff := Numerics.cutoff
  alpha := Numerics.alpha
  action := Core.action
  action_injective := Core.action_injective
  coefficient_nonneg := Numerics.coefficient_nonneg
  alpha_eq := Numerics.alpha_eq
  owned_envelope := Core.owned_envelope

/-- Rejected-axis data for the narrowed complete-source predicate.  The cell
records its complete quotient map and retained flag together; the required
capacity is the product of flag cardinality and Yoneda fibre size. -/
structure PreE7NoPairNoC3RetainedCellData {r : ℕ}
    (D : PreE7NoPairNoC3OwnerData r) where
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
        (preE7NoPairNoC3FirstOwnerPredicate
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

attribute [instance] PreE7NoPairNoC3RetainedCellData.flag_finite

/-- Uniform numerical package for the narrowed physical frontier. -/
structure PreE7NoPairNoC3NumericalCertificate {r : ℕ}
    (D : PreE7NoPairNoC3OwnerData r) where
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

/-- Exact integration of the narrowed owner, retained-cell and numerical
packages into its ambient-degree forward estimate. -/
noncomputable def preE7NoPairNoC3_exponentialForwardEstimate_of_data
    {r : ℕ}
    (D : PreE7NoPairNoC3OwnerData r)
    (Cells : PreE7NoPairNoC3RetainedCellData D)
    (Numerics : PreE7NoPairNoC3NumericalCertificate D)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7NoPairNoC3ResidualRatio :=
  preE7NoPairNoC3_exponentialForwardEstimate_of_axisOwnerOrRetainedCells
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
