import SymmetricSubgroupAsymptotics.Non2PreE7NoPairNoC3PhysicalFrontier
import SymmetricSubgroupAsymptotics.Non2PreE7NonPairConcreteInterface

/-!
# Shared concrete interface for the final pre-E7 residual

The structural owner/comparator catalogue, its numerical decoration, and the
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
coefficients are deliberately absent so the comparator and numerical proofs
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
  owned_comparator : ∀ w i b N, Owned w i b N →
    FusionQuotientComparator (preE7NonPairFirstOwnerAction w i) N (R w i)

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

/-- Reassemble the existing owner/comparator datum after its structural and
numerical halves have been proved. -/
noncomputable def PreE7NoPairNoC3EarlierComparatorCore.withNumerics
    {r : ℕ} (Core : PreE7NoPairNoC3EarlierComparatorCore r)
    (Numerics : PreE7NoPairNoC3OwnerNumerics Core) :
    PreE7NonPairOwnerComparatorData r where
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
  owned_comparator := Core.owned_comparator

/-- Rejected-axis data for the narrowed complete-source predicate.  The cell
records its quotient comparator and retained flag together; the required
capacity is the product of flag cardinality and Yoneda fibre size. -/
structure PreE7NoPairNoC3RetainedCellData {r : ℕ}
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

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
