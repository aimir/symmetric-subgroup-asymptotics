import SymmetricSubgroupAsymptotics.FusionCarrierYonedaTopFamily
import SymmetricSubgroupAsymptotics.Non2PreE7ComparatorAbelianTowerTemplate

/-!
# Refined-capacity earlier-owner template

The refined-capacity families use a reversible carrier on every literal
normal axis.  An accepted epimorphism selects one member of a finite family
of annihilator-aware Yoneda tops.  The complete incidence cost is the sum of
the selected towers' capacities, so top count and fibre size are never
maximized separately.

This module packages that construction into the common pre-`E7` earlier-owner
certificate.  It also provides the version with an exhaustive additive tail,
needed by the full affine-wreath family.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

attribute [local instance] Fintype.ofFinite

/-- Source data shared by the multiplicative refined-capacity families.  All
objects are attached to the literal action and literal normal axis. -/
structure PreE7RefinedCapacitySourceData
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  template_eq : family.template = .refinedCapacity
  R : Type
  [groupR : Group R]
  [finiteR : Finite R]
  v : ℕ
  action : R →* Equiv.Perm (Fin v)
  action_injective : Function.Injective action
  C : ℕ → {N : Subgroup (preE7NonPairAction w i) // N.Normal} → ℝ
  eta : ℝ
  delta : ℝ
  cutoff : ℝ
  alpha : ℝ
  theta : ℝ
  alpha_eq : alpha = eta + cutoff
  coefficient_nonneg : ∀ b N, 0 ≤ C b N
  carrier : ∀ N, FusionAxisCarrier (preE7NonPairAction w i) N
  Accepted : ∀ b N,
    Subgroup ((carrier N).checked.carrier × Equiv.Perm (Fin b)) → Prop
  accept_inverse : ∀ b N (J : Subgroup (Equiv.Perm (Fin b)))
      (gamma : GroupEpimorphism J (carrier N).checked.quotient),
    (carrier N).checked.carrierInverseSurvival
        (carrier N).source_eq
        (preE7NoPairNoC3BroadActionPredicate w i b)
        (fusionQuotientGraph (carrier N).checked.beta J gamma.1) →
      Accepted b N
        (fusionQuotientGraph (carrier N).checked.beta J gamma.1)
  topFamily : ∀ _b N, AxisYonedaTopFamily (carrier N) R
  select : ∀ b N (J : Subgroup (Equiv.Perm (Fin b))),
    FusionCarrierAcceptedEpi (carrier N).checked J (Accepted b N) →
      (topFamily b N).Index
  joint_capacity : ∀ b N (J : Subgroup (Equiv.Perm (Fin b))),
    ((∑ s : (topFamily b N).Index,
      ((topFamily b N).tower s).tower.capacity J : ℕ) : ℝ) ≤
        C b N * (2 : ℝ) ^ (eta * b)

attribute [instance]
  PreE7RefinedCapacitySourceData.groupR
  PreE7RefinedCapacitySourceData.finiteR

namespace PreE7RefinedCapacitySourceData

variable {family : PreE7NoPairNoC3EarlierOwnerFamily}
  {w : ℕ} {i : PreE7NonPairActionClass w}
  (D : PreE7RefinedCapacitySourceData family w i)

/-- The complete carrier/Yoneda construction bounds one original literal
normal axis with the retained comparator weight. -/
theorem broad_axis_envelope
    (b : ℕ)
    (N : {N : Subgroup (preE7NonPairAction w i) // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount (preE7NonPairAction w i)
        (preE7NoPairNoC3BroadActionPredicate w i b) N J ≤
      (D.C b N * (2 : ℝ) ^ (D.eta * b)) *
        completeQuotientWeight (R := D.R) J := by
  apply (D.carrier N).survivingEpiCount_le_of_intrinsic J
    (D.Accepted b N) (D.accept_inverse b N J)
  exact (D.topFamily b N).acceptedEpi_card_le_ownerCapacity
    (D.carrier N) D.R J (D.Accepted b N) (D.select b N J)
      (D.C b N) D.eta (D.joint_capacity b N J)

end PreE7RefinedCapacitySourceData

/-- Install a multiplicative refined-capacity construction in the common
earlier-owner catalogue. -/
noncomputable def
    PreE7EarlierActionComparatorCertificate.ofRefinedCapacity
    {family : PreE7NoPairNoC3EarlierOwnerFamily}
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (D : PreE7RefinedCapacitySourceData family w i) :
    PreE7EarlierActionComparatorCertificate family w i where
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
  broad_axis_envelope := by
    intro b N J
    simpa only [zero_mul, add_zero] using D.broad_axis_envelope b N J

/-- Refined-capacity source data with a separate source-independent additive
tail.  Only the main branch is transported through the reversible carrier;
the tail retains its direct literal-axis estimate. -/
structure PreE7RefinedCapacityAdditiveSourceData
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  template_eq : family.template = .refinedCapacity
  R : Type
  [groupR : Group R]
  [finiteR : Finite R]
  v : ℕ
  action : R →* Equiv.Perm (Fin v)
  action_injective : Function.Injective action
  C : ℕ → {N : Subgroup (preE7NonPairAction w i) // N.Normal} → ℝ
  tailCoefficient :
    ℕ → {N : Subgroup (preE7NonPairAction w i) // N.Normal} → ℝ
  eta : ℝ
  delta : ℝ
  cutoff : ℝ
  alpha : ℝ
  theta : ℝ
  alpha_eq : alpha = eta + cutoff
  coefficient_nonneg : ∀ b N, 0 ≤ C b N
  tail_nonneg : ∀ b N, 0 ≤ tailCoefficient b N
  Main : ∀ b (_N : {N : Subgroup
    (preE7NonPairAction w i) // N.Normal}),
      Subgroup (preE7NonPairAction w i × Equiv.Perm (Fin b)) → Prop
  Tail : ∀ b (_N : {N : Subgroup
    (preE7NonPairAction w i) // N.Normal}),
      Subgroup (preE7NonPairAction w i × Equiv.Perm (Fin b)) → Prop
  cover : ∀ b N (J : Subgroup (Equiv.Perm (Fin b)))
      (beta : GroupEpimorphism J (preE7NonPairAction w i ⧸ N.1)),
    preE7NoPairNoC3BroadActionPredicate w i b
        (fusionFullGoursatEncode N J beta).1 →
      Main b N (fusionFullGoursatEncode N J beta).1 ∨
        Tail b N (fusionFullGoursatEncode N J beta).1
  carrier : ∀ N, FusionAxisCarrier (preE7NonPairAction w i) N
  Accepted : ∀ b N,
    Subgroup ((carrier N).checked.carrier × Equiv.Perm (Fin b)) → Prop
  accept_inverse : ∀ b N (J : Subgroup (Equiv.Perm (Fin b)))
      (gamma : GroupEpimorphism J (carrier N).checked.quotient),
    (carrier N).checked.carrierInverseSurvival
        (carrier N).source_eq (Main b N)
        (fusionQuotientGraph (carrier N).checked.beta J gamma.1) →
      Accepted b N
        (fusionQuotientGraph (carrier N).checked.beta J gamma.1)
  topFamily : ∀ _b N, AxisYonedaTopFamily (carrier N) R
  select : ∀ b N (J : Subgroup (Equiv.Perm (Fin b))),
    FusionCarrierAcceptedEpi (carrier N).checked J (Accepted b N) →
      (topFamily b N).Index
  main_joint_capacity : ∀ b N (J : Subgroup (Equiv.Perm (Fin b))),
    ((∑ s : (topFamily b N).Index,
      ((topFamily b N).tower s).tower.capacity J : ℕ) : ℝ) ≤
        C b N * (2 : ℝ) ^ (eta * b)
  tail_envelope : ∀ b N (J : Subgroup (Equiv.Perm (Fin b))),
    fusionSurvivingEpiCount (preE7NonPairAction w i) (Tail b N) N J ≤
      tailCoefficient b N * (2 : ℝ) ^ (theta * b)

attribute [instance]
  PreE7RefinedCapacityAdditiveSourceData.groupR
  PreE7RefinedCapacityAdditiveSourceData.finiteR

namespace PreE7RefinedCapacityAdditiveSourceData

variable {family : PreE7NoPairNoC3EarlierOwnerFamily}
  {w : ℕ} {i : PreE7NonPairActionClass w}
  (D : PreE7RefinedCapacityAdditiveSourceData family w i)

/-- The carrier/Yoneda incidence for the main half of the additive split. -/
theorem main_axis_envelope
    (b : ℕ)
    (N : {N : Subgroup (preE7NonPairAction w i) // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount (preE7NonPairAction w i) (D.Main b N) N J ≤
      (D.C b N * (2 : ℝ) ^ (D.eta * b)) *
        completeQuotientWeight (R := D.R) J := by
  apply (D.carrier N).survivingEpiCount_le_of_intrinsic J
    (D.Accepted b N) (D.accept_inverse b N J)
  exact (D.topFamily b N).acceptedEpi_card_le_ownerCapacity
    (D.carrier N) D.R J (D.Accepted b N) (D.select b N J)
      (D.C b N) D.eta (D.main_joint_capacity b N J)

end PreE7RefinedCapacityAdditiveSourceData

/-- Install the refined-capacity main branch and its genuine additive tail in
the common earlier-owner certificate. -/
noncomputable def
    PreE7EarlierActionComparatorCertificate.ofRefinedCapacityAdditive
    {family : PreE7NoPairNoC3EarlierOwnerFamily}
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (D : PreE7RefinedCapacityAdditiveSourceData family w i) :
    PreE7EarlierActionComparatorCertificate family w i where
  R := D.R
  groupR := D.groupR
  finiteR := D.finiteR
  v := D.v
  action := D.action
  action_injective := D.action_injective
  C := D.C
  tailCoefficient := D.tailCoefficient
  eta := D.eta
  delta := D.delta
  cutoff := D.cutoff
  alpha := D.alpha
  theta := D.theta
  alpha_eq := D.alpha_eq
  coefficient_nonneg := D.coefficient_nonneg
  tail_nonneg := D.tail_nonneg
  broad_axis_envelope := by
    intro b N J
    have hsplit := fusionSurvivingEpiCount_le_add_of_cover
      (preE7NonPairAction w i)
      (preE7NoPairNoC3BroadActionPredicate w i b)
      (D.Main b N) (D.Tail b N) N J (D.cover b N J)
    exact hsplit.trans
      (add_le_add (D.main_axis_envelope b N J) (D.tail_envelope b N J))

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
