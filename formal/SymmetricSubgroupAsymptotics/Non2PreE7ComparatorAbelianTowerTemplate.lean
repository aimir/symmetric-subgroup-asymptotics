import SymmetricSubgroupAsymptotics.FusionCarrierAnnihilatorYonedaIncidence
import SymmetricSubgroupAsymptotics.Non2PreE7NoPairNoC3EarlierComparators

/-!
# Comparator certificates from abelian Yoneda towers

This file is the common proof template for the pre-`E7` families whose
literal quotient is reduced through abelian extension layers to a fixed
finite comparator.  It works directly on the original quotient `U/N`; no
replacement carrier, owner-order exclusion, or source change is used.

The retained restriction flags and the remaining Yoneda fibres are charged
together by `AbelianYonedaTower.capacity`.  A family instance therefore has
to prove one numerical joint-capacity inequality, rather than independent
worst-case flag and fibre estimates.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A fixed quotient top and an abelian Yoneda tower from one literal
original normal quotient `U/N` to a quotient of the comparator `R`. -/
structure FusionQuotientAbelianYonedaTower
    {w : ℕ} (U : Subgroup (Equiv.Perm (Fin w)))
    (N : {N : Subgroup U // N.Normal})
    (R : Type) [Group R] where
  M : Subgroup R
  [normal : M.Normal]
  top : (U ⧸ N.1) →* R ⧸ M
  tower : AbelianYonedaTower (R ⧸ M) (U ⧸ N.1) top

attribute [instance] FusionQuotientAbelianYonedaTower.normal

/-- Direct retained-cell incidence on the literal original quotient.  This
is the carrier-free form needed by an earlier-family action certificate. -/
theorem fusionSurvivingEpiCount_le_abelianYonedaTower
    {w b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (N : {N : Subgroup U // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b)))
    {R : Type} [Group R] [Finite R]
    (T : FusionQuotientAbelianYonedaTower U N R) :
    fusionSurvivingEpiCount U P N J ≤
      (T.tower.capacity J : ℝ) * completeQuotientWeight (R := R) J := by
  let X := {β : GroupEpimorphism J (U ⧸ N.1) //
    P (fusionFullGoursatEncode N J β).1}
  let f : X → CompleteQuotientMap J R × T.tower.Flag J := fun β =>
    (fusionCarrierTopQuotientMap T.M T.top T.tower.top_surjective β.1,
      T.tower.flag J β.1.1)
  have hfibre : ∀ y : CompleteQuotientMap J R × T.tower.Flag J,
      Nat.card {β : X // f β = y} ≤ T.tower.bound := by
    intro y
    refine fusionCarrierTopCell_fibre_card_le T.M T.top
      T.tower.top_surjective (fun β : X => β.1)
      (fun β : X => T.tower.flag J β.1.1) T.tower.bound ?_ y
    intro top a
    refine le_trans (Nat.card_le_card_of_injective
      (fun β => (⟨β.1.1, β.2⟩ :
        {γ : GroupEpimorphism J (U ⧸ N.1) //
          T.top.comp γ.1 = top ∧ T.tower.flag J γ.1 = a})) ?_)
      (T.tower.fibre_card_le J top a)
    intro β β' hβ
    have hβ' := congrArg Subtype.val hβ
    exact Subtype.ext (Subtype.ext hβ')
  have hnat := natCard_le_uniformFiber_mul f T.tower.bound hfibre
  rw [Nat.card_prod, completeQuotientMap_card] at hnat
  have hreal :
      (Nat.card X : ℝ) ≤
        (Nat.card (T.tower.Flag J) * T.tower.bound : ℕ) *
          completeQuotientWeight (R := R) J := by
    unfold completeQuotientWeight
    exact_mod_cast (by
      calc
        Nat.card X ≤ T.tower.bound *
            (completeQuotientCount (R := R) J *
              Nat.card (T.tower.Flag J)) := hnat
        _ = (Nat.card (T.tower.Flag J) * T.tower.bound) *
            completeQuotientCount (R := R) J := by ring)
  unfold fusionSurvivingEpiCount
  change (Nat.card X : ℝ) ≤ _
  refine hreal.trans (mul_le_mul_of_nonneg_right ?_
    (completeQuotientWeight_nonneg (R := R) J))
  exact_mod_cast T.tower.card_flag_mul_bound_le_capacity J

namespace Non2UnipotentPrefixFiniteMenu

/-- Family-independent source data for the comparator/abelian-layer
template.  Each normal axis retains its actual tower.  The sole numerical
input is the joint bound for the tower capacity. -/
structure PreE7ComparatorAbelianTowerSourceData
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  template_eq : family.template = .comparatorAbelianTower
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
  tower : ∀ _b N,
    FusionQuotientAbelianYonedaTower (preE7NonPairAction w i) N R
  joint_capacity : ∀ b N (J : Subgroup (Equiv.Perm (Fin b))),
    (((tower b N).tower.capacity J : ℕ) : ℝ) ≤
      C b N * (2 : ℝ) ^ (eta * b)

attribute [instance]
  PreE7ComparatorAbelianTowerSourceData.groupR
  PreE7ComparatorAbelianTowerSourceData.finiteR

/-- Every comparator/abelian-layer source datum gives the common earlier
action certificate.  The pure cold tail is zero; families with a genuine
additive exceptional branch extend this multiplicative core separately. -/
noncomputable def PreE7EarlierActionComparatorCertificate.ofAbelianYonedaTowers
    {family : PreE7NoPairNoC3EarlierOwnerFamily}
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (D : PreE7ComparatorAbelianTowerSourceData family w i) :
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
    have htower := fusionSurvivingEpiCount_le_abelianYonedaTower
      (preE7NonPairAction w i)
      (preE7NoPairNoC3BroadActionPredicate w i b) N J (D.tower b N)
    have hcap := D.joint_capacity b N J
    calc
      fusionSurvivingEpiCount (preE7NonPairAction w i)
          (preE7NoPairNoC3BroadActionPredicate w i b) N J ≤
          (((D.tower b N).tower.capacity J : ℕ) : ℝ) *
            completeQuotientWeight (R := D.R) J := htower
      _ ≤ (D.C b N * (2 : ℝ) ^ (D.eta * b)) *
            completeQuotientWeight (R := D.R) J :=
        mul_le_mul_of_nonneg_right hcap
          (completeQuotientWeight_nonneg (R := D.R) J)
      _ = (D.C b N * (2 : ℝ) ^ (D.eta * b)) *
            completeQuotientWeight (R := D.R) J +
          0 * (2 : ℝ) ^ (D.theta * b) := by ring

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
