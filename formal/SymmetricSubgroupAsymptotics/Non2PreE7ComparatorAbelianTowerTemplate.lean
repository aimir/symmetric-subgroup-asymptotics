import SymmetricSubgroupAsymptotics.FusionCarrierAnnihilatorYonedaIncidence
import SymmetricSubgroupAsymptotics.Non2PreE7NoPairNoC3EarlierComparators
import SymmetricSubgroupAsymptotics.Non2PreE7PaddedCertificateNumerics

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

/-- Split a literal surviving-epimorphism family across two exhaustive local
branches.  No disjointness is needed: choosing the first branch when both
hold gives an injection into the disjoint sum of the two counted families. -/
theorem fusionSurvivingEpiCount_le_add_of_cover
    {w b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P Main Tail : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (N : {N : Subgroup U // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b)))
    (cover : ∀ β : GroupEpimorphism J (U ⧸ N.1),
      P (fusionFullGoursatEncode N J β).1 →
        Main (fusionFullGoursatEncode N J β).1 ∨
          Tail (fusionFullGoursatEncode N J β).1) :
    fusionSurvivingEpiCount U P N J ≤
      fusionSurvivingEpiCount U Main N J +
        fusionSurvivingEpiCount U Tail N J := by
  let X := {β : GroupEpimorphism J (U ⧸ N.1) //
    P (fusionFullGoursatEncode N J β).1}
  let Y := {β : GroupEpimorphism J (U ⧸ N.1) //
    Main (fusionFullGoursatEncode N J β).1}
  let Z := {β : GroupEpimorphism J (U ⧸ N.1) //
    Tail (fusionFullGoursatEncode N J β).1}
  let f : X → Y ⊕ Z := fun β =>
    if h : Main (fusionFullGoursatEncode N J β.1).1 then
      Sum.inl ⟨β.1, h⟩
    else
      Sum.inr ⟨β.1, (cover β.1 β.2).resolve_left h⟩
  let underlying : Y ⊕ Z → GroupEpimorphism J (U ⧸ N.1) :=
    Sum.elim Subtype.val Subtype.val
  have h_underlying (β : X) : underlying (f β) = β.1 := by
    simp only [f, underlying]
    split <;> rfl
  have hf : Function.Injective f := by
    intro β γ hβγ
    apply Subtype.ext
    have hu := congrArg underlying hβγ
    exact (h_underlying β).symm.trans (hu.trans (h_underlying γ))
  have hnat : Nat.card X ≤ Nat.card Y + Nat.card Z := by
    simpa only [Nat.card_sum] using Nat.card_le_card_of_injective f hf
  unfold fusionSurvivingEpiCount
  change (Nat.card X : ℝ) ≤ (Nat.card Y : ℝ) + (Nat.card Z : ℝ)
  exact_mod_cast hnat

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
  sourceDegree : ℕ
  sourceDegree_two : 2 ≤ sourceDegree
  action : R →* Equiv.Perm (Fin sourceDegree)
  action_injective : Function.Injective action
  C : ℕ → {N : Subgroup (preE7NonPairAction w i) // N.Normal} → ℝ
  eta : ℝ
  eta_nonneg : 0 ≤ eta
  exponent_margin : preE7CharacterRho * w ≤
    ((evenWidth w : ℝ) - sourceDegree) / 8 - eta
  coefficient_nonneg : ∀ b N, 0 ≤ C b N
  coefficient_total_bound : ∀ b,
    fusionAxisEnvelopeTotal (preE7NonPairAction w i) (C b) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  tower : ∀ _b N,
    FusionQuotientAbelianYonedaTower (preE7NonPairAction w i) N R
  joint_capacity : ∀ b N (J : Subgroup (Equiv.Perm (Fin b))),
    (((tower b N).tower.capacity J : ℕ) : ℝ) ≤
      C b N * (2 : ℝ) ^ (eta * b)

attribute [instance]
  PreE7ComparatorAbelianTowerSourceData.groupR
  PreE7ComparatorAbelianTowerSourceData.finiteR

namespace PreE7ComparatorAbelianTowerSourceData

variable {family : PreE7NoPairNoC3EarlierOwnerFamily}
  {w : ℕ} {i : PreE7NonPairActionClass w}
  (D : PreE7ComparatorAbelianTowerSourceData family w i)

def degree : ℕ :=
  paddedComparatorDegree preE7CharacterRho D.sourceDegree w

def delta : ℝ :=
  paddedComparatorDelta preE7CharacterRho D.eta D.sourceDegree w

def cutoff : ℝ := (D.degree : ℝ) / 8 + D.delta / 2

def alpha : ℝ := D.eta + D.cutoff

def paddedAction : D.R →* Equiv.Perm (Fin D.degree) :=
  (characterComparatorPadHom (le_max_left _ _)).comp D.action

theorem paddedAction_injective : Function.Injective D.paddedAction :=
  (characterComparatorPadHom_injective _).comp D.action_injective

theorem entryParameters :
    PreE7CharacterEntryParameters preE7CharacterRho w D.degree D.eta D.delta
      D.cutoff D.alpha 0 := by
  simpa [degree, delta, cutoff, alpha] using
    (preE7Padded_entryParameters (w := w) (v0 := D.sourceDegree)
      (eta := D.eta) D.eta_nonneg D.sourceDegree_two D.exponent_margin)

end PreE7ComparatorAbelianTowerSourceData

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
  v := D.degree
  action := D.paddedAction
  action_injective := D.paddedAction_injective
  C := D.C
  tailCoefficient := fun _ _ => 0
  eta := D.eta
  delta := D.delta
  cutoff := D.cutoff
  alpha := D.alpha
  theta := 0
  alpha_eq := rfl
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
          0 * (2 : ℝ) ^ ((0 : ℝ) * b) := by ring

/-- The additive version of the tower template.  A family instance provides
an exhaustive main/tail split on the literal broad source.  The main branch
is controlled by the retained abelian tower, while the second branch is paid
as a pure cold row and never forced through a complete-quotient moment. -/
structure PreE7ComparatorAbelianTowerAdditiveSourceData
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  template_eq : family.template = .comparatorAbelianTower
  R : Type
  [groupR : Group R]
  [finiteR : Finite R]
  sourceDegree : ℕ
  sourceDegree_two : 2 ≤ sourceDegree
  action : R →* Equiv.Perm (Fin sourceDegree)
  action_injective : Function.Injective action
  C : ℕ → {N : Subgroup (preE7NonPairAction w i) // N.Normal} → ℝ
  tailCoefficient :
    ℕ → {N : Subgroup (preE7NonPairAction w i) // N.Normal} → ℝ
  eta : ℝ
  eta_nonneg : 0 ≤ eta
  exponent_margin : preE7CharacterRho * w ≤
    ((evenWidth w : ℝ) - sourceDegree) / 8 - eta
  theta : ℝ
  tail_gap : theta ≤ preE7CharacterWindow w
  coefficient_nonneg : ∀ b N, 0 ≤ C b N
  tail_nonneg : ∀ b N, 0 ≤ tailCoefficient b N
  coefficient_total_bound : ∀ b,
    fusionAxisEnvelopeTotal (preE7NonPairAction w i) (C b) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  tail_total_bound : ∀ b,
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
        (tailCoefficient b) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  Main : ∀ b (_N : {N : Subgroup
    (preE7NonPairAction w i) // N.Normal}),
      Subgroup (preE7NonPairAction w i × Equiv.Perm (Fin b)) → Prop
  Tail : ∀ b (_N : {N : Subgroup
    (preE7NonPairAction w i) // N.Normal}),
      Subgroup (preE7NonPairAction w i × Equiv.Perm (Fin b)) → Prop
  cover : ∀ b N (J : Subgroup (Equiv.Perm (Fin b)))
      (β : GroupEpimorphism J (preE7NonPairAction w i ⧸ N.1)),
    preE7NoPairNoC3BroadActionPredicate w i b
        (fusionFullGoursatEncode N J β).1 →
      Main b N (fusionFullGoursatEncode N J β).1 ∨
        Tail b N (fusionFullGoursatEncode N J β).1
  tower : ∀ _b N,
    FusionQuotientAbelianYonedaTower (preE7NonPairAction w i) N R
  main_joint_capacity : ∀ b N (J : Subgroup (Equiv.Perm (Fin b))),
    (((tower b N).tower.capacity J : ℕ) : ℝ) ≤
      C b N * (2 : ℝ) ^ (eta * b)
  tail_envelope : ∀ b N (J : Subgroup (Equiv.Perm (Fin b))),
    fusionSurvivingEpiCount (preE7NonPairAction w i) (Tail b N) N J ≤
      tailCoefficient b N * (2 : ℝ) ^ (theta * b)

attribute [instance]
  PreE7ComparatorAbelianTowerAdditiveSourceData.groupR
  PreE7ComparatorAbelianTowerAdditiveSourceData.finiteR

namespace PreE7ComparatorAbelianTowerAdditiveSourceData

variable {family : PreE7NoPairNoC3EarlierOwnerFamily}
  {w : ℕ} {i : PreE7NonPairActionClass w}
  (D : PreE7ComparatorAbelianTowerAdditiveSourceData family w i)

def degree : ℕ :=
  paddedComparatorDegree preE7CharacterRho D.sourceDegree w

def delta : ℝ :=
  paddedComparatorDelta preE7CharacterRho D.eta D.sourceDegree w

def cutoff : ℝ := (D.degree : ℝ) / 8 + D.delta / 2

def alpha : ℝ := D.eta + D.cutoff

def paddedAction : D.R →* Equiv.Perm (Fin D.degree) :=
  (characterComparatorPadHom (le_max_left _ _)).comp D.action

theorem paddedAction_injective : Function.Injective D.paddedAction :=
  (characterComparatorPadHom_injective _).comp D.action_injective

theorem entryParameters :
    PreE7CharacterEntryParameters preE7CharacterRho w D.degree D.eta D.delta
      D.cutoff D.alpha D.theta := by
  let P := preE7Padded_entryParameters (w := w) (v0 := D.sourceDegree)
    (eta := D.eta) D.eta_nonneg D.sourceDegree_two D.exponent_margin
  exact
    { delta_nonneg := P.delta_nonneg
      degree_pos := P.degree_pos
      ratio := P.ratio
      degree_upper := P.degree_upper
      delta_lower := P.delta_lower
      hot_margin := P.hot_margin
      threshold_eq := P.threshold_eq
      delta_upper := P.delta_upper
      degree_lower := P.degree_lower
      degree_width := P.degree_width
      cold_slope := P.cold_slope
      cold_gap := P.cold_gap
      tail_gap := D.tail_gap }

end PreE7ComparatorAbelianTowerAdditiveSourceData

/-- Install an exhaustive tower-plus-cold-tail split in the common earlier
action certificate. -/
noncomputable def
    PreE7EarlierActionComparatorCertificate.ofAbelianYonedaTowersAdditive
    {family : PreE7NoPairNoC3EarlierOwnerFamily}
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (D : PreE7ComparatorAbelianTowerAdditiveSourceData family w i) :
    PreE7EarlierActionComparatorCertificate family w i where
  R := D.R
  groupR := D.groupR
  finiteR := D.finiteR
  v := D.degree
  action := D.paddedAction
  action_injective := D.paddedAction_injective
  C := D.C
  tailCoefficient := D.tailCoefficient
  eta := D.eta
  delta := D.delta
  cutoff := D.cutoff
  alpha := D.alpha
  theta := D.theta
  alpha_eq := rfl
  coefficient_nonneg := D.coefficient_nonneg
  tail_nonneg := D.tail_nonneg
  broad_axis_envelope := by
    intro b N J
    have hsplit := fusionSurvivingEpiCount_le_add_of_cover
      (preE7NonPairAction w i)
      (preE7NoPairNoC3BroadActionPredicate w i b)
      (D.Main b N) (D.Tail b N) N J (D.cover b N J)
    have hmain0 := fusionSurvivingEpiCount_le_abelianYonedaTower
      (preE7NonPairAction w i) (D.Main b N) N J (D.tower b N)
    have hmain : fusionSurvivingEpiCount (preE7NonPairAction w i)
        (D.Main b N) N J ≤
        (D.C b N * (2 : ℝ) ^ (D.eta * b)) *
          completeQuotientWeight (R := D.R) J :=
      hmain0.trans (mul_le_mul_of_nonneg_right
        (D.main_joint_capacity b N J)
        (completeQuotientWeight_nonneg (R := D.R) J))
    exact hsplit.trans (add_le_add hmain (D.tail_envelope b N J))

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
