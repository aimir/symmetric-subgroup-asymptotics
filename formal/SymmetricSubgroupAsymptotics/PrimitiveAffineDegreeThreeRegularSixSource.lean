import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineTopTranslationSource

/-!
# The regular degree-three component at six blocks

When the actual degree-three affine component is its regular translation
group, quotienting the literal translation intersection leaves exactly the
faithful action on the block top.  This file records that structural
identification before the sharp two-generator estimate for the resulting
six-block permutation module is applied.

No abstract action replaces the block system: the terminal action below is
`topQuotientAction block P` on the actual set of blocks.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- In local degree three, divisibility of the actual component order by
three forces the component to be precisely its regular translation group.
This is extracted from the literal affine complement factorization. -/
theorem degreeThree_component_card_eq_translation_of_dvd_three
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component ∣ 3) :
    Nat.card block.Component = Nat.card P.V := by
  have hV : Nat.card P.V = 3 :=
    (P.card_eq (origin block)).trans hr
  have hthree : 3 ∣ Nat.card block.Component := by
    have hfactor := (P.isComplement'_complement (origin block)).card_mul
    rw [← hfactor, hV]
    exact dvd_mul_right 3 _
  have hle : Nat.card block.Component ≤ 3 :=
    Nat.le_of_dvd (by norm_num) hcomponent
  have hge : 3 ≤ Nat.card block.Component :=
    Nat.le_of_dvd (Nat.card_pos (α := block.Component)) hthree
  rw [hV]
  omega

/-- Consequently the local complement quotient is trivial. -/
theorem degreeThree_localQuotient_eq_one_of_component_dvd_three
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component ∣ 3) :
    ∀ q : LocalQuotient block P, q = 1 :=
  localQuotient_eq_one_of_component_card_eq_translation block P
    (degreeThree_component_card_eq_translation_of_dvd_three
      block P hr hcomponent)

/-- The signed quotient in the regular-component branch therefore acts
faithfully on the literal six-block top. -/
theorem degreeThree_regular_topQuotientAction_injective
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component ∣ 3) :
    Function.Injective (topQuotientAction block P) :=
  topQuotientAction_injective block P
    (degreeThree_localQuotient_eq_one_of_component_dvd_three
      block P hr hcomponent)

/-- The exact one-layer envelope ending at the actual block top.  Its
terminal permutation degree is `Nat.card block.Points`; in the residual
branch below this is six. -/
noncomputable def degreeThreeRegularTopEnvelope
    (H : ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart)
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component ∣ 3) :
    RelativeCompleteSourceEnvelope (preE7NonPairAction w U) :=
  topTranslationLayerEnvelope block P
    (degreeThree_localQuotient_eq_one_of_component_dvd_three
      block P hr hcomponent) H

@[simp] theorem degreeThreeRegularTopEnvelope_v
    (H : ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart)
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component ∣ 3) :
    (degreeThreeRegularTopEnvelope block P H hr hcomponent).v =
      Nat.card block.Points := rfl

/-- Construction boundary for the sole regular-component residual cell.
The only missing field here is the sharp numerical margin for the actual
six-block permutation module; all group and action data are already fixed. -/
structure DegreeThreeRegularSixSourceData
    (H : ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 6)
    (hcomponent : Nat.card block.Component ∣ 3) : Type where
  margin : RelativeCompleteSourceEnvelope.PreE7Margin
    (degreeThreeRegularTopEnvelope block P H hr hcomponent)

namespace DegreeThreeRegularSixSourceData

variable
  {H : ElementaryLayerJointCapacityBound
    (elementaryChart block P).p
    (QuotientGroup.mk' (E block P))
    (QuotientGroup.mk'_surjective (E block P))
    (elementaryChart block P).quotientRepresentation
    (elementaryChart block P).originalKernelChart}
  {hr : Nat.card block.Fibre = 3}
  {hs : Nat.card block.Points = 6}
  {hcomponent : Nat.card block.Component ∣ 3}

/-- Install the sharp six-block margin as the final ambient source. -/
noncomputable def source
    (D : DegreeThreeRegularSixSourceData block P H hr hs hcomponent) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  RelativeCompleteSourceEnvelope.toRankTailSourceOrYonedaTopOfMargin
    .acert (degreeThreeRegularTopEnvelope block P H hr hcomponent) D.margin

end DegreeThreeRegularSixSourceData

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
