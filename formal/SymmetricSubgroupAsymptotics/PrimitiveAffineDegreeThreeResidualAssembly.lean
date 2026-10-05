import SymmetricSubgroupAsymptotics.PrimitiveAffineFinalPartialAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixPublishedClassification
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeRegularSixSource

/-!
# Assembly of the degree-three affine residual lane

The numerical exhaustion leaves seven block counts.  The two-block cell is
the published degree-six affine slice; the eight-block cell was already
removed by the direct translation owner.  At the other counts a regular
`C3` component was already removed except at six blocks.  Thus the only
construction inputs below are precisely

* the sharp regular-`C3`, six-block endpoint; and
* the signed-quotient endpoint for an exact natural `S3` component.

This file proves the exhaustive dispatch.  It introduces no classification
or counting assumption; the two endpoint function types are temporary
construction boundaries to be instantiated by the adjacent checked files.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- The sole regular-component cell not removed by the earlier cyclic
translation owners. -/
abbrev DegreeThreeRegularSixResidualSource :=
  ∀ {w : ℕ} (U : PreE7NonPairActionClass w) (_hw : 5 ≤ w)
    (basePoint : Fin w)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre),
    ImprimitiveAffineResidualCapacityException
        (Nat.card block.Fibre) (Nat.card block.Points)
        (Nat.card block.Component) →
    Nat.card block.Fibre = 3 →
    Nat.card block.Points = 6 →
    Nat.card block.Component ∣ 3 →
    PreE7RankTailSourceOrYonedaTopData w U

/-- The exact-local-`S3` signed-quotient endpoint.  The disjunction is the
literal residual block-count list after the two-block published slice and
the direct eight-block translation cell have been removed. -/
abbrev DegreeThreeExactS3ResidualSource :=
  ∀ {w : ℕ} (U : PreE7NonPairActionClass w) (_hw : 5 ≤ w)
    (basePoint : Fin w)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre),
    ImprimitiveAffineResidualCapacityException
        (Nat.card block.Fibre) (Nat.card block.Points)
        (Nat.card block.Component) →
    Nat.card block.Fibre = 3 →
    (Nat.card block.Points = 3 ∨ Nat.card block.Points = 4 ∨
      Nat.card block.Points = 6 ∨ Nat.card block.Points = 12 ∨
      Nat.card block.Points = 18) →
    Nat.card block.Component = 6 →
    PreE7RankTailSourceOrYonedaTopData w U

/-- Exhaust the entire degree-three residual menu from the two concrete
signed-quotient endpoints and Butler--McKay's published degree-six slice. -/
noncomputable def degreeThreeResidualSource_of_endpoints
    (hKP : KovacsPraegerAbelianizationBound)
    (classification : PublishedDegreeSixThreeByTwoAffineClassification)
    (regularSix : DegreeThreeRegularSixResidualSource)
    (exactS3 : DegreeThreeExactS3ResidualSource) :
    PrimitiveAffineResidualDegreeSource 3 := by
  intro w U hw basePoint block P hres hr
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hr]
      norm_num)
  refine Classical.choice ?_
  cases hcap : hres.toCapacityException with
  | degreeTwo hr' hs => omega
  | degreeFour hr' hs => omega
  | degreeFive hr' hs => omega
  | degreeEight hr' hs => omega
  | degreeNine hr' hs => omega
  | degreeSixteen hr' hs => omega
  | degreeThree hr' hs =>
      rcases hs with hs2 | hs3 | hs4 | hs6 | hs8 | hs12 | hs18
      · have hw6 : w = 6 := by
          simpa only [hr, hs2] using width_eq block
        subst w
        exact ⟨degreeSixSource_of_publishedClassification hKP classification
          U basePoint block P hr hs2⟩
      · by_cases hcomponent : Nat.card block.Component ∣ 3
        · exact False.elim (hres.not_degreeThreeCyclic
            ⟨hr, Or.inl hs3, hcomponent⟩)
        · exact ⟨exactS3 U hw basePoint block P hres hr (Or.inl hs3)
            (degreeThree_component_card_eq_six_of_not_dvd_three
              block P hr hcomponent)⟩
      · by_cases hcomponent : Nat.card block.Component ∣ 3
        · exact False.elim (hres.not_degreeThreeCyclic
            ⟨hr, Or.inr (Or.inl hs4), hcomponent⟩)
        · exact ⟨exactS3 U hw basePoint block P hres hr
            (Or.inr (Or.inl hs4))
            (degreeThree_component_card_eq_six_of_not_dvd_three
              block P hr hcomponent)⟩
      · by_cases hcomponent : Nat.card block.Component ∣ 3
        · exact ⟨regularSix U hw basePoint block P hres hr hs6 hcomponent⟩
        · exact ⟨exactS3 U hw basePoint block P hres hr
            (Or.inr (Or.inr (Or.inl hs6)))
            (degreeThree_component_card_eq_six_of_not_dvd_three
              block P hr hcomponent)⟩
      · exact False.elim (hres.not_directTranslation
          (Or.inl ⟨hr, hs8⟩))
      · by_cases hcomponent : Nat.card block.Component ∣ 3
        · exact False.elim (hres.not_degreeThreeCyclic
            ⟨hr, Or.inr (Or.inr (Or.inl hs12)), hcomponent⟩)
        · exact ⟨exactS3 U hw basePoint block P hres hr
            (Or.inr (Or.inr (Or.inr (Or.inl hs12))))
            (degreeThree_component_card_eq_six_of_not_dvd_three
              block P hr hcomponent)⟩
      · by_cases hcomponent : Nat.card block.Component ∣ 3
        · exact False.elim (hres.not_degreeThreeCyclic
            ⟨hr, Or.inr (Or.inr (Or.inr hs18)), hcomponent⟩)
        · exact ⟨exactS3 U hw basePoint block P hres hr
            (Or.inr (Or.inr (Or.inr (Or.inr hs18))))
            (degreeThree_component_card_eq_six_of_not_dvd_three
              block P hr hcomponent)⟩

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
