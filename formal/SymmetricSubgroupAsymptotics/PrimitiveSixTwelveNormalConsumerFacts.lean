import SymmetricSubgroupAsymptotics.PrimitiveSixTwelveExactProfileFromComposition

/-! A proved internal consumer boundary replaces the unused116-row
locator in the many original degree6/12 joint factories. These fields are
actual group/profile facts, and the constructor proves them from the
already-retained composition correspondence and ordinary simple-index
bound. No additional literature premise is introduced. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

structure PrimitiveSixTwelveNormalConsumerFacts : Prop where
  quotient_card : ∀ (G : Type) [Group G] [Finite G] (r : ℕ)
    [MulAction G (Fin r)] [FaithfulSMul G (Fin r)] [MulAction.IsPreprimitive G (Fin r)]
    (D : ExactPrimitiveSemisimpleOuterLogProfile G r),r=6 ∨ r=12 →
      Nat.card (G⧸D.profile.E)≤2
  six_five_dvd : ∀ (G : Type) [Group G] [Finite G]
    [MulAction G (Fin 6)] [FaithfulSMul G (Fin 6)] [MulAction.IsPreprimitive G (Fin 6)]
    (D : ExactPrimitiveSemisimpleOuterLogProfile G 6),5∣Nat.card G

namespace PrimitiveSixTwelveNormalConsumerFacts

theorem of_composition
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) : PrimitiveSixTwelveNormalConsumerFacts where
  quotient_card := by
    intro G _ _ r _ _ _ D hr
    exact PrimitiveSixTwelveExactProfileFromComposition.socle_quotient_card_le_two
      D catalogue hindex hr
  six_five_dvd := by
    intro G _ _ _ _ _ D
    exact primitive_degreeSix_five_dvd_from_composition catalogue (X := Fin 6) (by simp)

/-- Compatibility for historical callers retaining the stronger locator.
The active endpoint instead uses `of_composition`. -/
theorem of_boundedCatalogue (catalogue : PublishedBoundedPrimitiveCatalogueClassification) :
    PrimitiveSixTwelveNormalConsumerFacts where
  quotient_card := by
    intro G _ _ r _ _ _ D hr
    rcases hr with rfl|rfl
    · exact PrimitiveSixExactProfileNormalGenerators.socle_quotient_card_le_two D catalogue
    · exact PrimitiveTwelveExactProfileNormalGenerators.socle_quotient_card_le_two D catalogue
  six_five_dvd := by
    intro G _ _ _ _ _ D
    exact PrimitiveSixExactProfileNormalGenerators.five_dvd_card D catalogue

variable (facts : PrimitiveSixTwelveNormalConsumerFacts)
    {G : Type} [Group G] [Finite G] {r : ℕ}
    [MulAction G (Fin r)] [FaithfulSMul G (Fin r)] [MulAction.IsPreprimitive G (Fin r)]
    (D : ExactPrimitiveSemisimpleOuterLogProfile G r)

include facts D

theorem socle_quotient_card_le_two (hr : r=6 ∨ r=12) : Nat.card (G⧸D.profile.E)≤2 :=
  facts.quotient_card G r D hr

theorem normal_total (hr : r=6 ∨ r=12)
    (A B : Subgroup G) (hA : A.Normal) (hB : B.Normal) : A≤B ∨ B≤A :=
  PrimitiveSixExactProfileNormalGenerators.normal_total_of_unique_minimal_small_quotient
    D.profile.E (D.oneFactor_socle_le
      (PrimitiveSixTwelveExactProfileFromComposition.factorCount_eq_one D hr))
    (facts.socle_quotient_card_le_two D hr) A B hA hB

theorem normal_generating_singletons (hr : r=6 ∨ r=12)
    (N : Subgroup G) (hN : N.Normal) :
    ∃ x : Fin 1→G,Subgroup.normalClosure (Set.range x)=N :=
  normal_generating_singletons_of_finite_normal_total (facts.normal_total D hr) N hN

theorem quotientSocle_one (hr : r=6 ∨ r=12)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G⧸N) 1 :=
  quotientSocleNormalGeneratorBound_one_of_normal_total (facts.normal_total D hr) N

end PrimitiveSixTwelveNormalConsumerFacts
end SymmetricSubgroupAsymptotics
