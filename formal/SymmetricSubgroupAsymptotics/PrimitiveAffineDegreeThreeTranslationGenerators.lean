import SymmetricSubgroupAsymptotics.ActualWreathAffineTernaryGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeNineZeroCore
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientSource

/-!
# Sharp generators for the retained degree-three translation image

The degree-nine files introduced the literal translation image, its pullback
inside the original elementary kernel, and the conversion from module
generators to ambient normal generators.  Those constructions are
degree-independent.  In local degree three the new Sylow-width generator
theorem gives the sharper budgets `1,2,4,6` at block counts `3,6,12,18`
before any finite S3 row is selected.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

private abbrev LiteralNormalAxis (G : Type) [Group G] :=
  {N : Subgroup G // N.Normal}

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The actual correlated ternary translation module has the canonical
integer width as a uniform generator bound. -/
theorem degreeThreeTranslationAmbient_uniform
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (i₀ : block.Points) :
    UniformSubrepresentationGeneratorBound
      (ActualWreathAffineCapacity.ambientRepresentation
        (initialState hTraceyPerm block) (localMap block P)
        (localTranslationChart block P))
      (ternaryWidthCore (Nat.card block.Points)
        ((Nat.card block.Points).factorization 3)) := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  have hpd := degreeThree_translation_prime_dim block P hr
  have h :=
    ActualWreathAffineCapacity.ambientTernary_uniformSubrepresentationGeneratorBound
      S (localMap block P) C hpd.1 hpd.2 i₀
  simpa only [S, C, Fintype.card_eq_nat_card] using h

/-- Every normal subgroup carried by the retained translation image has the
same sharp ternary-width normal-generator bound. -/
theorem degreeThreeTranslationCarried_normalGen_le
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (i₀ : block.Points)
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1)) [H.Normal]
    (hH : H ≤ degreeNineTranslationImage block P N) :
    MarkedC4.normalGen H ≤
      ternaryWidthCore (Nat.card block.Points)
        ((Nat.card block.Points).factorization 3) := by
  let L := degreeNineTranslationPreimage block P N H
  have hLgen : MarkedC4.normalGen L ≤
      ternaryWidthCore (Nat.card block.Points)
        ((Nat.card block.Points).factorization 3) := by
    apply normalGen_le_of_elementaryNormalSubrepresentation_comp_generated
      (E block P) (elementaryChart block P) L
      (degreeNineTranslationPreimage_le_translation block P N H)
    have huniform := degreeThreeTranslationAmbient_uniform
      block P hTraceyPerm hr i₀
    let M₀ := (elementaryChart block P).originalKernelChart
      |>.normalSubrepresentation (QuotientGroup.mk' (E block P))
        (QuotientGroup.mk'_surjective (E block P))
        (elementaryChart block P).quotientRepresentation L
    let M := ActualWreathAffineCapacity.subrepresentationComp
      (QuotientGroup.mk' (E block P))
      (elementaryChart block P).quotientRepresentation.ρ M₀
    have hM := huniform M
    simpa only [ActualWreathAffineCapacity.ambientRepresentation,
      initialState, localTranslationChart, elementaryChart,
      ActualWreathAffineCapacity.E,
      PermutationalWreathProduct.Compression.kernelElementaryChart,
      M, M₀] using hM
  rw [← degreeNineTranslationPreimage_map_eq block P N H hH]
  exact (MarkedC4.normalGen_map_le (QuotientGroup.mk' N.1)
    (QuotientGroup.mk'_surjective N.1) L).trans hLgen

/-- Specialization to the translation-carried sum of ambient minimal normal
factors. -/
theorem degreeThreeTranslationSoclePart_normalGen_le
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (i₀ : block.Points)
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    MarkedC4.normalGen (degreeNineTranslationSoclePart block P N) ≤
      ternaryWidthCore (Nat.card block.Points)
        ((Nat.card block.Points).factorization 3) :=
  degreeThreeTranslationCarried_normalGen_le block P hTraceyPerm hr i₀ N
    (degreeNineTranslationSoclePart block P N)
    (degreeNineTranslationSoclePart_le_image block P N)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
