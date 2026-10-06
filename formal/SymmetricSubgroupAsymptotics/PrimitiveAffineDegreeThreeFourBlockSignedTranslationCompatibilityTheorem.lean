import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockPairChartBitReflection
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockSignedTranslationCompatibility
import SymmetricSubgroupAsymptotics.PrimitiveAffineTranslationSubmoduleTopKernelAction

/-!
# The literal signed-translation compatibility theorem

The compatibility record used by the four-character projector is not an
extra hypothesis.  The quotient-wreath coordinate formula gives its local
linear action, while the literal pair-chart reflection identifies the same
coordinate's local scalar with the retained sign bit.
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

/-- Quotient conjugation on the actual correlated translation submodule is
the diagonal action read from the same literal four-pair-frame bits. -/
noncomputable def degreeThreeFourBlockSignedTranslationCompatibility
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :
    DegreeThreeFourBlockSignedTranslationCompatibility
      block P hr hs hcomponent where
  diagonal_action := by
    dsimp only
    let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
    let e := degreeThreeFourBlockIndexEquiv block hs
    intro k v
    funext i
    let q := C.sourceEquiv.symm k.1
    let k₀ := degreeThreeFourBlockOriginalPairKernelElement
      block P hr hs hcomponent k
    have hq : (quotientEmbedding block P q).right = 1 := by
      have hk₀ : (degreeThreeSignedQuotientPairFrame block P hr).top k₀.1 = 1 :=
        k₀.2
      rw [degreeThreeFourBlockOriginalPairKernelElement_val] at hk₀
      have hkTop : degreeThreeSignedQuotientPairTop block P q = 1 := by
        simpa [degreeThreeSignedQuotientPairFrame,
          BinaryPairFrame.ofEquiv] using hk₀
      apply Subtype.ext
      exact hkTop
    have hcoordinate :=
      translationSubmodule_quotientRepresentation_coordinate_of_top_eq_one
        block P q hq v (e.symm i)
    change (((elementaryChart block P).quotientRepresentation.ρ q v).1
        (e.symm i)) =
      degreeThreeFourBlockTranslationScalar
          block P hr hs hcomponent i k • v.1 (e.symm i)
    rw [hcoordinate, degreeThreeLocalScalar_action block P hr]
    congr 1
    apply (degreeThreeScalarFieldEquiv block P hr).injective
    rw [degreeThreeLocalScalar_eq_signScalar block P hr]
    simp only [degreeThreeFourBlockTranslationScalar,
      RingEquiv.apply_symm_apply]
    rw [degreeThreeFourBlockPairChart_bits_eq_localBit
      block P hr hs hcomponent k i]
    rfl

/-- Consequently the four distinct-sign branch has the full literal
`F₃⁴` translation submodule; no compatibility assumption remains. -/
theorem degreeThreeFourBlock_reindexedTranslationSubmodule_eq_top_of_fourSigns
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart
        block P hr hs hcomponent).action)
    (hfour :
      (degreeThreeFourBlockSignedIsotypeProfile
        block P hr hs hcomponent).isotypeCount = 4) :
    degreeThreeFourBlockReindexedTranslationSubmodule block P hs = ⊤ :=
  DegreeThreeFourBlockSignedTranslationCompatibility.reindexedTranslationSubmodule_eq_top_of_fourSigns
      (block := block) (P := P)
      (degreeThreeFourBlockSignedTranslationCompatibility
        block P hr hs hcomponent) hbinary hfour

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
