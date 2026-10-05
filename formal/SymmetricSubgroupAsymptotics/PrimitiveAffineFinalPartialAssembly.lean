import SymmetricSubgroupAsymptotics.PrimitiveAffineExceptionalConsumerPartialAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineConsumerAssembly
import SymmetricSubgroupAsymptotics.PrimitiveCatalogueClassificationPublished

/-!
# Final affine and T1 plumbing, parameterized only by the three active lanes

This module closes every assembly step after the degree-two, degree-three,
and degree-four residual source functions.  The final publication theorem
will instantiate those three arguments with their checked constructions;
no other project-owned input remains below this boundary.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open PrimitiveAffineImprimitiveBlockTransfer

abbrev PrimitiveAffineResidualDegreeSource (r : ℕ) :=
  ∀ {w : ℕ} (U : PreE7NonPairActionClass w) (_hw : 5 ≤ w)
    (basePoint : Fin w)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre),
    ImprimitiveAffineResidualCapacityException
        (Nat.card block.Fibre) (Nat.card block.Points)
        (Nat.card block.Component) →
    Nat.card block.Fibre = r →
    PreE7RankTailSourceOrYonedaTopData w U

/-- Assemble the primitive and imprimitive affine consumer after the three
independent low-degree source functions have been proved. -/
noncomputable def preE7PrimitiveAffineConsumerData_of_lowDegreeSources
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hcomp : PrimitiveCompositionLengthInput)
    (hKP : KovacsPraegerAbelianizationBound)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (published : PublishedPrimitiveAffineFiniteLiterature)
    (degreeTwo : PrimitiveAffineResidualDegreeSource 2)
    (degreeThree : PrimitiveAffineResidualDegreeSource 3)
    (degreeFour : PrimitiveAffineResidualDegreeSource 4) :
    PreE7PrimitiveAffineConsumerData := by
  let exceptional :=
    preE7PrimitiveAffineExceptionalCellConsumerData_of_lowDegreeSources
      hZmud lit hgen hClifford hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm hSimpleGen published.smallCatalogue degreeTwo degreeThree
      degreeFour
  let components := preE7PrimitiveAffineImprimitiveComponentSourceData
    published.smallCatalogue hcomp hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm exceptional
  exact preE7PrimitiveAffineConsumerData published hcomp hgen hKP
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hSimpleGen components

/-- Every final assembly step for T1, with only the three active affine
residual lanes still exposed.  The classification inputs and every other
argument are named pre-existing published results. -/
theorem T1_of_published_inputs_and_lowDegreeAffineSources
    (lit : PreE7CharacterLiterature)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hgen : PermutationSubgroupGeneratorBound)
    (hcomp : PrimitiveCompositionLengthInput)
    (hRDT : MarkedC4.RDTMarkedC4ReductionInput)
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hDegreeNine : PublishedPrimitiveDegreeNineClassification)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hHoltRoneyDougal : FaithfulSimplePermutationGeneratorBound)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (publishedAffine : PublishedPrimitiveAffineFiniteLiterature)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (degreeTwo : PrimitiveAffineResidualDegreeSource 2)
    (degreeThree : PrimitiveAffineResidualDegreeSource 3)
    (degreeFour : PrimitiveAffineResidualDegreeSource 4)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput) : T1 :=
  T1_of_preE7_primitiveCatalogueClassification lit hgen hRDT hTracey
    hExceptional hWeight hDegreeNine hPrimitive h18 hKP hLMM
    hHoltRoneyDougal
    (preE7PrimitiveCatalogueClassificationInput_of_published socle catalogue)
    (preE7PrimitiveAffineConsumerData_of_lowDegreeSources hZmud lit hgen
      hClifford hcomp hKP hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
      hSimpleGen publishedAffine degreeTwo degreeThree degreeFour)
    hcoarse hFS

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
