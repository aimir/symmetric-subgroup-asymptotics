import SymmetricSubgroupAsymptotics.C3HighAlignedRefinedExhaustion
import SymmetricSubgroupAsymptotics.C3HighAlignedRefinedContinuationWithoutCatalogue
import SymmetricSubgroupAsymptotics.C3DegreeSixAlignedLocalWithoutCatalogue
import SymmetricSubgroupAsymptotics.C3DegreeTwelveAlignedLocalWithoutCatalogue
import SymmetricSubgroupAsymptotics.C3TernaryPGroupAlignedPositiveLocalWithoutCatalogue

/-! Every old refined aligned cell keeps its exact local row, now using
proved local/actual head bounds. Its whole original physical owner sector
is exponentially contractive without a composition correspondence. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics
/-- Every aligned ternary p-group cell of width other than three has a local
row: its width is nine or twenty seven, and the positive-width ternary rows
apply. -/
theorem c3HighAligned_ternaryPGroup_localRow_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (j : C3HighAlignedFirstOwnerIndex)
    (hk : c3PhysicalOwnerKindEquiv j.1.2.1 =
      C3PhysicalOwnerKind.ternaryPGroup)
    (hw : c3HighAlignedFirstOwnerWidth j ≠ 3) :
    C3HighAlignedLocalRow j := by
  rcases j with ⟨⟨d, owner, i⟩, hj⟩
  have hU := hj.2
  rw [hk] at hU
  letI := Non2TransitiveActionClass.representative_pretransitive i
  cases d with
  | three => exact absurd rfl hw
  | four =>
      let U : Subgroup (Equiv.Perm (Fin 4)) := i.representative
      letI : MulAction.IsPretransitive U (Fin 4) :=
        Non2TransitiveActionClass.representative_pretransitive i
      exact absurd (by decide : 2 ∣ 4)
        (transitive_ternaryPGroup_width_not_even U hU (by decide))
  | six =>
      let U : Subgroup (Equiv.Perm (Fin 6)) := i.representative
      letI : MulAction.IsPretransitive U (Fin 6) :=
        Non2TransitiveActionClass.representative_pretransitive i
      exact absurd (by decide : 2 ∣ 6)
        (transitive_ternaryPGroup_width_not_even U hU (by decide))
  | twelve =>
      let U : Subgroup (Equiv.Perm (Fin 12)) := i.representative
      letI : MulAction.IsPretransitive U (Fin 12) :=
        Non2TransitiveActionClass.representative_pretransitive i
      exact absurd (by decide : 2 ∣ 12)
        (transitive_ternaryPGroup_width_not_even U hU (by decide))
  | nine =>
      exact c3HighAligned_degreeNine_ternaryPGroup_localRow_without_catalogue hChief hgen hindex published8 h18
        ⟨⟨C3HighWidthLabel.nine, owner, i⟩, hj⟩ hk rfl
  | twentySeven =>
      exact c3HighAligned_degreeTwentySeven_ternaryPGroup_localRow
        ⟨⟨C3HighWidthLabel.twentySeven, owner, i⟩, hj⟩ hk rfl

/-- Exhaustion: every refined aligned cell reaches one of the ternary
p-group, natural-`A4`, degree-six, prime-base or binary-nine rows. -/
theorem c3HighRefinedAligned_localRow_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (j : C3HighRefinedAlignedIndex) :
    C3HighAlignedLocalRow j.1 := by
  obtain ⟨j, hj⟩ := j
  cases hk : c3PhysicalOwnerKindEquiv j.1.2.1 with
  | ternaryPGroup =>
      exact c3HighAligned_ternaryPGroup_localRow_without_catalogue hChief hgen hindex published8 h18 j hk
        (fun hw => hj ⟨hw, hk⟩)
  | naturalA4 => exact c3HighAligned_naturalA4_localRow j hk
  | degreeSix =>
      obtain ⟨D, hD, h⟩ := c3HighAligned_degreeSix_local_bound_without_catalogue hgen hindex published8 hKP j hk
      exact C3HighAlignedLocalRow.of_kernel j .degreeSix D hD h
  | degreeTwelve =>
      obtain ⟨r, D, hD, h⟩ :=
        c3HighAligned_degreeTwelve_local_bound_without_catalogue hChief hWeight hgen hindex published8 h18 j hk
      exact C3HighAlignedLocalRow.of_kernel j r D hD h

/-- The complete high-C3 structural-owner continuation, with no remaining
local-row hypothesis. -/
noncomputable def c3PhysicalStructuralOwner_closedExponentialForwardEstimate_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      c3PhysicalStructuralOwnerRatio :=
  let hrow := c3HighRefinedAligned_localRow_without_catalogue hChief hWeight hgen hindex published8 h18 hKP
  c3PhysicalStructuralOwner_refinedExponentialForwardEstimate_without_catalogue
    hChief hWeight hgen hindex published8 h18
    (fun j => Classical.choose (hrow j))
    (fun j => (Classical.choose_spec (hrow j)).1)
    (fun j => (Classical.choose_spec (hrow j)).2.1)
    (fun j => (Classical.choose_spec (hrow j)).2.2)

end SymmetricSubgroupAsymptotics
