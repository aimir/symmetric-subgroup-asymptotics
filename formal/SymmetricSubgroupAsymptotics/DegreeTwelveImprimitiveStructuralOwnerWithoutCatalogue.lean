import SymmetricSubgroupAsymptotics.TernaryHighOwnerCapacity
import SymmetricSubgroupAsymptotics.DegreeTwelveImprimitiveTopGeometryWithoutCatalogue

/-! The two original degree12 imprimitive geometries install the same owners;
primitive degree12 is kept for the new semisimple sector. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock

/-- The two saturated degree-twelve orientations install their intrinsic
earlier owners, with the original normal subgroup and actual minimal block
system retained. -/
theorem degreeTwelve_high_imprimitive_structuralOwner_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal]
    (himprimitive : ¬ MulAction.IsPreprimitive A Ω)
    (hDegree : Nat.card Ω = 12)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    IsC1TernaryPrimeBaseOwner A ∨ IsC1BinaryNineTopOwner A Ω := by
  obtain ⟨ω₀, D, c, horient, hc, hTopRank, hRank⟩ :=
    degreeTwelve_high_imprimitive_top_geometry_without_catalogue
      hChief hWeight hgen hindex published8 h18 N himprimitive hDegree hHigh
  letI : Fintype D.Points := Fintype.ofFinite D.Points
  letI : ∀ x : D.Points, Fintype (originalBlockFibre D.map x) :=
    fun x => Fintype.ofFinite (originalBlockFibre D.map x)
  rcases horient with h34 | h43
  · exact Or.inl
      (D.degreeTwelve_primeBase_owner N h34.1 h34.2.2 hRank hTopRank)
  · have hCard : ∀ x : D.Points,
        Nat.card (originalBlockFibre D.map x) = 4 := by
      intro x
      rw [D.originalBlockFibre_card_eq x, h43.1]
    let e : ∀ x : D.Points, Fin 4 ≃ originalBlockFibre D.map x :=
      fun x => (Finite.equivFinOfCardEq (hCard x)).symm
    exact Or.inr
      (D.fourByThree_nineTopOwner N c h43.2.1 h43.2.2 hc
        hTopRank hRank e)

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
