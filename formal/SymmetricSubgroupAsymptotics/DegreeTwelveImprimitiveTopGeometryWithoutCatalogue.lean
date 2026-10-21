import SymmetricSubgroupAsymptotics.DegreeTwelveTopGeometry
import SymmetricSubgroupAsymptotics.DegreeTwelveImprimitiveBlockReductionWithoutCatalogue

/-! The original12-point top geometries on the actual imprimitive branch.
Primitive degree12 is deliberately retained for its semisimple owner. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

/-- The full high degree-twelve reduction with the literal top action
identified in both surviving orientations. -/
theorem degreeTwelve_high_imprimitive_top_geometry_without_catalogue
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
    ∃ (ω₀ : Ω) (D : OriginalMinimalBlock (A := A) ω₀)
        (c : ActualChiefSeries D.Component),
      ((Nat.card D.Fibre = 3 ∧ Nat.card D.Points = 4 ∧
          IsNaturalA4Action D.Top D.Points) ∨
        (Nat.card D.Fibre = 4 ∧ Nat.card D.Points = 3 ∧
          Nat.card D.Top = 3)) ∧
      actualChiefSeriesTernaryWeight c = 1 ∧
      Module.finrank (ZMod 3)
        (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1 ∧
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2 := by
  obtain ⟨ω₀, D, c, horient, hv, ht, hd⟩ :=
    degreeTwelve_high_imprimitive_minimalBlock_data_without_catalogue
      hChief hWeight hgen hindex published8 h18 N himprimitive hDegree hHigh
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : FaithfulSMul D.Top D.Points := D.top_faithful
  letI : Finite D.Top := D.top_finite
  letI : Nonempty D.Points := ⟨D.base⟩
  let T := originalNormalRange D.topMap N
  have hTRank : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 T) = 1 := by
    simpa only [T] using ht
  refine ⟨ω₀, D, c, ?_, hv, ht, hd⟩
  rcases horient with h34 | h43
  · exact Or.inl ⟨h34.1, h34.2,
      degreeFour_rankOne_isNaturalA4 h34.2 T hTRank⟩
  · have hP : IsPGroup 3 D.Top :=
      degreeThree_rankOne_isPGroup h43.2 T hTRank
    exact Or.inr ⟨h43.1, h43.2,
      transitiveThreePoint_threePGroup_card h43.2 hP⟩

end SymmetricSubgroupAsymptotics

end
