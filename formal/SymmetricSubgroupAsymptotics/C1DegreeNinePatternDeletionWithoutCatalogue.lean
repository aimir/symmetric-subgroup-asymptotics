import SymmetricSubgroupAsymptotics.C1DegreeNinePatternDeletion
import SymmetricSubgroupAsymptotics.C1DegreeNineRankBudgetWithoutCatalogue

/-! Deleting the same actual nonmarker orbit preserves the same full source
pattern; install its newly proved rank budget without a strict-head premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
open FusionOrbitProfileChart

/-- The numerical rank budget is the smaller invariant consequence needed
by the degree-nine ternary epimorphism row. -/
theorem C1DegreeNineSourcePattern.complementImage_rankBudget_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {X : Type} [Fintype X] {c : ℕ}
    (H : Subgroup (Equiv.Perm X))
    (selected : OrbitProfileFromOrbits.Orbit H)
    (eC : Fin c ≃ ↥((orbitSubaction H selected)ᶜ))
    (hpattern : C1DegreeNineSourcePattern H)
    (hselected : ¬ IsRegularC3Orbit H selected) :
    C1DegreeNineRankBudget (Complement.image H selected eC) :=
  (hpattern.complementImage H selected eC hselected).rankBudget_without_catalogue
    hChief hgen hindex published8 h18 (Complement.image H selected eC)

/-- In an exact selected-orbit chart, deleting a nonmarker orbit attaches the
degree-nine rank budget to the literal source projection of the actual fusion
model. -/
theorem C1DegreeNineSourcePattern.deletedModel_rankBudget_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {X : Type} [Fintype X] {w c : ℕ}
    (H : Subgroup (Equiv.Perm X))
    (selected : OrbitProfileFromOrbits.Orbit H)
    (U : Subgroup (Equiv.Perm (Fin w)))
    (eO : Fin w ≃ selected.orbit)
    (eC : Fin c ≃ ↥((orbitSubaction H selected)ᶜ))
    (himage : relabelSubgroup eO U =
      OrbitProfileFromOrbits.orbitImage H selected)
    (hpattern : C1DegreeNineSourcePattern H)
    (hselected : ¬ IsRegularC3Orbit H selected) :
    C1DegreeNineRankBudget
      ((fusionDeletedModel U
          (relabelSubgroup (chart H selected eO eC).symm H)).map
        (MonoidHom.snd U (Equiv.Perm (Fin c)))) := by
  rw [Complement.deletedSource_eq_image H selected eO eC U himage]
  exact hpattern.complementImage_rankBudget_without_catalogue hChief hgen hindex published8 h18
    H selected eC hselected

end SymmetricSubgroupAsymptotics

end
