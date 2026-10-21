import SymmetricSubgroupAsymptotics.C3PhysicalOwnerBranches
import SymmetricSubgroupAsymptotics.TernaryHighEarlierOwnerBoundedMenu

/-! The unchanged four old owner branches cover the actual old-owner sector,
using the proved bounded menu rather than a global strict-head premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
/-- The strict high inequality classifies every complete physical owner into
one of the four action branches. -/
theorem c3PhysicalStructuralOwner_branch_cover_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    (hG : C3PhysicalStructuralOwner n G) :
    ∃ k, C3PhysicalStructuralOwnerBranch k n G := by
  rcases hG with ⟨b, e, H, hphysical, hfull, o, N, hN, hHigh, hOwner⟩
  let A := OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o
  letI : MulAction.IsPretransitive A o.orbit :=
    orbitImage_pretransitive (C3ComplementSource b H) o
  letI : N.Normal := hN
  rcases ternaryHigh_earlierOwner_owned_menu_without_catalogue hChief hWeight hgen hindex published8 h18
      (A := A) (X := o.orbit) N hHigh hOwner with hThree | hA4 | hSix | hTwelve
  · exact ⟨.ternaryPGroup,
      b, e, H, hphysical, hfull, o, N, hN, hHigh, hOwner, hThree⟩
  · exact ⟨.naturalA4,
      b, e, H, hphysical, hfull, o, N, hN, hHigh, hOwner, hA4⟩
  · exact ⟨.degreeSix,
      b, e, H, hphysical, hfull, o, N, hN, hHigh, hOwner, hSix⟩
  · exact ⟨.degreeTwelve,
      b, e, H, hphysical, hfull, o, N, hN, hHigh, hOwner, hTwelve⟩

theorem c3PhysicalStructuralBranchMenu_cover_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    (hG : C3PhysicalStructuralOwner n G) :
    ∃ i, c3PhysicalStructuralBranchMenu n i G := by
  obtain ⟨k, hk⟩ := c3PhysicalStructuralOwner_branch_cover_without_catalogue
    hChief hWeight hgen hindex published8 h18 hG
  exact ⟨c3PhysicalOwnerKindEquiv.symm k, by
    simpa only [c3PhysicalStructuralBranchMenu,
      Equiv.apply_symm_apply] using hk⟩

end SymmetricSubgroupAsymptotics
