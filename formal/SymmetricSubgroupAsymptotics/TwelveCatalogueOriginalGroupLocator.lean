import SymmetricSubgroupAsymptotics.FullBinaryDoublingTwelveRepresentative
import SymmetricSubgroupAsymptotics.FullBinaryDoublingFrameTop
import SymmetricSubgroupAsymptotics.BinaryPairFramePointPullback
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopCatalogues

/-! Derive actual original12point group coverage from the EXISTING
published301 existential pair-top locator. Full local flips make every
returned invariant frame recover the original top, so no stronger
published classification statement is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelveCatalogueOriginalGroupLocator
open Non2UnipotentPrefixFiniteMenu Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

/-- The classifier uses a doubled24point action only to locate the SAME
original12point group. Every normal-axis source will be constructed on U. -/
theorem exists_top_equiv (T : DegreeTwoTwelvePairTopFiniteCatalogue)
    (published : PublishedDegreeTwoTwelvePairTopCatalogueLocator T)
    (U : Subgroup (Equiv.Perm (Fin 12))) [MulAction.IsPretransitive U (Fin 12)]
    (hU : ¬IsPGroup 2 U) :
    ∃ j : Fin 301,Nonempty ((T.row j).finite.top ≃* U) := by
  let A := FullBinaryDoublingTwelveRepresentative.choose U hU
  obtain ⟨j,hj⟩ := published A.index
  let R : DegreeTwoPairTopRealization (T.row j).finite A.index := Classical.choice hj
  let F := R.frame.pointPullback A.pointEquiv A.groupEquiv A.point_equivariant
  have hf : F.top.range=R.frame.top.range :=
    R.frame.pointPullback_top_range A.pointEquiv A.groupEquiv A.point_equivariant
  exact ⟨j,⟨R.topEquiv.trans
    ((MulEquiv.subgroupCongr hf.symm).trans (FullBinaryDoubling.frameTopEquiv U F))⟩⟩

end SymmetricSubgroupAsymptotics.TwelveCatalogueOriginalGroupLocator
