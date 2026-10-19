import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow67CornerInstalledJoint
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveJointComplete
open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveFlexibleProfiles
 def remainingData : DegreeTwoTwelveRow67CornerInstalledJoint.RemainingData where
  row j hnot hbranch := by
    have hj : j∈DegreeTwoTwelveRow67CornerInstalledJoint.remainingIndices :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j,hbranch,hnot⟩
    have he := Finset.card_eq_zero.mp DegreeTwoTwelveRow67CornerInstalledJoint.remainingIndices_card
    rw [he] at hj
    have hfalse : False := by simpa using hj
    exact hfalse.elim
 def resolution
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    DegreeTwoTwelvePairTopCatalogueResolution catalogue :=
  remainingData.resolution socle primitiveCatalogue hZmud lit
end DegreeTwoTwelveJointComplete
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
