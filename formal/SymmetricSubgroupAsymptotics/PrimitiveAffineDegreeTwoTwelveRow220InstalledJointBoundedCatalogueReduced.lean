import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow220InstalledJoint
import SymmetricSubgroupAsymptotics.PrimitiveSixTwelveNormalConsumerFacts
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJoinedHalfCycleInstalledJointBoundedCatalogueReduced
import SymmetricSubgroupAsymptotics.Row220OriginalJointDataBoundedCatalogueReduced

/-! Isolated actual degree6/12 normal-consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics

namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

namespace DegreeTwoTwelveRow220InstalledJoint

namespace BoundedCatalogueReduced

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveFlexibleProfiles

def packageAt (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSixTwelveNormalConsumerFacts) (k : Fin 1) :
    Data (catalogue.row (entry k).index).finite := by
  apply Classical.choice
  fin_cases k
  · exact ⟨(_root_.SymmetricSubgroupAsymptotics.Row220OriginalBlockFrame.BoundedCatalogueReduced.flexibleData) socle primitiveCatalogue⟩

def additionalPackage
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (j : Fin 301) (hj : j ∈ additionalIndices) : Data (catalogue.row j).finite := by
  apply Classical.choice
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hj
  exact ⟨packageAt socle primitiveCatalogue k⟩

namespace RemainingData

open _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelveRow220InstalledJoint.RemainingData

def previous (D : RemainingData)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    DegreeTwoTwelveJoinedHalfCycleInstalledJoint.RemainingData where
  row j hold hbranch := by
    by_cases hadd : j ∈ additionalIndices
    · exact _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelveRow220InstalledJoint.BoundedCatalogueReduced.additionalPackage socle primitiveCatalogue j hadd
    · exact D.row j (by simpa only [installedIndices, Finset.mem_union,
        not_or] using And.intro hold hadd) hbranch

def resolution (D : RemainingData)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    DegreeTwoTwelvePairTopCatalogueResolution catalogue :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelveJoinedHalfCycleInstalledJoint.BoundedCatalogueReduced.RemainingData.resolution ((_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelveRow220InstalledJoint.BoundedCatalogueReduced.RemainingData.previous D) socle primitiveCatalogue) socle primitiveCatalogue hZmud lit

end RemainingData

end BoundedCatalogueReduced

end DegreeTwoTwelveRow220InstalledJoint

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

end SymmetricSubgroupAsymptotics

