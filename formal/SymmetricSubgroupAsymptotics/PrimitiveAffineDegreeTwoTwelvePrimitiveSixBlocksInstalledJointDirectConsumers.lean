import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePrimitiveSixBlocksInstalledJoint
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixActualNormalConsumers
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow269InstalledJointDirectConsumers
import SymmetricSubgroupAsymptotics.Row278OriginalJointDataDirectConsumers
import SymmetricSubgroupAsymptotics.Row279OriginalJointDataDirectConsumers
import SymmetricSubgroupAsymptotics.Row288OriginalJointDataDirectConsumers
import SymmetricSubgroupAsymptotics.Row296OriginalJointDataDirectConsumers
import SymmetricSubgroupAsymptotics.Row297OriginalJointDataDirectConsumers
import SymmetricSubgroupAsymptotics.Row298OriginalJointDataDirectConsumers
import SymmetricSubgroupAsymptotics.Row299OriginalJointDataDirectConsumers

/-! Isolated direct six-point and coarse twelve-point consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics

namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

namespace DegreeTwoTwelvePrimitiveSixBlocksInstalledJoint

namespace DirectConsumers

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveFlexibleProfiles

def packageAt (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) (k : Fin 7) :
    Data (catalogue.row (entry k).index).finite := by
  apply Classical.choice
  fin_cases k
  · exact ⟨(_root_.SymmetricSubgroupAsymptotics.Row278OriginalBlockFrame.DirectConsumers.flexibleData) socle primitiveCatalogue⟩
  · exact ⟨(_root_.SymmetricSubgroupAsymptotics.Row279OriginalBlockFrame.DirectConsumers.flexibleData) socle primitiveCatalogue⟩
  · exact ⟨(_root_.SymmetricSubgroupAsymptotics.Row288OriginalBlockFrame.DirectConsumers.flexibleData) socle primitiveCatalogue⟩
  · exact ⟨(_root_.SymmetricSubgroupAsymptotics.Row296OriginalBlockFrame.DirectConsumers.flexibleData) socle primitiveCatalogue⟩
  · exact ⟨(_root_.SymmetricSubgroupAsymptotics.Row297OriginalBlockFrame.DirectConsumers.flexibleData) socle primitiveCatalogue⟩
  · exact ⟨(_root_.SymmetricSubgroupAsymptotics.Row298OriginalBlockFrame.DirectConsumers.flexibleData) socle primitiveCatalogue⟩
  · exact ⟨(_root_.SymmetricSubgroupAsymptotics.Row299OriginalBlockFrame.DirectConsumers.flexibleData) socle primitiveCatalogue⟩

def additionalPackage
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (j : Fin 301) (hj : j ∈ additionalIndices) : Data (catalogue.row j).finite := by
  apply Classical.choice
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hj
  exact ⟨packageAt socle primitiveCatalogue k⟩

namespace RemainingData

open _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelvePrimitiveSixBlocksInstalledJoint.RemainingData

def previous (D : RemainingData)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    DegreeTwoTwelveRow269InstalledJoint.RemainingData where
  row j hold hbranch := by
    by_cases hadd : j ∈ additionalIndices
    · exact _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelvePrimitiveSixBlocksInstalledJoint.DirectConsumers.additionalPackage socle primitiveCatalogue j hadd
    · exact D.row j (by simpa only [installedIndices, Finset.mem_union,
        not_or] using And.intro hold hadd) hbranch

def resolution (D : RemainingData)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    DegreeTwoTwelvePairTopCatalogueResolution catalogue :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelveRow269InstalledJoint.DirectConsumers.RemainingData.resolution ((_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelvePrimitiveSixBlocksInstalledJoint.DirectConsumers.RemainingData.previous D) socle primitiveCatalogue) socle primitiveCatalogue hZmud lit

end RemainingData

end DirectConsumers

end DegreeTwoTwelvePrimitiveSixBlocksInstalledJoint

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

end SymmetricSubgroupAsymptotics

