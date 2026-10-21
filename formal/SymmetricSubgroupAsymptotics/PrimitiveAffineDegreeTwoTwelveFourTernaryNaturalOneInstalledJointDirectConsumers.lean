import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFourTernaryNaturalOneInstalledJoint
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixActualNormalConsumers
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.FourTernaryNaturalOneOriginalJointDataDirectConsumers
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow220InstalledJointDirectConsumers

/-! Isolated direct six-point and coarse twelve-point consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics

namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

namespace DegreeTwoTwelveFourTernaryNaturalOneInstalledJoint

namespace DirectConsumers

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveFlexibleProfiles

def packageAt (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) (k : Fin 5) :
    Data (catalogue.row (entry k).index).finite := by
  apply Classical.choice
  fin_cases k
  · exact ⟨(_root_.SymmetricSubgroupAsymptotics.FourTernaryNaturalOneOriginalJointData.DirectConsumers.row122Data) socle primitiveCatalogue⟩
  · exact ⟨(_root_.SymmetricSubgroupAsymptotics.FourTernaryNaturalOneOriginalJointData.DirectConsumers.row157Data) socle primitiveCatalogue⟩
  · exact ⟨(_root_.SymmetricSubgroupAsymptotics.FourTernaryNaturalOneOriginalJointData.DirectConsumers.row213Data) socle primitiveCatalogue⟩
  · exact ⟨(_root_.SymmetricSubgroupAsymptotics.FourTernaryNaturalOneOriginalJointData.DirectConsumers.row232Data) socle primitiveCatalogue⟩
  · exact ⟨(_root_.SymmetricSubgroupAsymptotics.FourTernaryNaturalOneOriginalJointData.DirectConsumers.row259Data) socle primitiveCatalogue⟩

def additionalPackage
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (j : Fin 301) (hj : j ∈ additionalIndices) : Data (catalogue.row j).finite := by
  apply Classical.choice
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hj
  exact ⟨packageAt socle primitiveCatalogue k⟩

namespace RemainingData

open _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelveFourTernaryNaturalOneInstalledJoint.RemainingData

def previous (D : RemainingData)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    DegreeTwoTwelveRow220InstalledJoint.RemainingData where
  row j hold hbranch := by
    by_cases hadd : j ∈ additionalIndices
    · exact _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelveFourTernaryNaturalOneInstalledJoint.DirectConsumers.additionalPackage socle primitiveCatalogue j hadd
    · exact D.row j (by simpa only [installedIndices, Finset.mem_union,
        not_or] using And.intro hold hadd) hbranch

def resolution (D : RemainingData)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    DegreeTwoTwelvePairTopCatalogueResolution catalogue :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelveRow220InstalledJoint.DirectConsumers.RemainingData.resolution ((_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelveFourTernaryNaturalOneInstalledJoint.DirectConsumers.RemainingData.previous D) socle primitiveCatalogue) socle primitiveCatalogue hZmud lit

end RemainingData

end DirectConsumers

end DegreeTwoTwelveFourTernaryNaturalOneInstalledJoint

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

end SymmetricSubgroupAsymptotics

