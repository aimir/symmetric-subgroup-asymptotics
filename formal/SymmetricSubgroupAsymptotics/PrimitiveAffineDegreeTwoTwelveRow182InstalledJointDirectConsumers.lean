import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow182InstalledJoint
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixActualNormalConsumers
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTernaryInstalledJointDirectConsumers
import SymmetricSubgroupAsymptotics.Row182OriginalJointDataDirectConsumers

/-! Isolated direct six-point and coarse twelve-point consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics

namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

namespace DegreeTwoTwelveRow182InstalledJoint

namespace DirectConsumers

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveFlexibleProfiles

def packageAt (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    Data (catalogue.row entry.index).finite := by
  exact (_root_.SymmetricSubgroupAsymptotics.Row182OriginalBlockKernel.DirectConsumers.flexibleData) socle primitiveCatalogue

def additionalPackage
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (j : Fin 301) (hj : j ∈ additionalIndices) : Data (catalogue.row j).finite := by
  have he : j=entry.index := Finset.mem_singleton.mp hj
  subst j
  exact packageAt socle primitiveCatalogue

namespace RemainingData

open _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelveRow182InstalledJoint.RemainingData

def previous (D : RemainingData)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    DegreeTwoTwelveTernaryInstalledJoint.RemainingData where
  row j hold hbranch := by
    by_cases hadd : j ∈ additionalIndices
    · exact _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelveRow182InstalledJoint.DirectConsumers.additionalPackage socle primitiveCatalogue j hadd
    · exact D.row j (by simpa only [installedIndices, Finset.mem_union,
        not_or] using And.intro hold hadd) hbranch

def resolution (D : RemainingData)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (primitiveCatalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    DegreeTwoTwelvePairTopCatalogueResolution catalogue :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelveTernaryInstalledJoint.DirectConsumers.RemainingData.resolution ((_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelveRow182InstalledJoint.DirectConsumers.RemainingData.previous D) socle primitiveCatalogue) socle primitiveCatalogue hZmud lit

end RemainingData

end DirectConsumers

end DegreeTwoTwelveRow182InstalledJoint

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

end SymmetricSubgroupAsymptotics

