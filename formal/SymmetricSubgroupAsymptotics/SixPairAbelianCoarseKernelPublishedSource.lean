import SymmetricSubgroupAsymptotics.SixPairAbelianCoarseKernelSource
import SymmetricSubgroupAsymptotics.MarkedC4ActualGlobalMarkedMoment

/-! The actual abelian coarse-kernel source with the full marked moment
constructed from its ordinary published inputs. No marked-moment or
project-owned reduction hypothesis is an argument of this wrapper. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairAbelianCoarseKernelPublishedSource
open Non2UnipotentPrefixFiniteMenu
open MarkedC4 RDTOriginalWordStructure RDTNormalFInterface OrdinaryNilpotentGeneration
open LargeOrbitOrdinaryGeneration SolubleContainerCount SolubleContainerOrder

 def source
    (hsub : PublishedSolubleSubdirectHeight) (hseven : PublishedTheoremSeven)
    (hgen : KovacsPraegerAbelianizationBound)
    (hKP : KovacsPraegerBinaryAbelianQuotientBound) (h55 : PublishedTheorem55Binary)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (h8 : RDTDegreeEightExceptional.PublishedDegreeEightExceptional)
    (hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary)
    (lit : RDTTheorem46BinaryInput)
    (hodd : OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (h62 : PublishedProposition62) (h86 : PublishedTheorem86Representatives)
    (hDixon : PublishedDixonOrder)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (p : PreE7PairActionClass 6)
    [MulAction.IsPretransitive (preE7PairAction 6 p) (Fin 12)]
    (F : BinaryPairFrame (preE7PairAction 6 p) (Fin 6))
    (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))
    (hcomm : ∀ a b : (SixPairNestedTopFrames.nestedFrame F E).top.ker,a*b=b*a) :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) :=
  SixPairAbelianCoarseKernelSource.source p F E hcomm hgen
    (ActualGlobalMarkedMoment.marked_bound hsub hseven hgen hKP h55 h53 h57 h8 hderived lit hodd
      h62 h86 hDixon hAG)

end SymmetricSubgroupAsymptotics.SixPairAbelianCoarseKernelPublishedSource
