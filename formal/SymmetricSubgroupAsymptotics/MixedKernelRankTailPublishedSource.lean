import SymmetricSubgroupAsymptotics.MixedKernelRankTailResidual
import SymmetricSubgroupAsymptotics.MarkedC4ActualGlobalMarkedMoment

/-! Local mixed-tail source data compose with the proved global marked
moment using ordinary published hypotheses. No marked-moment theorem or
project reduction constructor is supplied as a final input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.MixedKernelRankTailResidual.Data
open SymmetricSubgroupAsymptotics SymmetricSubgroupAsymptotics.MarkedC4
open RDTOriginalWordStructure RDTNormalFInterface OrdinaryNilpotentGeneration
open LargeOrbitOrdinaryGeneration SolubleContainerCount SolubleContainerOrder
variable {w : ℕ} {U : PreE7NonPairActionClass w}

def finalSourceOfPublished (D : MixedKernelRankTailResidual.Data w U)
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
    (hAG : PublishedAschbacherGuralnickSolubleGeneration) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  D.finalSource (MarkedC4.ActualGlobalMarkedMoment.marked_bound
    hsub hseven hgen hKP h55 h53 h57 h8 hderived lit hodd h62 h86 hDixon hAG)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.MixedKernelRankTailResidual.Data
