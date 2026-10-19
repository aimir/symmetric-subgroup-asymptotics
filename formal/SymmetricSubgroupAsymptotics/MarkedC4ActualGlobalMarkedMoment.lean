import SymmetricSubgroupAsymptotics.MarkedC4ActualSolubleGlobal
import SymmetricSubgroupAsymptotics.MarkedC4ConstructedGlobalReduction
import SymmetricSubgroupAsymptotics.MarkedC4AschbacherGuralnickSolubleGeneration

/-! The full global marked C4 moment from the constructed soluble theorem
and the ordinary Aschbacher--Guralnick soluble-generation theorem.
Every hypothesis is named ordinary literature; no project reduction
constructor or marked-moment proposition is an input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualGlobalMarkedMoment
open RDTOriginalWordStructure RDTNormalFInterface OrdinaryNilpotentGeneration
open LargeOrbitOrdinaryGeneration SolubleContainerCount SolubleContainerOrder

theorem marked_bound
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
    Non2UnipotentPrefixFiniteMenu.GlobalMarkedC4MomentBound :=
  globalMarkedC4MomentBound_of_soluble
    (rdtOneGeneratorSolubleInput_of_aschbacherGuralnick hAG)
    (ActualSolubleGlobal.marked_bound hsub hseven hgen hKP h55 h53 h57 h8 hderived lit hodd
      h62 h86 hDixon)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualGlobalMarkedMoment
