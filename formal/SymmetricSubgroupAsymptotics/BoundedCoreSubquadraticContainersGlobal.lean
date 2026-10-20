import SymmetricSubgroupAsymptotics.BoundedCoreFixedCutoffMarkedBound
import SymmetricSubgroupAsymptotics.MarkedC4SubquadraticContainersGlobal

/-! The global weighted moment with the bounded-chief-section nilpotent
core construction. The sharp unrestricted Theorem Seven is not an input. -/
set_option autoImplicit false
noncomputable section
open Filter
namespace SymmetricSubgroupAsymptotics.MarkedC4.BoundedCoreSubquadraticContainersGlobal
open RDTOriginalWordStructure RDTNormalFInterface OrdinaryNilpotentGeneration
open LargeOrbitOrdinaryGeneration SolubleContainerOrder

/-- The same global marked conclusion, without a Pyber hypothesis. -/
theorem marked_bound
    (hgen : KovacsPraegerAbelianizationBound)
    (hKP : KovacsPraegerBinaryAbelianQuotientBound) (h55 : PublishedTheorem55Binary)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (h8 : RDTDegreeEightExceptional.PublishedDegreeEightExceptional)
    (hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary)
    (rdt46 : RDTTheorem46BinaryInput)
    (hodd : OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (h62 : PublishedProposition62)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hDixon : PublishedDixonOrder)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration) :
    Non2UnipotentPrefixFiniteMenu.GlobalMarkedC4MomentBound := by
  apply globalMarkedC4MomentBound_of_soluble
    (rdtOneGeneratorSolubleInput_of_aschbacherGuralnick hAG)
  apply SubquadraticContainersGlobal.solubleGlobal_of_smallSource h62 hLMM hDixon
  intro C hC
  exact BoundedCoreFixedCutoffMarkedBound.marked_bound hgen hKP h55 h53 h57
    h8 hderived rdt46 hodd (by omega : 1 < C)

end SymmetricSubgroupAsymptotics.MarkedC4.BoundedCoreSubquadraticContainersGlobal

end
