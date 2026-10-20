import SymmetricSubgroupAsymptotics.MarkedC4ActualFixedCutoffMarkedBound
import SymmetricSubgroupAsymptotics.MarkedC4ConstructedGlobalReduction

/-! The actual soluble global marked C4 theorem, assembled from original
bounded-word enumeration and the constructed large-orbit reduction.
No RDTMarkedC4ReductionInput or marked count/encoding callback is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualSolubleGlobal
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
    (hDixon : PublishedDixonOrder) : SolubleGlobalMarkedC4MomentBound := by
  apply ConstructedGlobalReduction.solubleGlobal_of_smallSource h62 h86 hDixon
  intro C hC
  exact ActualFixedCutoffMarkedBound.marked_bound hsub hseven hgen hKP h55 h53 h57 h8 hderived
    lit hodd (by omega : 1<C)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualSolubleGlobal
