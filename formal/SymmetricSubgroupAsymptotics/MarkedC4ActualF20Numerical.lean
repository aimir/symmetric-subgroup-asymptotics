import SymmetricSubgroupAsymptotics.MarkedC4ActualGlobalMarkedMoment
import SymmetricSubgroupAsymptotics.Non2PreE7RankTailSourceDichotomyClosure

/-! Thread the constructed global marked moment into the existing F20
numerical owner. This removes the project-owned RDT reduction input from
this branch. The remaining catalogue/exhaustion obligations are unchanged;
no full T1 theorem is asserted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualF20Numerical
open RDTOriginalWordStructure RDTNormalFInterface OrdinaryNilpotentGeneration
open LargeOrbitOrdinaryGeneration SolubleContainerCount SolubleContainerOrder
open Non2UnipotentPrefixFiniteMenu

def numericalPackage
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
    {w : ℕ} {i : PreE7NonPairActionClass w} (S : PreE7F20Source w i) :
    PreE7EarlierNumericalPackage .f20 w i :=
  S.numericalPackage (ActualGlobalMarkedMoment.marked_bound hsub hseven hgen hKP h55 h53 h57 h8 hderived lit hodd h62 h86 hDixon hAG)

def rankTailActionOwner
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
    {w : ℕ} {i : PreE7NonPairActionClass w} (S : PreE7F20Source w i) :
    PreE7NumericalRankTailActionOwner w i :=
  S.rankTailActionOwner (ActualGlobalMarkedMoment.marked_bound hsub hseven hgen hKP h55 h53 h57 h8 hderived lit hodd h62 h86 hDixon hAG)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualF20Numerical
