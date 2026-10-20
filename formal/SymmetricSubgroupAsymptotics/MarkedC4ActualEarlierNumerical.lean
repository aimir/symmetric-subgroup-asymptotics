import SymmetricSubgroupAsymptotics.MarkedC4ActualF20Numerical

/-! Source-catalogue numerical threading without the old project-owned RDT
reduction input. The actual action catalogue remains an explicit obligation;
this file does not assert catalogue exhaustiveness or T1. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

noncomputable def PreE7RankTailOwnerSourceData.toActionOwnerMarked
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hM4 : GlobalMarkedC4MomentBound)
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (S : PreE7RankTailOwnerSourceData w U) :
    PreE7NumericalRankTailActionOwner w U := by
  cases S with
  | ordinary family source =>
      refine ⟨preE7NoPairNoC3EarlierOwnerEquiv.symm family, ?_⟩
      simpa only [preE7NoPairNoC3EarlierNumericalRankTailFamilyAction,
        preE7NoPairNoC3EarlierOwnerEquiv.apply_symm_apply] using
        (Or.inl (preE7OrdinaryNumericalFamilyAction lit hgen source) :
          preE7NoPairNoC3EarlierNumericalRankTailFamilyAction family w U)
  | b6 source =>
      refine ⟨preE7NoPairNoC3EarlierOwnerEquiv.symm .b6, ?_⟩
      simpa only [preE7NoPairNoC3EarlierNumericalRankTailFamilyAction,
        preE7NoPairNoC3EarlierOwnerEquiv.apply_symm_apply] using
        (Or.inr (Or.inl ⟨rfl, ⟨source⟩⟩) :
          preE7NoPairNoC3EarlierNumericalRankTailFamilyAction .b6 w U)
  | y1 source =>
      refine ⟨preE7NoPairNoC3EarlierOwnerEquiv.symm .y1, ?_⟩
      simpa only [preE7NoPairNoC3EarlierNumericalRankTailFamilyAction,
        preE7NoPairNoC3EarlierOwnerEquiv.apply_symm_apply] using
        (Or.inr (Or.inr (Or.inl ⟨rfl, ⟨source⟩⟩)) :
          preE7NoPairNoC3EarlierNumericalRankTailFamilyAction .y1 w U)
  | sns2 source =>
      refine ⟨preE7NoPairNoC3EarlierOwnerEquiv.symm .sns2, ?_⟩
      simpa only [preE7NoPairNoC3EarlierNumericalRankTailFamilyAction,
        preE7NoPairNoC3EarlierOwnerEquiv.apply_symm_apply] using
        (Or.inr (Or.inr (Or.inr ⟨rfl, ⟨source⟩⟩)) :
          preE7NoPairNoC3EarlierNumericalRankTailFamilyAction .sns2 w U)
  | f20 source =>
      exact source.rankTailActionOwner hM4

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualEarlierNumerical
open RDTOriginalWordStructure RDTNormalFInterface OrdinaryNilpotentGeneration
open LargeOrbitOrdinaryGeneration SolubleContainerCount SolubleContainerOrder
open Non2UnipotentPrefixFiniteMenu

def actionOwner
    (hsub : PublishedSolubleSubdirectHeight) (hseven : PublishedTheoremSeven)
    (hKPgen : KovacsPraegerAbelianizationBound)
    (hKP : KovacsPraegerBinaryAbelianQuotientBound) (h55 : PublishedTheorem55Binary)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (h8 : RDTDegreeEightExceptional.PublishedDegreeEightExceptional)
    (hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary)
    (rdt46 : RDTTheorem46BinaryInput)
    (hodd : OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (h62 : PublishedProposition62) (h86 : PublishedTheorem86Representatives)
    (hDixon : PublishedDixonOrder)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (lit : PreE7CharacterLiterature) (hgen : PermutationSubgroupGeneratorBound)
    {w : ℕ} {U : PreE7NonPairActionClass w} (S : PreE7RankTailOwnerSourceData w U) :
    PreE7NumericalRankTailActionOwner w U :=
  S.toActionOwnerMarked lit hgen
    (ActualGlobalMarkedMoment.marked_bound hsub hseven hKPgen hKP h55 h53 h57 h8 hderived
      rdt46 hodd h62 h86 hDixon hAG)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualEarlierNumerical
