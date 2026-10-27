import SymmetricSubgroupAsymptotics.CFSGSuzBrayBoundedSharpT1Reduction
import SymmetricSubgroupAsymptotics.CFSGJankoTwoDihedralBinaryGoodSylow

/-! Successor removes ONLY J2 from Good13. Three published bundles, the
original CFSG classification input, and the numerical21 callback are unchanged.
The J2 recovery is supplied internally by whole-matrix certificates, with
inherited simplicity on the exact OLD presentation carrier. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

def RemainingGoodSylowIndexAfterJankoTwoDihedral (i : CFSG.Index) : Prop :=
  RemainingGoodSylowIndexAfterSuzBray i ∧ i ≠ .sporadic .j2

theorem goodSylow_callback_after_janko_two_dihedral
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterJankoTwoDihedral i →
        ∃ p,GoodSylowPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingGoodSylowIndexAfterSuzBray i) :
    ∃ p,GoodSylowPrime i.Model p := by
  by_cases hj : i = .sporadic .j2
  · subst i
    letI : Finite CFSG.Models.Presentations.J2.Model :=
      inferInstanceAs (Finite ((CFSG.Index.sporadic .j2).Model))
    letI : IsSimpleGroup CFSG.Models.Presentations.J2.Model :=
      inferInstanceAs (IsSimpleGroup ((CFSG.Index.sporadic .j2).Model))
    exact ⟨2,CFSGJankoTwoDihedralBinaryGoodSylow.goodSylowPrime hCFSG⟩
  · exact remaining i hn ⟨hi,hj⟩

end SymmetricSubgroupAsymptotics.CFSGReduction

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

theorem T1_of_three_published_inputs_cfsg_and_remaining_after_janko_two_dihedral
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hTracey : TraceyPermutationGeneratorInput)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterJankoTwoDihedral i →
        ∃ p,CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuTwentyFourComplete i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyFourIndexSquare i) : T1 :=
  T1_of_three_published_inputs_cfsg_and_remaining_after_suz_bray_bounded_sharp
    lit hExceptionalOrbits hTracey hCFSG
    (CFSGReduction.goodSylow_callback_after_janko_two_dihedral hCFSG remainingGoodSylow)
    remainingSimpleIndex

theorem allTargets_of_three_published_inputs_cfsg_and_remaining_after_janko_two_dihedral
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hTracey : TraceyPermutationGeneratorInput)
    (hCFSG : CFSG.CFSGClassification)
    (remainingGoodSylow : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterJankoTwoDihedral i →
        ∃ p,CFSGReduction.GoodSylowPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuTwentyFourComplete i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyFourIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_three_published_inputs_cfsg_and_remaining_after_janko_two_dihedral
      lit hExceptionalOrbits hTracey hCFSG remainingGoodSylow remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
