import SymmetricSubgroupAsymptotics.CFSGRemainingSolubleSylowNormalizerModels
import SymmetricSubgroupAsymptotics.OddOrderSolvabilityClosedBinaryModels

/-! The same existing remaining12 callback, with every already closed
binary model consuming internally proved odd-order solvability. Earlier
Lie/Tits/Mathieu callback stages are reused unchanged. No old classification
or actual raw/old Monster identification is required by this model leaf.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueClosedNormalizerModels
open CFSGReduction SolubleSylowNormalizerGeneration
open SylowTwoNormalizerOfOddOrderSolvability (OddOrderSolvability)

theorem normalizer_callback_after_Ru_binary
    (hodd : OddOrderSolvability)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterRuBinary i →
        ∃ p, SolubleSylowNormalizerPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingGoodSylowIndexAfterMathieuTwentyFour i) :
    ∃ p, SolubleSylowNormalizerPrime i.Model p := by
  by_cases hm : i = .sporadic .ru
  · subst i
    letI : Finite CFSG.Models.MatrixGroups.Ru.Model :=
      inferInstanceAs (Finite ((CFSG.Index.sporadic .ru).Model))
    letI : IsSimpleGroup CFSG.Models.MatrixGroups.Ru.Model :=
      inferInstanceAs (IsSimpleGroup ((CFSG.Index.sporadic .ru).Model))
    exact ⟨2, of_goodSylowPrime (OddOrderSolvabilityClosedBinaryModels.Ru.goodSylowPrime hodd hn)⟩
  · exact remaining i hn ⟨hi,hm⟩

theorem normalizer_callback_after_ON_binary
    (hodd : OddOrderSolvability)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterONBinary i →
        ∃ p, SolubleSylowNormalizerPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingGoodSylowIndexAfterRuBinary i) :
    ∃ p, SolubleSylowNormalizerPrime i.Model p := by
  by_cases hm : i = .sporadic .onan
  · subst i
    letI : Finite CFSG.Models.MatrixGroups.ON.Model :=
      inferInstanceAs (Finite ((CFSG.Index.sporadic .onan).Model))
    letI : IsSimpleGroup CFSG.Models.MatrixGroups.ON.Model :=
      inferInstanceAs (IsSimpleGroup ((CFSG.Index.sporadic .onan).Model))
    exact ⟨2, of_goodSylowPrime (OddOrderSolvabilityClosedBinaryModels.ON.goodSylowPrime hodd hn)⟩
  · exact remaining i hn ⟨hi,hm⟩

theorem normalizer_callback_after_binary_frames
    (hodd : OddOrderSolvability)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterBinaryFrames i →
        ∃ p, SolubleSylowNormalizerPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingGoodSylowIndexAfterONBinary i) :
    ∃ p, SolubleSylowNormalizerPrime i.Model p := by
  by_cases hm : i = .sporadic .j1
  · subst i
    letI : Finite CFSG.Models.Presentations.J1.Model :=
      inferInstanceAs (Finite ((CFSG.Index.sporadic .j1).Model))
    letI : IsSimpleGroup CFSG.Models.Presentations.J1.Model :=
      inferInstanceAs (IsSimpleGroup ((CFSG.Index.sporadic .j1).Model))
    exact ⟨2, of_goodSylowPrime (OddOrderSolvabilityClosedBinaryModels.JankoOne.goodSylowPrime hodd)⟩
  · by_cases hf22 : i = .sporadic .fi22
    · subst i
      letI : Finite (CFSG.Models.YGroups.SimpleSection CFSG.Models.YGroups.arms332) :=
        inferInstanceAs (Finite ((CFSG.Index.sporadic .fi22).Model))
      exact ⟨2, of_goodSylowPrime (OddOrderSolvabilityClosedBinaryModels.Y.goodSylowPrime CFSG.Models.YGroups.arms332 hodd)⟩
    · by_cases hf23 : i = .sporadic .fi23
      · subst i
        letI : Finite (CFSG.Models.YGroups.SimpleSection CFSG.Models.YGroups.arms432) :=
          inferInstanceAs (Finite ((CFSG.Index.sporadic .fi23).Model))
        exact ⟨2, of_goodSylowPrime (OddOrderSolvabilityClosedBinaryModels.Y.goodSylowPrime CFSG.Models.YGroups.arms432 hodd)⟩
      · by_cases hf24 : i = .sporadic .fi24Prime
        · subst i
          letI : Finite (CFSG.Models.YGroups.SimpleSection CFSG.Models.YGroups.arms442) :=
            inferInstanceAs (Finite ((CFSG.Index.sporadic .fi24Prime).Model))
          exact ⟨2, of_goodSylowPrime (OddOrderSolvabilityClosedBinaryModels.Y.goodSylowPrime CFSG.Models.YGroups.arms442 hodd)⟩
        · by_cases hb : i = .sporadic .babyMonster
          · subst i
            letI : Finite (CFSG.Models.YGroups.SimpleSection CFSG.Models.YGroups.arms433) :=
              inferInstanceAs (Finite ((CFSG.Index.sporadic .babyMonster).Model))
            exact ⟨2, of_goodSylowPrime (OddOrderSolvabilityClosedBinaryModels.Y.goodSylowPrime CFSG.Models.YGroups.arms433 hodd)⟩
          · exact remaining i hn ⟨hi, hm, hf22, hf23, hf24, hb⟩

theorem normalizer_callback_after_suz_bray
    (hodd : OddOrderSolvability)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterSuzBray i →
        ∃ p,SolubleSylowNormalizerPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingGoodSylowIndexAfterBinaryFrames i) :
    ∃ p,SolubleSylowNormalizerPrime i.Model p := by
  by_cases hs : i = .sporadic .suz
  · subst i
    letI : Finite CFSG.Models.MatrixGroups.Suz.Model :=
      inferInstanceAs (Finite ((CFSG.Index.sporadic .suz).Model))
    exact ⟨2, of_goodSylowPrime (OddOrderSolvabilityClosedBinaryModels.Suz.goodSylowPrime hodd hn)⟩
  · exact remaining i hn ⟨hi,hs⟩

theorem normalizer_callback_after_janko_two_dihedral
    (hodd : OddOrderSolvability)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterJankoTwoDihedral i →
        ∃ p,SolubleSylowNormalizerPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingGoodSylowIndexAfterSuzBray i) :
    ∃ p,SolubleSylowNormalizerPrime i.Model p := by
  by_cases hj : i = .sporadic .j2
  · subst i
    letI : Finite CFSG.Models.Presentations.J2.Model :=
      inferInstanceAs (Finite ((CFSG.Index.sporadic .j2).Model))
    letI : IsSimpleGroup CFSG.Models.Presentations.J2.Model :=
      inferInstanceAs (IsSimpleGroup ((CFSG.Index.sporadic .j2).Model))
    exact ⟨2, of_goodSylowPrime (OddOrderSolvabilityClosedBinaryModels.JankoTwo.goodSylowPrime hodd)⟩
  · exact remaining i hn ⟨hi,hj⟩

theorem models_of_remaining (hodd : OddOrderSolvability)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterJankoTwoDihedral i →
        ∃ p, SolubleSylowNormalizerPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) : ∃ p, SolubleSylowNormalizerPrime i.Model p := by
  rcases model_goodSylow_or_remaining_after_ReeGTwo i hn with h | hi
  · obtain ⟨p, hp⟩ := h
    exact ⟨p, of_goodSylowPrime hp⟩
  · exact (normalizer_callback_after_ReeFFour (normalizer_callback_after_Tits (normalizer_callback_after_Mathieu22 (normalizer_callback_after_Mathieu11 (normalizer_callback_after_Mathieu12 (normalizer_callback_after_Mathieu23 (normalizer_callback_after_Mathieu24 (normalizer_callback_after_Ru_binary hodd (normalizer_callback_after_ON_binary hodd (normalizer_callback_after_binary_frames hodd (normalizer_callback_after_suz_bray hodd (normalizer_callback_after_janko_two_dihedral hodd remaining)))))))))))) i hn hi

end SymmetricSubgroupAsymptotics.ExtendedCatalogueClosedNormalizerModels
