import SymmetricSubgroupAsymptotics.CFSGJankoTwoDihedralT1Reduction
import SymmetricSubgroupAsymptotics.SolubleSylowNormalizerModelReduction

/-! The exact twelve remaining tags retain their old guard. Every closed
GoodSylow branch coerces to the weaker normalizer-pair property. This file
does not yet delete an unchecked native J3/McL/HS branch. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SolubleSylowNormalizerGeneration
open CFSGReduction

theorem normalizer_callback_after_ReeFFour
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterReeFFour i →
        ∃ p, SolubleSylowNormalizerPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingGoodSylowIndexAfterReeGTwo i) :
    ∃ p, SolubleSylowNormalizerPrime i.Model p := by
  by_cases hree : ∃ (m : ℕ) (hm : 1 ≤ m), i = .reeF4 m hm
  · obtain ⟨m,hm,rfl⟩ := hree
    exact ⟨2, of_goodSylowPrime (CFSGReeFFourOriginalGoodSylow.original_goodSylowPrime m (by omega))⟩
  · apply remaining i hn
    exact ⟨hi,fun m hm he => hree ⟨m,hm,he⟩⟩

theorem normalizer_callback_after_Tits
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterTits i →
        ∃ p, SolubleSylowNormalizerPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingGoodSylowIndexAfterReeFFour i) :
    ∃ p, SolubleSylowNormalizerPrime i.Model p := by
  by_cases ht : i = .tits
  · subst i
    exact ⟨2, of_goodSylowPrime (tits_goodSylowPrime)⟩
  · exact remaining i hn ⟨hi, ht⟩

theorem normalizer_callback_after_Mathieu22
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterMathieuTwentyTwo i →
        ∃ p, SolubleSylowNormalizerPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingGoodSylowIndexAfterTits i) :
    ∃ p, SolubleSylowNormalizerPrime i.Model p := by
  by_cases hm : i=.sporadic .m22
  · subst i
    exact ⟨11, of_goodSylowPrime (CFSGMathieuTwentyTwoGoodSylowEleven.goodSylowPrime)⟩
  · exact remaining i hn ⟨hi,hm⟩

theorem normalizer_callback_after_Mathieu11
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterMathieuEleven i →
        ∃ p, SolubleSylowNormalizerPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingGoodSylowIndexAfterMathieuTwentyTwo i) :
    ∃ p, SolubleSylowNormalizerPrime i.Model p := by
  by_cases hm : i=.sporadic .m11
  · subst i
    letI : Finite CFSG.Models.Presentations.M11.Model :=
      inferInstanceAs (Finite ((CFSG.Index.sporadic .m11).Model))
    letI : IsSimpleGroup CFSG.Models.Presentations.M11.Model :=
      inferInstanceAs (IsSimpleGroup ((CFSG.Index.sporadic .m11).Model))
    exact ⟨2, of_goodSylowPrime (CFSGMathieuElevenGoodSylowTwo.goodSylowPrime)⟩
  · exact remaining i hn ⟨hi,hm⟩

theorem normalizer_callback_after_Mathieu12
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterMathieuTwelve i →
        ∃ p, SolubleSylowNormalizerPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingGoodSylowIndexAfterMathieuEleven i) :
    ∃ p, SolubleSylowNormalizerPrime i.Model p := by
  by_cases hm : i = .sporadic .m12
  · subst i
    letI : Finite CFSG.Models.Presentations.M12.Model :=
      inferInstanceAs (Finite ((CFSG.Index.sporadic .m12).Model))
    letI : IsSimpleGroup CFSG.Models.Presentations.M12.Model :=
      inferInstanceAs (IsSimpleGroup ((CFSG.Index.sporadic .m12).Model))
    exact ⟨11, of_goodSylowPrime (CFSGMathieuTwelveGoodSylowEleven.goodSylowPrime)⟩
  · exact remaining i hn ⟨hi, hm⟩

theorem normalizer_callback_after_Mathieu23
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterMathieuTwentyThree i →
        ∃ p, SolubleSylowNormalizerPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingGoodSylowIndexAfterMathieuTwelve i) :
    ∃ p, SolubleSylowNormalizerPrime i.Model p := by
  by_cases hm : i = .sporadic .m23
  · subst i
    letI : Finite CFSG.Models.Presentations.M23.Model :=
      inferInstanceAs (Finite ((CFSG.Index.sporadic .m23).Model))
    letI : IsSimpleGroup CFSG.Models.Presentations.M23.Model :=
      inferInstanceAs (IsSimpleGroup ((CFSG.Index.sporadic .m23).Model))
    exact ⟨23, of_goodSylowPrime (CFSGMathieuTwentyThreeGoodSylowTwentyThree.goodSylowPrime)⟩
  · exact remaining i hn ⟨hi, hm⟩

theorem normalizer_callback_after_Mathieu24
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterMathieuTwentyFour i →
        ∃ p, SolubleSylowNormalizerPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) (hi : RemainingGoodSylowIndexAfterMathieuTwentyThree i) :
    ∃ p, SolubleSylowNormalizerPrime i.Model p := by
  by_cases hm : i = .sporadic .m24
  · subst i
    letI : Finite CFSG.Models.Presentations.M24.Model :=
      inferInstanceAs (Finite ((CFSG.Index.sporadic .m24).Model))
    letI : IsSimpleGroup CFSG.Models.Presentations.M24.Model :=
      inferInstanceAs (IsSimpleGroup ((CFSG.Index.sporadic .m24).Model))
    exact ⟨23, of_goodSylowPrime (CFSGMathieuTwentyFourGoodSylowTwentyThree.goodSylowPrime)⟩
  · exact remaining i hn ⟨hi, hm⟩

theorem normalizer_callback_after_Ru_binary
    (hCFSG : CFSG.CFSGClassification)
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
    exact ⟨2, of_goodSylowPrime (CFSGRuBinaryPowerGoodSylow.goodSylowPrime hCFSG hn)⟩
  · exact remaining i hn ⟨hi,hm⟩

theorem normalizer_callback_after_ON_binary
    (hCFSG : CFSG.CFSGClassification)
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
    exact ⟨2, of_goodSylowPrime (CFSGONBinaryPowerGoodSylow.goodSylowPrime hCFSG hn)⟩
  · exact remaining i hn ⟨hi,hm⟩

theorem normalizer_callback_after_binary_frames
    (hCFSG : CFSG.CFSGClassification)
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
    exact ⟨2, of_goodSylowPrime (CFSGJankoOneBinaryFrameGoodSylow.goodSylowPrime hCFSG)⟩
  · by_cases hf22 : i = .sporadic .fi22
    · subst i
      letI : Finite (CFSG.Models.YGroups.SimpleSection CFSG.Models.YGroups.arms332) :=
        inferInstanceAs (Finite ((CFSG.Index.sporadic .fi22).Model))
      exact ⟨2, of_goodSylowPrime (CFSGYBinaryDerivedFrames.goodSylowPrime CFSG.Models.YGroups.arms332 hCFSG)⟩
    · by_cases hf23 : i = .sporadic .fi23
      · subst i
        letI : Finite (CFSG.Models.YGroups.SimpleSection CFSG.Models.YGroups.arms432) :=
          inferInstanceAs (Finite ((CFSG.Index.sporadic .fi23).Model))
        exact ⟨2, of_goodSylowPrime (CFSGYBinaryDerivedFrames.goodSylowPrime CFSG.Models.YGroups.arms432 hCFSG)⟩
      · by_cases hf24 : i = .sporadic .fi24Prime
        · subst i
          letI : Finite (CFSG.Models.YGroups.SimpleSection CFSG.Models.YGroups.arms442) :=
            inferInstanceAs (Finite ((CFSG.Index.sporadic .fi24Prime).Model))
          exact ⟨2, of_goodSylowPrime (CFSGYBinaryDerivedFrames.goodSylowPrime CFSG.Models.YGroups.arms442 hCFSG)⟩
        · by_cases hb : i = .sporadic .babyMonster
          · subst i
            letI : Finite (CFSG.Models.YGroups.SimpleSection CFSG.Models.YGroups.arms433) :=
              inferInstanceAs (Finite ((CFSG.Index.sporadic .babyMonster).Model))
            exact ⟨2, of_goodSylowPrime (CFSGYBinaryDerivedFrames.goodSylowPrime CFSG.Models.YGroups.arms433 hCFSG)⟩
          · exact remaining i hn ⟨hi, hm, hf22, hf23, hf24, hb⟩

theorem normalizer_callback_after_suz_bray
    (hCFSG : CFSG.CFSGClassification)
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
    exact ⟨2, of_goodSylowPrime (CFSGSuzOddRotationGoodSylow.goodSylowPrime hCFSG hn)⟩
  · exact remaining i hn ⟨hi,hs⟩

theorem normalizer_callback_after_janko_two_dihedral
    (hCFSG : CFSG.CFSGClassification)
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
    exact ⟨2, of_goodSylowPrime (CFSGJankoTwoDihedralBinaryGoodSylow.goodSylowPrime hCFSG)⟩
  · exact remaining i hn ⟨hi,hj⟩

theorem models_of_remaining (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterJankoTwoDihedral i →
        ∃ p, SolubleSylowNormalizerPrime i.Model p)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬IsMulCommutative i.Model) : ∃ p, SolubleSylowNormalizerPrime i.Model p := by
  rcases model_goodSylow_or_remaining_after_ReeGTwo i hn with h | hi
  · obtain ⟨p, hp⟩ := h
    exact ⟨p, of_goodSylowPrime hp⟩
  · exact (normalizer_callback_after_ReeFFour (normalizer_callback_after_Tits (normalizer_callback_after_Mathieu22 (normalizer_callback_after_Mathieu11 (normalizer_callback_after_Mathieu12 (normalizer_callback_after_Mathieu23 (normalizer_callback_after_Mathieu24 (normalizer_callback_after_Ru_binary hCFSG (normalizer_callback_after_ON_binary hCFSG (normalizer_callback_after_binary_frames hCFSG (normalizer_callback_after_suz_bray hCFSG (normalizer_callback_after_janko_two_dihedral hCFSG remaining)))))))))))) i hn hi

theorem aschbacherGuralnick_of_cfsg_and_remaining
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingGoodSylowIndexAfterJankoTwoDihedral i →
        ∃ p, SolubleSylowNormalizerPrime i.Model p) :
    MarkedC4.PublishedAschbacherGuralnickSolubleGeneration :=
  aschbacherGuralnick_of_cfsg_normalizerPair_models hCFSG (models_of_remaining hCFSG remaining)

end SymmetricSubgroupAsymptotics.SolubleSylowNormalizerGeneration
