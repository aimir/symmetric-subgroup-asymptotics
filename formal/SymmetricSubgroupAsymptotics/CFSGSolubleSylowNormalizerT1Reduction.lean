import SymmetricSubgroupAsymptotics.CFSGRemainingSolubleSylowNormalizerModels

/-! The same T1 with the same three published bundles, pinned CFSG and
numerical21 callback, replacing Good12 by actual soluble Sylow-normalizer
generating conjugates on exactly the same twelve tags. No tag is deleted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction

/-- Extract the unchanged numerical21 reduction independently of the
soluble-generation proof. All field-family and finite-model facts are the
already proved original-model callbacks used by the previous T1 chain. -/
theorem sufficientSimpleIndex_of_remaining_Mathieu24
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterMathieuTwentyFourComplete i →
        ModelBoundsAfterMathieuTwentyFourIndexSquare i) :
    PrimitiveSocleRawStructure.SufficientSimpleIndexBounds := by
  apply sufficientSimpleIndexBounds_of_cfsg_after_unitary_rankTwo hCFSG
  intro i _ _ hn hi
  apply modelBoundsAfterUnitarySquare_of_after_twistedD_square i
  apply modelBoundsAfterTwistedDSquare_of_remaining_after_twistedD_outer i hn hi
  intro hiD
  apply modelBoundsAfterTwistedDSquare_of_remaining_after_unitary_outer i hn hiD
  intro hiU
  apply modelBoundsAfterTwistedDSquare_of_after_triality_index_square i
  apply modelBoundsAfterTrialitySquare_of_after_fFour_twistedE6_squares i
  apply modelBoundsAfterFFourTwistedE6Squares_of_remaining_after_twistedE6_outer i hiU
  intro hiE
  apply modelBoundsAfterFFourTwistedE6Squares_of_remaining_after_triality_outer i hiE
  intro hiTriality
  apply modelBoundsAfterFFourTwistedE6Squares_of_remaining_after_fFour_outer i hiTriality
  intro hiF
  apply modelBoundsAfterFFourTwistedE6Squares_of_after_GTwo_square i
  apply modelBoundsAfterGTwoSquare_of_remaining_after_GTwo_outer i hiF
  intro hiG
  apply modelBoundsAfterGTwoSquare_of_after_ReeGTwo_square i
  apply modelBoundsAfterReeGTwoSquare_of_remaining_after_ReeGTwo_outer i hiG
  intro hiRG
  apply modelBoundsAfterReeGTwoSquare_of_after_ReeFFour_square i
  apply modelBoundsAfterReeFFourSquare_of_remaining_after_ReeFFour_outer i hiRG
  intro hiRF
  have h24 := simpleIndex_callback_after_Mathieu24_complete remaining
  have h23 := simpleIndex_callback_after_Mathieu23_complete h24
  have h22 := simpleIndex_callback_after_Mathieu22_complete h23
  have h12 := simpleIndex_callback_after_Mathieu12_complete h22
  have h24square := simpleIndex_callback_after_Mathieu24_square h12
  have h23square := simpleIndex_callback_after_Mathieu23_square h24square
  have h12square := simpleIndex_callback_after_Mathieu12_square h23square
  have h11 := simpleIndex_callback_after_Mathieu11_complete h12square
  have h11square := simpleIndex_callback_after_Mathieu11_square h11
  have h22square := simpleIndex_callback_after_Mathieu22_square h11square
  exact modelBoundsAfterReeFFourSquare_of_after_Tits_square i hn
    (simpleIndex_callback_after_Tits h22square i hn hiRF)

end SymmetricSubgroupAsymptotics.CFSGReduction

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

theorem T1_of_three_published_inputs_cfsg_and_remaining_soluble_normalizer_pairs
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hTracey : TraceyPermutationGeneratorInput)
    (hCFSG : CFSG.CFSGClassification)
    (remainingNormalizerPairs : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterJankoTwoDihedral i →
        ∃ p, SolubleSylowNormalizerGeneration.SolubleSylowNormalizerPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuTwentyFourComplete i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyFourIndexSquare i) : T1 := by
  exact T1_of_six_published_inputs_and_sufficientSimpleIndex lit
    (SolubleSylowNormalizerGeneration.aschbacherGuralnick_of_cfsg_and_remaining
      hCFSG remainingNormalizerPairs)
    hExceptionalOrbits
    (CFSGTransitiveSubquadraticCount.transitiveCountInput_proved hCFSG)
    hTracey (TraceyPublished2018BoundedSharpCFSG.mcIverNeumann_of_coarse hCFSG hTracey)
    (CFSGReduction.sufficientSimpleIndex_of_remaining_Mathieu24 hCFSG remainingSimpleIndex)

theorem allTargets_of_three_published_inputs_cfsg_and_remaining_soluble_normalizer_pairs
    (lit : PreE7CharacterPublishedInputs)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hTracey : TraceyPermutationGeneratorInput)
    (hCFSG : CFSG.CFSGClassification)
    (remainingNormalizerPairs : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → CFSGReduction.RemainingGoodSylowIndexAfterJankoTwoDihedral i →
        ∃ p, SolubleSylowNormalizerGeneration.SolubleSylowNormalizerPrime i.Model p)
    (remainingSimpleIndex : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexAfterMathieuTwentyFourComplete i →
        CFSGReduction.ModelBoundsAfterMathieuTwentyFourIndexSquare i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_three_published_inputs_cfsg_and_remaining_soluble_normalizer_pairs
      lit hExceptionalOrbits hTracey hCFSG remainingNormalizerPairs remainingSimpleIndex)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
