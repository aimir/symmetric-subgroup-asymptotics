import SymmetricSubgroupAsymptotics.EightPointMinimalFailureDegreeSixOrSeven
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixOrdinaryGeneratorsWithoutIndexInput
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSevenOrdinaryGeneratorsWithoutIndexInput
import SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement

/-! Eliminate the independent globally minimal failed eight-point action.
Only pinned CFSG is required (for the proved odd-order backend). No
Tracey/MN input, named-model callback, independent local IH or finite
classification premise is added. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.EightPointHalfDegreeCompleteCFSG
open EightPointHalfDegreeFiniteModelReduction

theorem no_primitive_sporadic_counterexample_eight (hCFSG : CFSG.CFSGClassification) :
    ¬Nonempty (PrimitiveSporadicCounterexample 8) := by
  rintro ⟨w⟩
  have hd := EightPointMinimalFailureDegreeSixOrSeven.degree_eq_six_or_seven w
  rcases w with ⟨d,hlo,hhi,J,ht,hp,hbad,hmin,D,s,e⟩
  change d=6 ∨ d=7 at hd
  rcases hd with h6 | h7
  · subst d
    have hr := PrimitiveDegreeSixOrdinaryGeneratorsWithoutIndexInput.genRank_le_three D
    omega
  · subst d
    have hr := PrimitiveDegreeSevenOrdinaryGeneratorsWithoutIndexInput.genRank_le_three hCFSG D
    omega

theorem no_cumulative_global_counterexample_eight (hCFSG : CFSG.CFSGClassification) :
    ¬Nonempty (OriginalAffineBoundedSharpCoTwoTopRefinement.CumulativeGlobalCounterexample 8) := by
  rintro ⟨w⟩
  exact no_primitive_sporadic_counterexample_eight hCFSG ⟨w.val⟩

theorem genRank_le_four (hCFSG : CFSG.CFSGClassification)
    (J : Subgroup (Equiv.Perm (Fin 8))) : MarkedC4.genRank J≤4 := by
  rcases EightPointHalfDegreeFiniteModelReduction.genRank_le_four_or_sporadic_counterexample
    hCFSG J with hpaid | hbad
  · exact hpaid
  · exact (no_primitive_sporadic_counterexample_eight hCFSG hbad).elim

end SymmetricSubgroupAsymptotics.EightPointHalfDegreeCompleteCFSG
