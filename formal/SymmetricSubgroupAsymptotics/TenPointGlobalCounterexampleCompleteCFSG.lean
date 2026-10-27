import SymmetricSubgroupAsymptotics.PrimitiveTenOrdinaryGeneratorsFromNineCFSG
import SymmetricSubgroupAsymptotics.TenPointMinimalFailureDegreeNineOrTen

/-! Close the independent globally minimal failed action through10.
The SAME original witness is below8 (already impossible), primitive9,
or primitive10. No local original-action IH is substituted for this
independent global witness and no model callback is introduced. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TenPointGlobalCounterexampleCompleteCFSG
open EightPointHalfDegreeFiniteModelReduction

 theorem no_primitive_sporadic_counterexample_ten (hCFSG : CFSG.CFSGClassification) :
    ¬Nonempty (PrimitiveSporadicCounterexample 10) := by
  rintro ⟨w⟩
  have hd := TenPointMinimalFailureDegreeNineOrTen.degree_eq_nine_or_ten hCFSG w
  rcases w with ⟨d,hlo,hhi,J,ht,hp,hbad,hmin,D,s,e⟩
  change d=9 ∨ d=10 at hd
  rcases hd with h9 | h10
  · subst d
    have hr := PrimitiveNineOrdinaryGeneratorsWithoutClassification.genRank_le_four J hp
    omega
  · subst d
    have hr := PrimitiveTenOrdinaryGeneratorsFromNineCFSG.genRank_le_five hCFSG J hp
    omega

 theorem no_cumulative_global_counterexample_ten (hCFSG : CFSG.CFSGClassification) :
    ¬Nonempty (OriginalAffineBoundedSharpCoTwoTopRefinement.CumulativeGlobalCounterexample 10) := by
  rintro ⟨w⟩
  exact no_primitive_sporadic_counterexample_ten hCFSG ⟨w.val⟩

end SymmetricSubgroupAsymptotics.TenPointGlobalCounterexampleCompleteCFSG
