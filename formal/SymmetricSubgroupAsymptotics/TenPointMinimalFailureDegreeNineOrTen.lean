import SymmetricSubgroupAsymptotics.EightPointHalfDegreeCompleteCFSG

/-! Preserve the independent original global failed action while using
the completed eight-point theorem only on the SAME smaller-degree witness.
No assertion that this group belongs to an earlier original action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TenPointMinimalFailureDegreeNineOrTen
open EightPointHalfDegreeFiniteModelReduction

theorem degree_eq_nine_or_ten (hCFSG : CFSG.CFSGClassification)
    (w : PrimitiveSporadicCounterexample 10) : w.degree=9 ∨ w.degree=10 := by
  by_cases h8 : w.degree≤8
  · apply (EightPointHalfDegreeCompleteCFSG.no_primitive_sporadic_counterexample_eight hCFSG ?_).elim
    exact ⟨⟨w.degree,w.degree_ge_four,h8,w.group,w.transitive,w.primitive,
      w.failed,w.minimal,w.socle,w.sporadic,w.equiv⟩⟩
  · have hhi := w.degree_le
    omega

theorem cumulative_degree_eq_nine_or_ten (hCFSG : CFSG.CFSGClassification)
    (w : OriginalAffineBoundedSharpCoTwoTopRefinement.CumulativeGlobalCounterexample 10) :
    w.val.degree=9 ∨ w.val.degree=10 :=
  degree_eq_nine_or_ten hCFSG w.val

end SymmetricSubgroupAsymptotics.TenPointMinimalFailureDegreeNineOrTen
