import SymmetricSubgroupAsymptotics.PrimitiveEightOrdinaryGeneratorsFromCanonicalCoverage
import SymmetricSubgroupAsymptotics.OriginalAffineBoundedSharpCoTwoTopRefinement

/-! The literal primitive eight-point action retained by every actual-top
obstruction has rank≤3, contradicting its failed-three field. No CFSG,
model callback, generator hypothesis or original-group IH is required. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ElementarySylowEightActualTopObstructionFalse

 theorem no_primitive_sporadic_obstruction
    (J : Subgroup (Equiv.Perm (Fin 8))) [MulAction.IsPretransitive J (Fin 8)]
    (P : Sylow 2 J) :
    ¬Nonempty (ElementarySylowEightOrdinaryCFSGReduction.PrimitiveSporadicObstruction J P) := by
  rintro ⟨w⟩
  exact (not_lt_of_ge (PrimitiveEightOrdinaryGeneratorsFromCanonicalCoverage.genRank_le_three
    J w.primitive)) w.failed_three

theorem no_actual_sporadic_obstruction {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] :
    ¬Nonempty (ElementarySylowEightFaithfulActionOrdinary.ActualSporadicObstruction
      (G := G) (X := X)) := by
  rintro ⟨w⟩
  exact (not_lt_of_ge (PrimitiveEightOrdinaryGeneratorsFromCanonicalCoverage.genRank_le_three
    _ w.obstruction.primitive)) w.obstruction.failed_three

theorem no_cumulative_actual_top_obstruction {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] :
    ¬Nonempty (OriginalAffineBoundedSharpCoTwoTopRefinement.CumulativeActualTopObstruction
      (G := G) (X := X)) := by
  rintro ⟨w⟩
  exact no_actual_sporadic_obstruction ⟨w.val⟩

theorem elementary_sylow_genRank_le_three (hCFSG : CFSG.CFSGClassification)
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X]
    (P : Sylow 2 G) (hel : ∀ g : P, g^2=1) (hdegree : Nat.card X=8) :
    MarkedC4.genRank G≤3 := by
  rcases ElementarySylowEightFaithfulActionOrdinary.genRank_le_three_or_actual_sporadic
    hCFSG P hel hdegree with hp | hbad
  · exact hp
  · exact (no_actual_sporadic_obstruction hbad).elim

end SymmetricSubgroupAsymptotics.ElementarySylowEightActualTopObstructionFalse
