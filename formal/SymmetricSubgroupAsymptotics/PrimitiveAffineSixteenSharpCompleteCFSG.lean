import SymmetricSubgroupAsymptotics.EightPointHalfDegreeCompleteCFSG
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenEightPointSharpReduction

/-! The primitive affine degree-sixteen sharp bound from pinned CFSG.
The actual eight-point complement action is retained. The independent
failed eight-point witness in the earlier reduction is now contradicted
by the complete half-degree theorem, with no numerical model callback.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenSharpCompleteCFSG
open TraceySharpHalfDegreeNumerics

theorem linear_genRank_le_four (hCFSG : CFSG.CFSGClassification)
    {H : Type} [Group H] [Finite H]
    (f : H →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))
    (hf : Function.Injective f) : MarkedC4.genRank H ≤ 4 := by
  exact (PrimitiveAffineSixteenEightPointSharpReduction.genRank_le_four_of_injective_or_sporadic_counterexample hCFSG f hf).resolve_right
      (EightPointHalfDegreeCompleteCFSG.no_primitive_sporadic_counterexample_eight hCFSG)

variable {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P in
theorem genRank_le_five (hCFSG : CFSG.CFSGClassification)
    (hprimitive : MulAction.IsPreprimitive G X) (hdegree : Nat.card X = 16) :
    MarkedC4.genRank G ≤ 5 := by
  exact (PrimitiveAffineSixteenEightPointSharpReduction.genRank_le_five_or_sporadic_counterexample P hCFSG hprimitive hdegree).resolve_right
      (EightPointHalfDegreeCompleteCFSG.no_primitive_sporadic_counterexample_eight hCFSG)

include P in
theorem genRank_le_sharpFloor (hCFSG : CFSG.CFSGClassification)
    (hprimitive : MulAction.IsPreprimitive G X) (hdegree : Nat.card X = 16) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) := by
  exact (PrimitiveAffineSixteenEightPointSharpReduction.genRank_le_sharpFloor_or_sporadic_counterexample P hCFSG hprimitive hdegree).resolve_right
      (EightPointHalfDegreeCompleteCFSG.no_primitive_sporadic_counterexample_eight hCFSG)

include P in
theorem exists_generating_finset (hCFSG : CFSG.CFSGClassification)
    (hprimitive : MulAction.IsPreprimitive G X) (hdegree : Nat.card X = 16) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ S.card ≤ 5 := by
  exact (PrimitiveAffineSixteenEightPointSharpReduction.exists_generating_finset_or_sporadic_counterexample P hCFSG hprimitive hdegree).resolve_right
      (EightPointHalfDegreeCompleteCFSG.no_primitive_sporadic_counterexample_eight hCFSG)

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenSharpCompleteCFSG
