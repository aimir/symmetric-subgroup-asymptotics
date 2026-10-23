import SymmetricSubgroupAsymptotics.CFSGHermitianCorrectionRange
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitarySubspaceCompression
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRankTwoSingularSpan

/-! The actual five-space head correction parametrizes the WHOLE joint
perpendicular and retains the original three-space residual norm. Literal
singular spanning then supplies an outside singular witness whenever the
actual correction range is not contained in the specified submodule. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters
open CFSGHermitianHyperbolicCompression CFSGHermitianOrthogonalSpan

private theorem head_middle_zero (q : CFSG.PrimePower) (v : Fin 3 → q.Extension 2) :
    unitaryNaturalPair q 4 (Pi.single (0 : Fin 5) 1) (unitaryMiddleVector q 2 v) = 0 := by
  rw [unitaryNaturalPair_first]
  have hh : unitarySplitLinearEquiv q 2 (unitaryMiddleVector q 2 v) = middleVector v :=
    (unitarySplitLinearEquiv q 2).apply_symm_apply _
  have he := congrArg (fun x => x (.inr (.inr ()))) hh
  change unitaryMiddleVector q 2 v (Fin.last 4) = 0 at he
  exact he

private theorem head_zero (q : CFSG.PrimePower) :
    unitaryNaturalPair q 4 (Pi.single (0 : Fin 5) 1) (Pi.single 0 1) = 0 := by
  rw [unitaryNaturalPair_first]
  norm_num [Pi.single_apply, Fin.ext_iff]

def unitaryHeadCorrection (q : CFSG.PrimePower) (w : Fin 5 → q.Extension 2) :
    (Fin 3 → q.Extension 2) →ₗ[q.Extension 2] (Fin 5 → q.Extension 2) :=
  CFSGHermitianTransverseCorrection.correction (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4)
    (Pi.single 0 1) w (unitaryMiddleVector q 2)

theorem unitaryHeadCorrection_pair (q : CFSG.PrimePower) (w : Fin 5 → q.Extension 2)
    (u v : Fin 3 → q.Extension 2) :
    unitaryNaturalPair q 4 (unitaryHeadCorrection q w u) (unitaryHeadCorrection q w v) =
      -unitaryNaturalPair q 2 u v := by
  have hh := CFSGHermitianTransverseCorrection.correction_pairing (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4)
    (Pi.single 0 1) w (unitaryMiddleVector q 2) (head_zero q) (head_middle_zero q)
    (fun z => (unitaryNaturalPair_zero_swap q 4 _ _).mp (head_middle_zero q z)) u v
  exact hh.trans (unitaryMiddleVector_pair q 2 u v)

theorem unitaryHeadCorrection_orthogonal (q : CFSG.PrimePower) (w : Fin 5 → q.Extension 2)
    (hw : unitaryNaturalPair q 4 w (Pi.single (0 : Fin 5) 1) ≠ 0) (v : Fin 3 → q.Extension 2) :
    unitaryNaturalPair q 4 (Pi.single (0 : Fin 5) 1) (unitaryHeadCorrection q w v) = 0 ∧
      unitaryNaturalPair q 4 w (unitaryHeadCorrection q w v) = 0 := by
  exact ⟨CFSGHermitianTransverseCorrection.correction_orthogonal_to _ _ _ _ _ _
      (head_zero q) (head_middle_zero q) v,
    CFSGHermitianTransverseCorrection.correction_orthogonal _ _ _ _ _ hw v⟩

theorem unitaryHeadCorrection_range (q : CFSG.PrimePower) (w : Fin 5 → q.Extension 2)
    (hw : unitaryNaturalPair q 4 w (Pi.single (0 : Fin 5) 1) ≠ 0) :
    (unitaryHeadCorrection q w).range =
      (pairRightLinear (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4) (Pi.single 0 1)).ker ⊓
      (pairRightLinear (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4) w).ker := by
  apply CFSGHermitianTransverseCorrection.correction_range_eq_joint _ _ _ _
    (unitaryMiddleVector q 2) (unitaryMiddleProjection q 2) (fun x => x 0)
    hw (head_zero q) (head_middle_zero q)
  intro x hx
  apply unitary_vector_decomposition q 2 x
  exact (unitaryNaturalPair_first q 4 x).symm.trans hx

theorem exists_unitaryHeadCorrection_singular_outside (q : CFSG.PrimePower)
    (w : Fin 5 → q.Extension 2)
    (hw : unitaryNaturalPair q 4 w (Pi.single (0 : Fin 5) 1) ≠ 0)
    (W : Submodule (q.Extension 2) (Fin 5 → q.Extension 2))
    (hnot : ¬ (unitaryHeadCorrection q w).range ≤ W) :
    ∃ v : Fin 5 → q.Extension 2, v ≠ 0 ∧ unitaryNaturalPair q 4 v v = 0 ∧ v ∉ W ∧
      unitaryNaturalPair q 4 (Pi.single (0 : Fin 5) 1) v = 0 ∧ unitaryNaturalPair q 4 w v = 0 := by
  classical
  have hex : ∃ u : Fin 3 → q.Extension 2,
      unitaryNaturalPair q 2 u u = 0 ∧ unitaryHeadCorrection q w u ∉ W := by
    by_contra hn
    push_neg at hn
    apply hnot
    have hle : Submodule.span (q.Extension 2)
        {u : Fin 3 → q.Extension 2 | unitaryNaturalPair q 2 u u = 0} ≤
        W.comap (unitaryHeadCorrection q w) :=
      Submodule.span_le.mpr (fun u hu => hn u hu)
    rw [unitary_rankTwo_singular_span_eq_top] at hle
    rintro v ⟨u, rfl⟩
    exact hle trivial
  obtain ⟨u, hu, huW⟩ := hex
  have hv0 : unitaryHeadCorrection q w u ≠ 0 := fun h => huW (h ▸ W.zero_mem)
  refine ⟨unitaryHeadCorrection q w u, hv0, ?_, huW, ?_⟩
  · rw [unitaryHeadCorrection_pair, hu, neg_zero]
  · exact unitaryHeadCorrection_orthogonal q w hw u

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
