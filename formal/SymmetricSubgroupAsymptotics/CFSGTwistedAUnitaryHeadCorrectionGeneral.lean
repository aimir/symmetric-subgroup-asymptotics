import SymmetricSubgroupAsymptotics.CFSGHermitianCorrectionRange
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitarySubspaceCompression
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitarySingularSpan

/-! The actual arbitrary-rank head correction parametrizes the WHOLE joint
perpendicular and retains the original smaller residual norm. Literal
singular spanning then supplies an outside singular witness whenever the
actual correction range is not contained in the specified submodule. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters
open CFSGHermitianHyperbolicCompression CFSGHermitianOrthogonalSpan

private theorem general_head_middle_zero (q : CFSG.PrimePower) (n : ℕ) (v : Fin (n+3) → q.Extension 2) :
    unitaryNaturalPair q (n+4) (Pi.single (0 : Fin (n+5)) 1) (unitaryMiddleVector q (n+2) v) = 0 := by
  rw [unitaryNaturalPair_first]
  have hh : unitarySplitLinearEquiv q (n+2) (unitaryMiddleVector q (n+2) v) = middleVector v :=
    (unitarySplitLinearEquiv q (n+2)).apply_symm_apply _
  have he := congrArg (fun x => x (.inr (.inr ()))) hh
  change unitaryMiddleVector q (n+2) v (Fin.last (n+4)) = 0 at he
  exact he

private theorem general_head_zero (q : CFSG.PrimePower) (n : ℕ) :
    unitaryNaturalPair q (n+4) (Pi.single (0 : Fin (n+5)) 1) (Pi.single 0 1) = 0 := by
  rw [unitaryNaturalPair_first]
  norm_num [Pi.single_apply, Fin.ext_iff]

def unitaryHeadCorrectionGeneral (q : CFSG.PrimePower) (n : ℕ) (w : Fin (n+5) → q.Extension 2) :
    (Fin (n+3) → q.Extension 2) →ₗ[q.Extension 2] (Fin (n+5) → q.Extension 2) :=
  CFSGHermitianTransverseCorrection.correction (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (n+4) : Mat (q.Extension 2) (n+4))
    (Pi.single 0 1) w (unitaryMiddleVector q (n+2))

theorem unitaryHeadCorrectionGeneral_pair (q : CFSG.PrimePower) (n : ℕ) (w : Fin (n+5) → q.Extension 2)
    (u v : Fin (n+3) → q.Extension 2) :
    unitaryNaturalPair q (n+4) (unitaryHeadCorrectionGeneral q n w u) (unitaryHeadCorrectionGeneral q n w v) =
      -unitaryNaturalPair q (n+2) u v := by
  have hh := CFSGHermitianTransverseCorrection.correction_pairing (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (n+4) : Mat (q.Extension 2) (n+4))
    (Pi.single 0 1) w (unitaryMiddleVector q (n+2)) (general_head_zero q n) (general_head_middle_zero q n)
    (fun z => (unitaryNaturalPair_zero_swap q (n+4) _ _).mp (general_head_middle_zero q n z)) u v
  exact hh.trans (unitaryMiddleVector_pair q (n+2) u v)

theorem unitaryHeadCorrectionGeneral_orthogonal (q : CFSG.PrimePower) (n : ℕ) (w : Fin (n+5) → q.Extension 2)
    (hw : unitaryNaturalPair q (n+4) w (Pi.single (0 : Fin (n+5)) 1) ≠ 0) (v : Fin (n+3) → q.Extension 2) :
    unitaryNaturalPair q (n+4) (Pi.single (0 : Fin (n+5)) 1) (unitaryHeadCorrectionGeneral q n w v) = 0 ∧
      unitaryNaturalPair q (n+4) w (unitaryHeadCorrectionGeneral q n w v) = 0 := by
  exact ⟨CFSGHermitianTransverseCorrection.correction_orthogonal_to _ _ _ _ _ _
      (general_head_zero q n) (general_head_middle_zero q n) v,
    CFSGHermitianTransverseCorrection.correction_orthogonal _ _ _ _ _ hw v⟩

theorem unitaryHeadCorrectionGeneral_range (q : CFSG.PrimePower) (n : ℕ) (w : Fin (n+5) → q.Extension 2)
    (hw : unitaryNaturalPair q (n+4) w (Pi.single (0 : Fin (n+5)) 1) ≠ 0) :
    (unitaryHeadCorrectionGeneral q n w).range =
      (pairRightLinear (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (n+4) : Mat (q.Extension 2) (n+4)) (Pi.single 0 1)).ker ⊓
      (pairRightLinear (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (n+4) : Mat (q.Extension 2) (n+4)) w).ker := by
  apply CFSGHermitianTransverseCorrection.correction_range_eq_joint _ _ _ _
    (unitaryMiddleVector q (n+2)) (unitaryMiddleProjection q (n+2)) (fun x => x 0)
    hw (general_head_zero q n) (general_head_middle_zero q n)
  intro x hx
  apply unitary_vector_decomposition q (n+2) x
  exact (unitaryNaturalPair_first q (n+4) x).symm.trans hx

theorem exists_unitaryHeadCorrectionGeneral_singular_outside (q : CFSG.PrimePower) (n : ℕ)
    (w : Fin (n+5) → q.Extension 2)
    (hw : unitaryNaturalPair q (n+4) w (Pi.single (0 : Fin (n+5)) 1) ≠ 0)
    (W : Submodule (q.Extension 2) (Fin (n+5) → q.Extension 2))
    (hnot : ¬ (unitaryHeadCorrectionGeneral q n w).range ≤ W) :
    ∃ v : Fin (n+5) → q.Extension 2, v ≠ 0 ∧ unitaryNaturalPair q (n+4) v v = 0 ∧ v ∉ W ∧
      unitaryNaturalPair q (n+4) (Pi.single (0 : Fin (n+5)) 1) v = 0 ∧ unitaryNaturalPair q (n+4) w v = 0 := by
  classical
  have hex : ∃ u : Fin (n+3) → q.Extension 2,
      unitaryNaturalPair q (n+2) u u = 0 ∧ unitaryHeadCorrectionGeneral q n w u ∉ W := by
    by_contra hn
    push_neg at hn
    apply hnot
    have hle : Submodule.span (q.Extension 2)
        {u : Fin (n+3) → q.Extension 2 | unitaryNaturalPair q (n+2) u u = 0} ≤
        W.comap (unitaryHeadCorrectionGeneral q n w) :=
      Submodule.span_le.mpr (fun u hu => hn u hu)
    rw [unitary_singular_span_eq_top q (n+2) (by omega)] at hle
    rintro v ⟨u, rfl⟩
    exact hle trivial
  obtain ⟨u, hu, huW⟩ := hex
  have hv0 : unitaryHeadCorrectionGeneral q n w u ≠ 0 := fun h => huW (h ▸ W.zero_mem)
  refine ⟨unitaryHeadCorrectionGeneral q n w u, hv0, ?_, huW, ?_⟩
  · rw [unitaryHeadCorrectionGeneral_pair, hu, neg_zero]
  · exact unitaryHeadCorrectionGeneral_orthogonal q n w hw u

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
