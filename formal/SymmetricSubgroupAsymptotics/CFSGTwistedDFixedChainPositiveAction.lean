import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedChainAction

/-! Positive-coordinate action of the literal fixed-field SL chain block.
The zero negative half remains zero, without a characteristic assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedChainPositiveAction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationSLDouble
open CFSGTwistedA2FixedField CFSGTwistedDFixedChainLift
open CFSGTwistedDFixedChainAction CFSGSpecialLinearLastBlock

theorem positive_action (s : ℕ) (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin (s + 3)) (fixedField q))
    (v : Index (s + 4) → q.Extension 2) :
    (((fixedChainLift s q A).val : Mat (q.Extension 2) (s + 4)) *ᵥ v) ∘ Sum.inl =
      (lastBlockHom (q.Extension 2) (s + 3)
        (Matrix.SpecialLinearGroup.map (fixedField q).subtype A)).val *ᵥ (v ∘ Sum.inl) := by
  rw [fixedChainLift_val]
  unfold doubleMatrix
  rw [Matrix.fromBlocks_mulVec]
  funext i
  simp only [Function.comp_apply, Sum.elim_inl, Matrix.zero_mulVec, add_zero]

theorem positive_castSucc (s : ℕ) (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin (s + 3)) (fixedField q))
    (v : Index (s + 4) → q.Extension 2) (i : Fin (s + 3)) :
    (((fixedChainLift s q A).val : Mat (q.Extension 2) (s + 4)) *ᵥ v) (Sum.inl i.castSucc) =
      ((Matrix.SpecialLinearGroup.map (fixedField q).subtype A).val *ᵥ
        (fun j : Fin (s + 3) => v (Sum.inl j.castSucc))) i := by
  have h := congrFun (positive_action s q A v) i.castSucc
  rw [lastBlockHom_mulVec] at h
  simpa only [Function.comp_apply, lastIndex_symm_right, Sum.elim_inr] using h

theorem positive_last (s : ℕ) (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin (s + 3)) (fixedField q))
    (v : Index (s + 4) → q.Extension 2) :
    (((fixedChainLift s q A).val : Mat (q.Extension 2) (s + 4)) *ᵥ v)
        (Sum.inl (Fin.last (s + 3))) = v (Sum.inl (Fin.last (s + 3))) := by
  have h := congrFun (positive_action s q A v) (Fin.last (s + 3))
  rw [lastBlockHom_mulVec] at h
  simpa only [Function.comp_apply, lastIndex_symm_left, Sum.elim_inl] using h

theorem negative_zero (s : ℕ) (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin (s + 3)) (fixedField q))
    (v : Index (s + 4) → q.Extension 2) (hv : v ∘ Sum.inr = 0) :
    (((fixedChainLift s q A).val : Mat (q.Extension 2) (s + 4)) *ᵥ v) ∘ Sum.inr = 0 := by
  rw [negative_action, hv, Matrix.mulVec_zero]

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedChainPositiveAction
