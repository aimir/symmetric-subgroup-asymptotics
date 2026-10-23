import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankChainLift
import SymmetricSubgroupAsymptotics.CFSGSpecialLinearLastBlockTranspose

/-! Exact natural positive and contragredient negative action of the
literal fixed-field chain lift already in the genuine low ranks. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankChainAction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationSLDouble
open CFSGTwistedA2FixedField CFSGTwistedDAllRankChainLift
open CFSGSpecialLinearLastBlock CFSGSpecialLinearLastBlockTranspose

theorem chainLift_val (n : ℕ) (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin (n + 1)) (fixedField q)) :
    (chainLift n q A : Mat (q.Extension 2) (n + 2)) =
      doubleMatrix (q.Extension 2) (n + 2)
        (lastBlockHom (q.Extension 2) (n + 1)
          (Matrix.SpecialLinearGroup.map (fixedField q).subtype A)) := rfl

theorem negative_action (n : ℕ) (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin (n + 1)) (fixedField q))
    (v : Index (n + 2) → q.Extension 2) :
    ((chainLift n q A : Mat (q.Extension 2) (n + 2)) *ᵥ v) ∘ Sum.inr =
      (lastBlockHom (q.Extension 2) (n + 1)
        (Matrix.SpecialLinearGroup.map (fixedField q).subtype (A⁻¹).transpose)).val *ᵥ
          (v ∘ Sum.inr) := by
  rw [chainLift_val]
  have he :
      ((lastBlockHom (q.Extension 2) (n + 1)
        (Matrix.SpecialLinearGroup.map (fixedField q).subtype A))⁻¹).val.transpose =
      (lastBlockHom (q.Extension 2) (n + 1)
        (Matrix.SpecialLinearGroup.map (fixedField q).subtype (A⁻¹).transpose)).val := by
    rw [map_transpose, map_inv, lastBlockHom_transpose, map_inv]
    rfl
  unfold doubleMatrix
  rw [Matrix.fromBlocks_mulVec]
  funext i
  simp only [Function.comp_apply, Sum.elim_inr, Matrix.zero_mulVec, zero_add, he]

theorem inverseTranspose_negative_action (n : ℕ) (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin (n + 1)) (fixedField q))
    (v : Index (n + 2) → q.Extension 2) :
    ((chainLift n q (A⁻¹).transpose : Mat (q.Extension 2) (n + 2)) *ᵥ v) ∘ Sum.inr =
      (Sum.elim (fun _ : Unit => v (Sum.inr (Fin.last (n + 1))))
        ((Matrix.SpecialLinearGroup.map (fixedField q).subtype A).val *ᵥ
          (fun i : Fin (n + 1) => v (Sum.inr i.castSucc)))) ∘
            (lastIndex (n + 1)).symm := by
  rw [negative_action, CFSGSpecialLinearTranspose.inverseTranspose_twice,
    lastBlockHom_mulVec]
  rfl

theorem inverseTranspose_negative_castSucc (n : ℕ) (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin (n + 1)) (fixedField q))
    (v : Index (n + 2) → q.Extension 2) (i : Fin (n + 1)) :
    ((chainLift n q (A⁻¹).transpose : Mat (q.Extension 2) (n + 2)) *ᵥ v)
        (Sum.inr i.castSucc) =
      ((Matrix.SpecialLinearGroup.map (fixedField q).subtype A).val *ᵥ
        (fun j : Fin (n + 1) => v (Sum.inr j.castSucc))) i := by
  have h := congrFun (inverseTranspose_negative_action n q A v) i.castSucc
  simpa only [Function.comp_apply, lastIndex_symm_right, Sum.elim_inr] using h

theorem inverseTranspose_negative_last (n : ℕ) (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin (n + 1)) (fixedField q))
    (v : Index (n + 2) → q.Extension 2) :
    ((chainLift n q (A⁻¹).transpose : Mat (q.Extension 2) (n + 2)) *ᵥ v)
        (Sum.inr (Fin.last (n + 1))) = v (Sum.inr (Fin.last (n + 1))) := by
  have h := congrFun (inverseTranspose_negative_action n q A v) (Fin.last (n + 1))
  simpa only [Function.comp_apply, lastIndex_symm_left, Sum.elim_inl] using h

theorem positive_action (n : ℕ) (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin (n + 1)) (fixedField q))
    (v : Index (n + 2) → q.Extension 2) :
    ((chainLift n q A : Mat (q.Extension 2) (n + 2)) *ᵥ v) ∘ Sum.inl =
      (lastBlockHom (q.Extension 2) (n + 1)
        (Matrix.SpecialLinearGroup.map (fixedField q).subtype A)).val *ᵥ (v ∘ Sum.inl) := by
  rw [chainLift_val]
  unfold doubleMatrix
  rw [Matrix.fromBlocks_mulVec]
  funext i
  simp only [Function.comp_apply, Sum.elim_inl, Matrix.zero_mulVec, add_zero]

theorem positive_castSucc (n : ℕ) (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin (n + 1)) (fixedField q))
    (v : Index (n + 2) → q.Extension 2) (i : Fin (n + 1)) :
    ((chainLift n q A : Mat (q.Extension 2) (n + 2)) *ᵥ v) (Sum.inl i.castSucc) =
      ((Matrix.SpecialLinearGroup.map (fixedField q).subtype A).val *ᵥ
        (fun j : Fin (n + 1) => v (Sum.inl j.castSucc))) i := by
  have h := congrFun (positive_action n q A v) i.castSucc
  rw [lastBlockHom_mulVec] at h
  simpa only [Function.comp_apply, lastIndex_symm_right, Sum.elim_inr] using h

theorem positive_last (n : ℕ) (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin (n + 1)) (fixedField q))
    (v : Index (n + 2) → q.Extension 2) :
    ((chainLift n q A : Mat (q.Extension 2) (n + 2)) *ᵥ v)
        (Sum.inl (Fin.last (n + 1))) = v (Sum.inl (Fin.last (n + 1))) := by
  have h := congrFun (positive_action n q A v) (Fin.last (n + 1))
  rw [lastBlockHom_mulVec] at h
  simpa only [Function.comp_apply, lastIndex_symm_left, Sum.elim_inl] using h

theorem negative_zero (n : ℕ) (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin (n + 1)) (fixedField q))
    (v : Index (n + 2) → q.Extension 2) (hv : v ∘ Sum.inr = 0) :
    ((chainLift n q A : Mat (q.Extension 2) (n + 2)) *ᵥ v) ∘ Sum.inr = 0 := by
  rw [negative_action, hv, Matrix.mulVec_zero]

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankChainAction
