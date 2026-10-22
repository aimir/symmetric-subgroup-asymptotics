import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedChainLift
import SymmetricSubgroupAsymptotics.CFSGSpecialLinearLastBlockTranspose

/-! Natural negative-coordinate action of the actual fixed-field chain
lift. Inverse transpose realizes an arbitrary SL action on those literal
coordinates while fixing the final negative coordinate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedChainAction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationSLDouble
open CFSGTwistedA2FixedField CFSGTwistedDFixedChainLift
open CFSGSpecialLinearLastBlock CFSGSpecialLinearLastBlockTranspose

theorem fixedChainLift_val (s : ℕ) (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin (s + 3)) (fixedField q)) :
    ((fixedChainLift s q A).val : Mat (q.Extension 2) (s + 4)) =
      doubleMatrix (q.Extension 2) (s + 4)
        (lastBlockHom (q.Extension 2) (s + 3)
          (Matrix.SpecialLinearGroup.map (fixedField q).subtype A)) := rfl

theorem negative_action (s : ℕ) (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin (s + 3)) (fixedField q))
    (v : Index (s + 4) → q.Extension 2) :
    (((fixedChainLift s q A).val : Mat (q.Extension 2) (s + 4)) *ᵥ v) ∘ Sum.inr =
      (lastBlockHom (q.Extension 2) (s + 3)
        (Matrix.SpecialLinearGroup.map (fixedField q).subtype (A⁻¹).transpose)).val *ᵥ
          (v ∘ Sum.inr) := by
  rw [fixedChainLift_val]
  have he :
      ((lastBlockHom (q.Extension 2) (s + 3)
        (Matrix.SpecialLinearGroup.map (fixedField q).subtype A))⁻¹).val.transpose =
      (lastBlockHom (q.Extension 2) (s + 3)
        (Matrix.SpecialLinearGroup.map (fixedField q).subtype (A⁻¹).transpose)).val := by
    rw [map_transpose, map_inv, lastBlockHom_transpose, map_inv]
    rfl
  unfold doubleMatrix
  rw [Matrix.fromBlocks_mulVec]
  funext i
  simp only [Function.comp_apply, Sum.elim_inr, Matrix.zero_mulVec, zero_add, he]

theorem inverseTranspose_negative_action (s : ℕ) (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin (s + 3)) (fixedField q))
    (v : Index (s + 4) → q.Extension 2) :
    (((fixedChainLift s q (A⁻¹).transpose).val : Mat (q.Extension 2) (s + 4)) *ᵥ v) ∘ Sum.inr =
      (Sum.elim (fun _ : Unit => v (Sum.inr (Fin.last (s + 3))))
        ((Matrix.SpecialLinearGroup.map (fixedField q).subtype A).val *ᵥ
          (fun i : Fin (s + 3) => v (Sum.inr i.castSucc)))) ∘
            (lastIndex (s + 3)).symm := by
  rw [negative_action, CFSGSpecialLinearTranspose.inverseTranspose_twice,
    lastBlockHom_mulVec]
  rfl

theorem inverseTranspose_negative_castSucc (s : ℕ) (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin (s + 3)) (fixedField q))
    (v : Index (s + 4) → q.Extension 2) (i : Fin (s + 3)) :
    (((fixedChainLift s q (A⁻¹).transpose).val : Mat (q.Extension 2) (s + 4)) *ᵥ v)
        (Sum.inr i.castSucc) =
      ((Matrix.SpecialLinearGroup.map (fixedField q).subtype A).val *ᵥ
        (fun j : Fin (s + 3) => v (Sum.inr j.castSucc))) i := by
  have h := congrFun (inverseTranspose_negative_action s q A v) i.castSucc
  simpa only [Function.comp_apply, lastIndex_symm_right, Sum.elim_inr] using h

theorem inverseTranspose_negative_last (s : ℕ) (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin (s + 3)) (fixedField q))
    (v : Index (s + 4) → q.Extension 2) :
    (((fixedChainLift s q (A⁻¹).transpose).val : Mat (q.Extension 2) (s + 4)) *ᵥ v)
        (Sum.inr (Fin.last (s + 3))) = v (Sum.inr (Fin.last (s + 3))) := by
  have h := congrFun (inverseTranspose_negative_action s q A v) (Fin.last (s + 3))
  simpa only [Function.comp_apply, lastIndex_symm_left, Sum.elim_inl] using h

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedChainAction
