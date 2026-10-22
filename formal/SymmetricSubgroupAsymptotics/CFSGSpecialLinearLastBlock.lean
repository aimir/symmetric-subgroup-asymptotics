import SymmetricSubgroupAsymptotics.CFSGSpecialLinearReindex
import SymmetricSubgroupAsymptotics.CFSGTypeABlockEmbedding

/-! The literal determinant-one block lift fixing the LAST coordinate.
Its elementary parameters and full natural vector action are explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSpecialLinearLastBlock
open CFSGTypeAElementaryMatrices CFSGSpecialLinearReindex CFSGTypeABlockEmbedding

def lastIndex (m : ℕ) : Unit ⊕ Fin m ≃ Fin (m + 1) where
  toFun := Sum.elim (fun _ => Fin.last m) Fin.castSucc
  invFun x := if h : x.val < m then Sum.inr ⟨x.val, h⟩ else Sum.inl ()
  left_inv x := by
    cases x with
    | inl u => cases u; simp
    | inr i => simp [i.isLt]
  right_inv x := by
    dsimp only
    split_ifs with hx
    · apply Fin.ext
      rfl
    · apply Fin.ext
      change m = x.val
      have := x.isLt
      omega

theorem lastIndex_left (m : ℕ) : lastIndex m (Sum.inl ()) = Fin.last m := rfl

theorem lastIndex_right (m : ℕ) (i : Fin m) : lastIndex m (Sum.inr i) = i.castSucc := rfl

theorem lastIndex_symm_left (m : ℕ) : (lastIndex m).symm (Fin.last m) = Sum.inl () :=
  (lastIndex m).symm_apply_apply (Sum.inl ())

theorem lastIndex_symm_right (m : ℕ) (i : Fin m) :
    (lastIndex m).symm i.castSucc = Sum.inr i :=
  (lastIndex m).symm_apply_apply (Sum.inr i)

variable (K : Type) [Field K] (m : ℕ)

def lastBlockHom : Matrix.SpecialLinearGroup (Fin m) K →* Matrix.SpecialLinearGroup (Fin (m + 1)) K :=
  (reindexHom (lastIndex m)).comp blockHom

theorem blockHom_elementary (i j : Fin m) (hij : i ≠ j) (a : K) :
    blockHom (elementary hij a) = elementary (Sum.inr_injective.ne hij) a := by
  apply Subtype.ext
  ext (x | x) (y | y) <;>
    simp [CFSGTypeABlockEmbedding.blockHom, Matrix.transvection, Matrix.single_apply, Matrix.one_apply]

theorem lastBlockHom_elementary (i j : Fin m) (hij : i ≠ j) (a : K) :
    lastBlockHom K m (elementary hij a) = elementary ((Fin.castSucc_injective m).ne hij) a := by
  change reindexHom (lastIndex m) (blockHom (elementary hij a)) = _
  rw [blockHom_elementary, reindexHom_elementary] <;> rfl

theorem lastBlockHom_mulVec (A : Matrix.SpecialLinearGroup (Fin m) K) (v : Fin (m + 1) → K) :
    (lastBlockHom K m A).val *ᵥ v =
      (Sum.elim (fun _ : Unit => v (Fin.last m))
        (A.val *ᵥ (fun i : Fin m => v i.castSucc))) ∘ (lastIndex m).symm := by
  change (reindexHom (lastIndex m) (blockHom A)).val *ᵥ v = _
  rw [reindexHom_mulVec, blockHom_coe, Matrix.fromBlocks_mulVec]
  simp only [Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
  rfl

end SymmetricSubgroupAsymptotics.CFSGSpecialLinearLastBlock
