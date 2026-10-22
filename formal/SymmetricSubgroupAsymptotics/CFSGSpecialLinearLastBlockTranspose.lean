import SymmetricSubgroupAsymptotics.CFSGSpecialLinearLastBlock
import SymmetricSubgroupAsymptotics.CFSGSpecialLinearTranspose

/-! The last-coordinate block embedding commutes with literal transpose
and inverse. These identities retain the contragredient action without
changing the original coordinate carrier. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSpecialLinearLastBlockTranspose
open CFSGSpecialLinearLastBlock CFSGSpecialLinearReindex CFSGTypeABlockEmbedding
variable {F K I J : Type} [Field F] [Field K]
variable [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem map_transpose (f : F →+* K) (A : Matrix.SpecialLinearGroup I F) :
    Matrix.SpecialLinearGroup.map f A.transpose =
      (Matrix.SpecialLinearGroup.map f A).transpose := by
  apply Subtype.ext
  rfl

theorem reindexHom_transpose (e : I ≃ J) (A : Matrix.SpecialLinearGroup I K) :
    reindexHom e A.transpose = (reindexHom e A).transpose := by
  apply Subtype.ext
  rfl

theorem blockHom_transpose (A : Matrix.SpecialLinearGroup I K) :
    blockHom A.transpose = (blockHom A).transpose := by
  apply Subtype.ext
  change Matrix.fromBlocks (1 : Matrix Unit Unit K) 0 0 A.val.transpose =
    (Matrix.fromBlocks (1 : Matrix Unit Unit K) 0 0 A.val).transpose
  rw [Matrix.fromBlocks_transpose]
  simp only [Matrix.transpose_one, Matrix.transpose_zero]

theorem lastBlockHom_transpose (m : ℕ) (A : Matrix.SpecialLinearGroup (Fin m) K) :
    lastBlockHom K m A.transpose = (lastBlockHom K m A).transpose := by
  change reindexHom (lastIndex m) (blockHom A.transpose) = _
  rw [blockHom_transpose, reindexHom_transpose]
  rfl

theorem lastBlockHom_inverseTranspose (m : ℕ) (A : Matrix.SpecialLinearGroup (Fin m) K) :
    lastBlockHom K m (A⁻¹).transpose = ((lastBlockHom K m A)⁻¹).transpose := by
  rw [lastBlockHom_transpose, map_inv]

end SymmetricSubgroupAsymptotics.CFSGSpecialLinearLastBlockTranspose
