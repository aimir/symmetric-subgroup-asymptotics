import SymmetricSubgroupAsymptotics.CFSGTypeAVectorTransitivity
import Mathlib.Data.Matrix.Block

/-! The actual determinant-one block embedding fixing one original
coordinate. Its action on the other coordinates is the original SL action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeABlockEmbedding
open Matrix
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

abbrev BigSL := Matrix.SpecialLinearGroup (Unit ⊕ n) F

def blockHom : Matrix.SpecialLinearGroup n F→*BigSL (F:=F) (n:=n) where
  toFun A := ⟨Matrix.fromBlocks (1 : Matrix Unit Unit F) 0 0 A.val,by
    rw [Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,A.property,one_mul]⟩
  map_one' := by
    apply Subtype.ext
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks,Matrix.one_apply]
  map_mul' A B := by
    apply Subtype.ext
    change Matrix.fromBlocks (1 : Matrix Unit Unit F) 0 0 (A.val*B.val)=
      Matrix.fromBlocks (1 : Matrix Unit Unit F) 0 0 A.val*
        Matrix.fromBlocks (1 : Matrix Unit Unit F) 0 0 B.val
    rw [Matrix.fromBlocks_multiply]
    simp

@[simp] theorem blockHom_coe (A : Matrix.SpecialLinearGroup n F) :
    (blockHom A).val=Matrix.fromBlocks (1 : Matrix Unit Unit F) 0 0 A.val := rfl

theorem blockHom_apply (A : Matrix.SpecialLinearGroup n F) (x : Unit ⊕ n→F) :
    (blockHom A).toLin' x=Sum.elim (x∘Sum.inl) (A.toLin' (x∘Sum.inr)) := by
  change Matrix.toLin' (blockHom A).val x=_
  rw [Matrix.toLin'_apply,blockHom_coe,Matrix.fromBlocks_mulVec]
  simp only [Matrix.one_mulVec,Matrix.zero_mulVec,add_zero,zero_add]
  rfl

def firstVector : Unit ⊕ n→F := Pi.single (Sum.inl ()) 1

@[simp] theorem blockHom_firstVector (A : Matrix.SpecialLinearGroup n F) :
    (blockHom A).toLin' (firstVector (F:=F) (n:=n))=firstVector := by
  rw [blockHom_apply]
  ext (i | j)
  · rfl
  · change A.toLin' (firstVector∘Sum.inr) j=0
    have hz : (firstVector (F:=F) (n:=n))∘Sum.inr=0 := by
      funext k
      simp [firstVector,Function.comp_apply]
    rw [hz,map_zero]
    rfl

end SymmetricSubgroupAsymptotics.CFSGTypeABlockEmbedding
