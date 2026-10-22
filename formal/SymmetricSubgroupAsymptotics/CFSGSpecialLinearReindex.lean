import SymmetricSubgroupAsymptotics.CFSGTypeAElementaryMatrices
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Matrix.Basis

/-! Simultaneous row/column reindexing as an actual special-linear
homomorphism, retaining elementary parameters and natural vector action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSpecialLinearReindex
open CFSGTypeAElementaryMatrices
variable {K I J : Type*} [Field K] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def reindexHom (e : I ≃ J) : Matrix.SpecialLinearGroup I K →* Matrix.SpecialLinearGroup J K where
  toFun A := ⟨Matrix.reindex e e A.val, by rw [Matrix.det_reindex_self]; exact A.property⟩
  map_one' := Subtype.ext ((Matrix.reindexAlgEquiv K K e).map_one)
  map_mul' A B := Subtype.ext ((Matrix.reindexAlgEquiv K K e).map_mul A.val B.val)

theorem reindexHom_val (e : I ≃ J) (A : Matrix.SpecialLinearGroup I K) :
    (reindexHom e A).val = A.val.submatrix e.symm e.symm := rfl

theorem reindexHom_elementary (e : I ≃ J) (i j : I) (hij : i ≠ j) (a : K) :
    reindexHom e (elementary hij a) = elementary (e.injective.ne hij) a := by
  apply Subtype.ext
  change (Matrix.transvection i j a).submatrix e.symm e.symm = Matrix.transvection (e i) (e j) a
  change (1 : Matrix I I K).submatrix e.symm e.symm +
    (Matrix.single i j a).submatrix e.symm e.symm = _
  rw [Matrix.submatrix_one_equiv, Matrix.submatrix_single_equiv]
  rfl

theorem reindexHom_mulVec (e : I ≃ J) (A : Matrix.SpecialLinearGroup I K) (v : J → K) :
    (reindexHom e A).val *ᵥ v = (A.val *ᵥ (v ∘ e)) ∘ e.symm := by
  rw [reindexHom_val, Matrix.submatrix_mulVec_equiv]
  rfl

end SymmetricSubgroupAsymptotics.CFSGSpecialLinearReindex
