import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Group.Units.Hom

/-! The literal diagonal units, with their original coordinate units as
parameters. This exposes every diagonal entry without a determinant or
finite-group order formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGDiagonalMatrixUnits
variable (I K : Type*) [Fintype I] [DecidableEq I] [CommRing K]

def diagonalHom : (I→Kˣ)→*(Matrix I I K)ˣ where
  toFun := fun d=>
    { val:=Matrix.diagonal (fun i=>(d i:K))
      inv:=Matrix.diagonal (fun i=>((d i)⁻¹:Kˣ))
      val_inv:=by
        rw [Matrix.diagonal_mul_diagonal]
        ext i j
        simp [Matrix.diagonal_apply,Matrix.one_apply]
      inv_val:=by
        rw [Matrix.diagonal_mul_diagonal]
        ext i j
        simp [Matrix.diagonal_apply,Matrix.one_apply] }
  map_one' := by
    apply Units.ext
    ext i j
    simp [Matrix.diagonal_apply,Matrix.one_apply]
  map_mul' := by
    intro d e
    apply Units.ext
    change Matrix.diagonal (fun i=>((d*e) i:K))=
      Matrix.diagonal (fun i=>(d i:K))*Matrix.diagonal (fun i=>(e i:K))
    rw [Matrix.diagonal_mul_diagonal]
    rfl

theorem diagonalHom_val (d : I→Kˣ) :
    (diagonalHom I K d : Matrix I I K)=Matrix.diagonal (fun i=>(d i:K)) := rfl

theorem diagonalHom_injective : Function.Injective (diagonalHom I K) := by
  intro d e h
  funext i
  apply Units.ext
  have hi := congrArg (fun u : (Matrix I I K)ˣ=>(u : Matrix I I K) i i) h
  simpa only [diagonalHom_val,Matrix.diagonal_apply_eq] using hi

end SymmetricSubgroupAsymptotics.CFSGDiagonalMatrixUnits
