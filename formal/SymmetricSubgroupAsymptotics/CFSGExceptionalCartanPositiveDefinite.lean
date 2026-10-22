import Mathlib.Data.Matrix.Cartan
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Actual positive definiteness for the pinned E₆/E₇/E₈ Cartan tables.
A single explicit rational Gram factor handles all three; no finite-type
classification or exceptional root-system constructor is assumed. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalCartanPositiveDefinite

 def rootRows : Matrix (Fin 8) (Fin 8) ℚ :=
  !![1/2,-1/2,-1/2,-1/2,-1/2,-1/2,-1/2,1/2;
     1,1,0,0,0,0,0,0;
     -1,1,0,0,0,0,0,0;
     0,-1,1,0,0,0,0,0;
     0,0,-1,1,0,0,0,0;
     0,0,0,-1,1,0,0,0;
     0,0,0,0,-1,1,0,0;
     0,0,0,0,0,-1,1,0]
 def rootColumns : Matrix (Fin 8) (Fin 8) ℚ := rootRows.transpose

 theorem root_gram : rootColumns.conjTranspose*rootColumns=
    (Int.castRingHom ℚ).mapMatrix CartanMatrix.E₈ := by
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rootColumns,rootRows,CartanMatrix.E₈,Matrix.mul_apply,Fin.sum_univ_succ]

 theorem rootColumns_kernel_zero (x : Fin 8→ℚ) (hx : rootColumns*ᵥx=0) : x=0 := by
  have h0 := congrFun hx (0:Fin 8)
  have h1 := congrFun hx (1:Fin 8)
  have h2 := congrFun hx (2:Fin 8)
  have h3 := congrFun hx (3:Fin 8)
  have h4 := congrFun hx (4:Fin 8)
  have h5 := congrFun hx (5:Fin 8)
  have h6 := congrFun hx (6:Fin 8)
  have h7 := congrFun hx (7:Fin 8)
  norm_num [rootColumns,rootRows,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6 h7
  iterate 8
    try dsimp [Matrix.vecCons,Fin.succ] at h0 h1 h2 h3 h4 h5 h6 h7
    norm_num at h0 h1 h2 h3 h4 h5 h6 h7
  have hx0 : x (0:Fin 8)=0 := by linarith
  have hx1 : x (1:Fin 8)=0 := by linarith
  have hx2 : x (2:Fin 8)=0 := by linarith
  have hx3 : x (3:Fin 8)=0 := by linarith
  have hx4 : x (4:Fin 8)=0 := by linarith
  have hx5 : x (5:Fin 8)=0 := by linarith
  have hx6 : x (6:Fin 8)=0 := by linarith
  have hx7 : x (7:Fin 8)=0 := by linarith
  ext i
  fin_cases i <;> first | exact hx0 | exact hx1 | exact hx2 | exact hx3 | exact hx4 | exact hx5 | exact hx6 | exact hx7

 theorem rootColumns_injective : Function.Injective rootColumns.mulVec := by
  intro x y h
  apply sub_eq_zero.mp
  apply rootColumns_kernel_zero
  rw [Matrix.mulVec_sub,h,sub_self]

 theorem E8_positive_definite : ((Int.castRingHom ℚ).mapMatrix CartanMatrix.E₈).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [←root_gram]
    exact Matrix.isHermitian_conjTranspose_mul_self rootColumns
  · intro x hx
    have hy : rootColumns*ᵥx≠0 := by
      intro h
      apply hx
      apply rootColumns_injective
      simpa only [Matrix.mulVec_zero] using h
    have hnonneg : 0≤(rootColumns*ᵥx) ⬝ᵥ(rootColumns*ᵥx) :=
      Finset.sum_nonneg (fun i _=>mul_self_nonneg ((rootColumns*ᵥx) i))
    have hne : (rootColumns*ᵥx) ⬝ᵥ(rootColumns*ᵥx)≠0 := by
      intro h
      exact hy (dotProduct_self_eq_zero.mp h)
    have hpos : 0<(rootColumns*ᵥx) ⬝ᵥ(rootColumns*ᵥx) :=
      lt_of_le_of_ne hnonneg (Ne.symm hne)
    have he : star x ⬝ᵥ(((Int.castRingHom ℚ).mapMatrix CartanMatrix.E₈)*ᵥx)=
        (rootColumns*ᵥx) ⬝ᵥ(rootColumns*ᵥx) := by
      rw [←root_gram,Matrix.conjTranspose_eq_transpose_of_trivial,
        ←Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]
      simp only [star_trivial]
    rw [he]
    exact hpos

 private def firstSeven (i : Fin 7) : Fin 8 := ⟨i.val,by omega⟩
 private def firstSix (i : Fin 6) : Fin 8 := ⟨i.val,by omega⟩

 private theorem firstSeven_injective : Function.Injective firstSeven := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 8=>k.val) h)
 private theorem firstSix_injective : Function.Injective firstSix := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 8=>k.val) h)

 theorem E7_is_principal : (Int.castRingHom ℚ).mapMatrix CartanMatrix.E₇=
    ((Int.castRingHom ℚ).mapMatrix CartanMatrix.E₈).submatrix firstSeven firstSeven := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [firstSeven,CartanMatrix.E₇,CartanMatrix.E₈]

 theorem E6_is_principal : (Int.castRingHom ℚ).mapMatrix CartanMatrix.E₆=
    ((Int.castRingHom ℚ).mapMatrix CartanMatrix.E₈).submatrix firstSix firstSix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [firstSix,CartanMatrix.E₆,CartanMatrix.E₈]

 theorem E7_positive_definite : ((Int.castRingHom ℚ).mapMatrix CartanMatrix.E₇).PosDef := by
  rw [E7_is_principal]
  exact E8_positive_definite.submatrix firstSeven_injective

 theorem E6_positive_definite : ((Int.castRingHom ℚ).mapMatrix CartanMatrix.E₆).PosDef := by
  rw [E6_is_principal]
  exact E8_positive_definite.submatrix firstSix_injective

end SymmetricSubgroupAsymptotics.CFSGExceptionalCartanPositiveDefinite
