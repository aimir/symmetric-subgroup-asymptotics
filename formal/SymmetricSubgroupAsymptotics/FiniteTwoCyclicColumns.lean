import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Every nonscalar two-by-two matrix has a cyclic vector, in every
field. The columns (v,Av) satisfy the literal trace/determinant companion
identity, proved directly with no characteristic restriction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.FiniteTwoCyclicColumns
variable {K : Type*} [Field K]

def cyclicColumns (A : Matrix (Fin 2) (Fin 2) K) (v : Fin 2 → K) :
    Matrix (Fin 2) (Fin 2) K := !![v 0, (A *ᵥ v) 0; v 1, (A *ᵥ v) 1]

def companion (t d : K) : Matrix (Fin 2) (Fin 2) K := !![0, -d; 1, t]

theorem companion_det (t d : K) : (companion t d).det=d := by
  simp [companion, Matrix.det_fin_two]

theorem exists_cyclic_columns (A : Matrix (Fin 2) (Fin 2) K)
    (hA : A ∉ Set.range (Matrix.scalar (Fin 2))) :
    ∃ v : Fin 2 → K, (cyclicColumns A v).det ≠ 0 := by
  by_cases hc : A 1 0≠0
  · refine ⟨![1,0], ?_⟩
    simpa [cyclicColumns, Matrix.det_fin_two, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] using hc
  · by_cases hb : A 0 1≠0
    · refine ⟨![0,1], ?_⟩
      simpa [cyclicColumns, Matrix.det_fin_two, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two] using neg_ne_zero.mpr hb
    · have hc0 : A 1 0=0 := not_ne_iff.mp hc
      have hb0 : A 0 1=0 := not_ne_iff.mp hb
      have hd : A 1 1≠A 0 0 := by
        intro hd
        apply hA
        refine ⟨A 0 0, ?_⟩
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.scalar_apply, Matrix.diagonal_apply, hc0, hb0, hd]
      refine ⟨![1,1], ?_⟩
      simpa [cyclicColumns, Matrix.det_fin_two, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, hc0, hb0] using sub_ne_zero.mpr hd

theorem mul_cyclic_columns (A : Matrix (Fin 2) (Fin 2) K) (v : Fin 2 → K) :
    A * cyclicColumns A v = cyclicColumns A v * companion A.trace A.det := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyclicColumns, companion, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

end SymmetricSubgroupAsymptotics.FiniteTwoCyclicColumns
