import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootGenerators
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Ten explicit positive norm-two vectors in an actual A4 principal
chain, orthogonal to any coordinate orthogonal to that chain. This is a
small lattice witness, independent of a root census or representation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalA4RootPilot
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinatePositiveRootGenerators
variable {n : Type} [Fintype n] [DecidableEq n]

def chainGram : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2,-1,0,0;-1,2,-1,0;0,-1,2,-1;0,0,-1,2]

def coefficients : Fin 10→Fin 4→ℤ :=
  ![![1,0,0,0],![0,1,0,0],![0,0,1,0],![0,0,0,1],
    ![1,1,0,0],![0,1,1,0],![0,0,1,1],
    ![1,1,1,0],![0,1,1,1],![1,1,1,1]]

theorem coefficients_injective : Function.Injective coefficients := by decide

theorem coefficients_nonnegative (t : Fin 10) (i : Fin 4) :
    0≤coefficients t i := by
  fin_cases t <;> fin_cases i <;> norm_num [coefficients]

def vector (e : Fin 4↪n) (t : Fin 10) : n→ℤ :=
  ∑i : Fin 4,coefficients t i • (Pi.single (e i) (1:ℤ) : n→ℤ)

theorem vector_restrict (e : Fin 4↪n) (t : Fin 10) (j : Fin 4) :
    vector e t (e j)=coefficients t j := by
  classical
  simp [vector,Finset.sum_apply,Pi.smul_apply,Pi.single_apply,e.injective.eq_iff]

theorem vector_injective (e : Fin 4↪n) : Function.Injective (vector e) := by
  intro t s he
  apply coefficients_injective
  funext j
  have hh := congrFun he (e j)
  simpa only [vector_restrict] using hh

theorem vector_nonnegative (e : Fin 4↪n) (t : Fin 10) (j : n) :
    0≤vector e t j := by
  classical
  change 0≤(∑i : Fin 4,coefficients t i • (Pi.single (e i) (1:ℤ) : n→ℤ)) j
  rw [Finset.sum_apply]
  apply Finset.sum_nonneg
  intro i _
  simp only [Pi.smul_apply,smul_eq_mul,Pi.single_apply]
  split_ifs
  · simpa only [mul_one] using coefficients_nonnegative t i
  · simp

theorem vector_norm (A : Matrix n n ℤ) (e : Fin 4↪n)
    (he : ∀i j,A (e i) (e j)=chainGram i j) (t : Fin 10) :
    integerPairing A (vector e t) (vector e t)=2 := by
  simp only [vector,map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply]
  simp only [integerPairing,Matrix.toBilin'_single,smul_eq_mul,he]
  fin_cases t <;> norm_num [coefficients,chainGram,Fin.sum_univ_succ]

theorem vector_orthogonal (A : Matrix n n ℤ) (e : Fin 4↪n) (j : n)
    (he : ∀i,A (e i) j=0) (t : Fin 10) :
    integerPairing A (vector e t) (Pi.single j (1:ℤ) : n→ℤ)=0 := by
  simp only [vector,map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply]
  simp only [integerPairing,Matrix.toBilin'_single,smul_eq_mul,he,mul_zero,Finset.sum_const_zero]

def positiveRoots (A : Matrix n n ℤ) (e : Fin 4↪n)
    (he : ∀i j,A (e i) (e j)=chainGram i j) (t : Fin 10) :
    {k : Roots A // ∀i,0≤k.val i} :=
  ⟨⟨vector e t,vector_norm A e he t⟩,vector_nonnegative e t⟩

theorem positiveRoots_injective (A : Matrix n n ℤ) (e : Fin 4↪n)
    (he : ∀i j,A (e i) (e j)=chainGram i j) : Function.Injective (positiveRoots A e he) := by
  intro t s h
  apply vector_injective e
  exact congrArg (fun k : {k : Roots A // ∀i,0≤k.val i}=>k.val.val) h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalA4RootPilot
