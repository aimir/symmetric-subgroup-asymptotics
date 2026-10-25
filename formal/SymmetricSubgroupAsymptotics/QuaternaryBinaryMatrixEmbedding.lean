import SymmetricSubgroupAsymptotics.QuaternaryPauliMatrices
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.FinCases

/-! Faithful scalar restriction in the displayed F4 basis (1,omega).
Multiplication by a+b*omega is the binary matrix [[a,b],[b,a+b]].
The SAME entry embedding extends to matrices in every finite dimension.
The trace-Hermitian Gram is literally the standard hyperbolic binary
pairing; no classical-group or form-recognition statement is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.QuaternaryBinaryMatrixEmbedding
open BinaryQuadraticField
abbrev K := Scalar
abbrev B := ZMod 2

def scalarMatrix (z : K) : Matrix (Fin 2) (Fin 2) B :=
  !![z.re,z.im;z.im,z.re+z.im]

private theorem scalar_add : ∀ x y : K, scalarMatrix (x+y)=scalarMatrix x+scalarMatrix y := by
  decide +kernel
private theorem scalar_mul : ∀ x y : K, scalarMatrix (x*y)=scalarMatrix x*scalarMatrix y := by
  decide +kernel

def scalarHom : K →+* Matrix (Fin 2) (Fin 2) B where
  toFun := scalarMatrix
  map_zero' := by decide +kernel
  map_one' := by decide +kernel
  map_add' := scalar_add
  map_mul' := scalar_mul

theorem scalarHom_injective : Function.Injective scalarHom := by
  intro z w he
  have hre := congrFun (congrFun he 0) 0
  have him := congrFun (congrFun he 0) 1
  change z.re=w.re at hre
  change z.im=w.im at him
  exact QuadraticAlgebra.ext hre him

/-- Since Tr(z)=z.im, this is the literal trace-Hermitian Gram formula. -/
theorem trace_hermitian_gram : ∀ z w : K,
    (z^2*w).im=z.re*w.im+z.im*w.re := by decide +kernel

def splitIndex (I : Type*) : I ⊕ I ≃ I × Fin 2 where
  toFun := Sum.elim (fun i => (i,0)) (fun i => (i,1))
  invFun p := if p.2=0 then Sum.inl p.1 else Sum.inr p.1
  left_inv x := by cases x <;> rfl
  right_inv p := by rcases p with ⟨i,j⟩; fin_cases j <;> rfl

variable (I : Type*) [Fintype I] [DecidableEq I]

def matrixHom : Matrix I I K →+* Matrix (I × Fin 2) (I × Fin 2) B :=
  (Matrix.compRingEquiv I (Fin 2) B).toRingHom.comp
    (scalarHom.mapMatrix : Matrix I I K →+* Matrix I I (Matrix (Fin 2) (Fin 2) B))

def splitMatrixHom : Matrix I I K →+* Matrix (I ⊕ I) (I ⊕ I) B :=
  (Matrix.reindexAlgEquiv B B (splitIndex I).symm).toRingHom.comp (matrixHom I)

theorem matrixHom_injective : Function.Injective (matrixHom I) := by
  intro A C he
  have hh : A.map scalarHom=C.map scalarHom :=
    (Matrix.compRingEquiv I (Fin 2) B).injective he
  funext i j
  exact scalarHom_injective (congrFun (congrFun hh i) j)

theorem splitMatrixHom_injective : Function.Injective (splitMatrixHom I) := by
  intro A C he
  exact matrixHom_injective I ((Matrix.reindexAlgEquiv B B (splitIndex I).symm).injective he)

theorem split_matrix_entries (A : Matrix I I K) (i j : I) :
    splitMatrixHom I A (Sum.inl i) (Sum.inl j)=(A i j).re ∧
    splitMatrixHom I A (Sum.inl i) (Sum.inr j)=(A i j).im ∧
    splitMatrixHom I A (Sum.inr i) (Sum.inl j)=(A i j).im ∧
    splitMatrixHom I A (Sum.inr i) (Sum.inr j)=(A i j).re+(A i j).im := by
  exact ⟨rfl,rfl,rfl,rfl⟩

def unitHom : (Matrix I I K)ˣ →* (Matrix (I ⊕ I) (I ⊕ I) B)ˣ :=
  Units.map (splitMatrixHom I).toMonoidHom

theorem unitHom_injective : Function.Injective (unitHom I) := by
  intro A C he
  apply Units.ext
  exact splitMatrixHom_injective I (congrArg Units.val he)

theorem unitHom_val (A : (Matrix I I K)ˣ) :
    (unitHom I A).val=splitMatrixHom I A.val := rfl

end SymmetricSubgroupAsymptotics.QuaternaryBinaryMatrixEmbedding
