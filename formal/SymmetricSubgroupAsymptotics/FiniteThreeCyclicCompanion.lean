import SymmetricSubgroupAsymptotics.LinearMapCyclicPowerBasis
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.Tactic.FinCases

/-! The actual degree-three cyclic basis gives an actual GL3 conjugator
to a companion matrix. All fields are allowed; no noncyclic classification
or finite-field selection argument occurs here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteThreeCyclicCompanion

open Module
open scoped Matrix
variable {K : Type*} [Field K]

/-- The final column records the image of the last cyclic basis vector. -/
def companion (c : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, c 0; 1, 0, c 1; 0, 1, c 2]

theorem toMatrix_eq_companion {V : Type*} [AddCommGroup V] [Module K V]
    (A : Module.End K V) (b : Basis (Fin 3) K V)
    (h01 : A (b 0) = b 1) (h12 : A (b 1) = b 2) :
    LinearMap.toMatrix b b A = companion (fun i => b.repr (A (b 2)) i) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, companion, h01, h12]

theorem exists_companion_basis {V : Type*} [AddCommGroup V] [Module K V]
    [Module.Finite K V] (A : Module.End K V) (hd : Module.finrank K V = 3)
    (hmin : (minpoly K A).natDegree = 3) :
    ∃ (b : Basis (Fin 3) K V) (c : Fin 3 → K),
      LinearMap.toMatrix b b A = companion c := by
  obtain ⟨v, b, hb⟩ := LinearMapCyclicPowerBasis.exists_basis_three A hd hmin
  have h01 : A (b 0) = b 1 := by
    rw [hb 0, hb 1]
    simp only [Fin.val_zero, pow_zero, Module.End.one_apply, Fin.val_one, pow_one]
  have h12 : A (b 1) = b 2 := by
    rw [hb 1, hb 2]
    change A (A v) = (A ^ 2) v
    rw [pow_two, Module.End.mul_apply]
  exact ⟨b, _, toMatrix_eq_companion A b h01 h12⟩

/-- The matrix whose columns are an actual basis, with its actual inverse. -/
def basisMatrix (b : Basis (Fin 3) K (Fin 3 → K)) :
    Matrix.GeneralLinearGroup (Fin 3) K where
  val := (Pi.basisFun K (Fin 3)).toMatrix b
  inv := b.toMatrix (Pi.basisFun K (Fin 3))
  val_inv := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  inv_val := Module.Basis.toMatrix_mul_toMatrix_flip _ _

theorem basisMatrix_conjugate (A : Matrix (Fin 3) (Fin 3) K)
    (b : Basis (Fin 3) K (Fin 3 → K)) :
    (↑((basisMatrix b)⁻¹) : Matrix (Fin 3) (Fin 3) K) * A *
      (basisMatrix b : Matrix (Fin 3) (Fin 3) K) =
        LinearMap.toMatrix b b (Matrix.toLin' A) := by
  change b.toMatrix (Pi.basisFun K (Fin 3)) * A *
    (Pi.basisFun K (Fin 3)).toMatrix b = _
  simpa only [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin'] using
    basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b
      (Pi.basisFun K (Fin 3)) b (Pi.basisFun K (Fin 3)) (Matrix.toLin' A)

theorem exists_companion_conjugator (A : Matrix (Fin 3) (Fin 3) K)
    (hmin : (minpoly K A).natDegree = 3) :
    ∃ (P : Matrix.GeneralLinearGroup (Fin 3) K) (c : Fin 3 → K),
      (↑(P⁻¹) : Matrix (Fin 3) (Fin 3) K) * A *
        (P : Matrix (Fin 3) (Fin 3) K) = companion c := by
  have hm : (minpoly K (Matrix.toLin' A)).natDegree = 3 := by
    simpa only [Matrix.minpoly_toLin'] using hmin
  obtain ⟨b, c, hc⟩ := exists_companion_basis (Matrix.toLin' A)
    (by simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]) hm
  exact ⟨basisMatrix b, c, (basisMatrix_conjugate A b).trans hc⟩

end SymmetricSubgroupAsymptotics.FiniteThreeCyclicCompanion
