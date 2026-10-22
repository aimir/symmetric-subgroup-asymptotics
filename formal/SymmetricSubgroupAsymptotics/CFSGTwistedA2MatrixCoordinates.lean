import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalCartan
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Eight integral matrix coordinates for the literal natural A2 model.
The same coordinate table works over every commutative coefficient ring,
including characteristics two and three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2MatrixCoordinates
open CFSGTwistedANaturalMatrices
variable (R : Type*) [CommRing R]

def matrixVectors : Fin 8 → Mat R 2 :=
  ![cartan R 2 0, cartan R 2 1, positive R 2 0, positive R 2 1,
    Matrix.single 0 2 1, negative R 2 0, negative R 2 1, Matrix.single 2 0 1]

def matrixCoordinates : Mat R 2 →ₗ[R] (Fin 8 → R) where
  toFun M := ![M 0 0, -M 2 2, M 0 1, M 1 2, M 0 2, M 1 0, M 2 1, M 2 0]
  map_add' M N := by
    funext i
    fin_cases i <;> simp [Matrix.add_apply, add_comm]
  map_smul' a M := by
    funext i
    fin_cases i <;> simp [Matrix.smul_apply]

def matrixCombination : (Fin 8 → R) →ₗ[R] Mat R 2 :=
  Fintype.linearCombination R (matrixVectors R)

set_option maxHeartbeats 600000 in
theorem coordinates_vector (j : Fin 8) :
    matrixCoordinates R (matrixVectors R j) = Pi.single j 1 := by
  funext i
  fin_cases j <;> fin_cases i <;>
    norm_num [matrixVectors, matrixCoordinates, cartan_eq, positive, negative,
      Matrix.single, Pi.single_apply] <;>
    (try simp only [Fin.ext_iff]) <;> norm_num [Matrix.single]

theorem coordinates_combination (a : Fin 8 → R) :
    matrixCoordinates R (matrixCombination R a) = a := by
  classical
  change matrixCoordinates R (∑ i, a i • matrixVectors R i) = a
  rw [map_sum]
  simp only [map_smul, coordinates_vector]
  funext j
  simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]

theorem matrixCombination_injective : Function.Injective (matrixCombination R) := by
  intro a b h
  have hh := congrArg (matrixCoordinates R) h
  simpa only [coordinates_combination] using hh

theorem map_matrixVectors {S : Type*} [CommRing S] (f : R →+* S) (j : Fin 8) :
    f.mapMatrix (matrixVectors R j) = matrixVectors S j := by
  fin_cases j
  · change f.mapMatrix (cartan R 2 0) = cartan S 2 0
    exact map_cartan R 2 f 0
  · change f.mapMatrix (cartan R 2 1) = cartan S 2 1
    exact map_cartan R 2 f 1
  · change f.mapMatrix (positive R 2 0) = positive S 2 0
    exact map_positive R 2 f 0
  · change f.mapMatrix (positive R 2 1) = positive S 2 1
    exact map_positive R 2 f 1
  · change (Matrix.single (0 : Fin 3) 2 (1 : R)).map f = Matrix.single 0 2 1
    simp only [Matrix.map_single, map_one]
  · change f.mapMatrix (negative R 2 0) = negative S 2 0
    exact map_negative R 2 f 0
  · change f.mapMatrix (negative R 2 1) = negative S 2 1
    exact map_negative R 2 f 1
  · change (Matrix.single (2 : Fin 3) 0 (1 : R)).map f = Matrix.single 2 0 1
    simp only [Matrix.map_single, map_one]

theorem coordinates_map {S : Type*} [CommRing S] (f : R →+* S) (M : Mat R 2) :
    matrixCoordinates S (f.mapMatrix M) = fun i => f (matrixCoordinates R M i) := by
  funext i
  fin_cases i <;> simp [matrixCoordinates]

end SymmetricSubgroupAsymptotics.CFSGTwistedA2MatrixCoordinates
