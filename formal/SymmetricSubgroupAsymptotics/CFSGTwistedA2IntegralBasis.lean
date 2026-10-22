import SymmetricSubgroupAsymptotics.CFSGTwistedA2RationalBasis
import Mathlib.Algebra.Module.NatInt

/-! An exact basis for the ORIGINAL divided-power-stable A2 lattice.
Integrality follows from the checked integral matrix descent, not from a
claim that rational injectivity survives reduction modulo a prime. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalRelations
open CFSG.Models.Chevalley CFSGSerreDiagram
open CFSGTwistedANaturalMatrices CFSGTwistedA2MatrixCoordinates
open CFSGSerreSquareZeroMatrix

theorem P_mem_lattice : P ∈ integralLattice A := by
  have h := dividedPower_mem A false 0 1 (E 1)
    (generator_mem_integralLattice A (.E 1))
  simpa only [dividedPower, Nat.factorial_one, Nat.cast_one, inv_one,
    one_smul, pow_one, LinearMap.restrictScalars_apply, LieAlgebra.ad_apply,
    rootVector, Bool.false_eq_true, if_false, E, P] using h

theorem N_mem_lattice : N ∈ integralLattice A := by
  have h := dividedPower_mem A true 1 1 (F 0)
    (generator_mem_integralLattice A (.F 0))
  simpa only [dividedPower, Nat.factorial_one, Nat.cast_one, inv_one,
    one_smul, pow_one, LinearMap.restrictScalars_apply, LieAlgebra.ad_apply,
    rootVector, if_true, F, N] using h

theorem vectors_mem_lattice (i : Fin 8) : vectors i ∈ integralLattice A := by
  fin_cases i
  · exact generator_mem_integralLattice A (.H 0)
  · exact generator_mem_integralLattice A (.H 1)
  · exact generator_mem_integralLattice A (.E 0)
  · exact generator_mem_integralLattice A (.E 1)
  · exact P_mem_lattice
  · exact generator_mem_integralLattice A (.F 0)
  · exact generator_mem_integralLattice A (.F 1)
  · exact N_mem_lattice

def integralVectors (i : Fin 8) : integralLattice A := ⟨vectors i, vectors_mem_lattice i⟩

theorem integralRepresentation_vectors (i : Fin 8) :
    integralRepresentation (realizationData 2) (integralVectors i) = matrixVectors ℤ i := by
  apply integerCast_injective (Fin 3)
  rw [integralRepresentation_cast]
  change rationalNatural 2 (vectors i) = (Int.castRingHom ℚ).mapMatrix (matrixVectors ℤ i)
  rw [rationalNatural_vectors, map_matrixVectors]

def integralCoordinates : integralLattice A →ₗ[ℤ] (Fin 8 → ℤ) :=
  (matrixCoordinates ℤ).comp (integralRepresentation (realizationData 2))

def integralCombination : (Fin 8 → ℤ) →ₗ[ℤ] integralLattice A :=
  Fintype.linearCombination ℤ integralVectors

theorem integralCoordinates_vectors (i : Fin 8) :
    integralCoordinates (integralVectors i) = Pi.single i 1 := by
  change matrixCoordinates ℤ (integralRepresentation (realizationData 2) (integralVectors i)) = _
  rw [integralRepresentation_vectors, coordinates_vector]

theorem integralCoordinates_combination (a : Fin 8 → ℤ) :
    integralCoordinates (integralCombination a) = a := by
  classical
  change integralCoordinates (∑ i, a i • integralVectors i) = a
  rw [map_sum]
  simp only [map_smul, integralCoordinates_vectors]
  funext j
  simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]

theorem integralCombination_val (a : Fin 8 → ℤ) :
    (integralCombination a).val = rationalCombination (fun i => (a i : ℚ)) := by
  change (integralLattice A).subtype (∑ i, a i • integralVectors i) =
    ∑ i, (a i : ℚ) • vectors i
  simp only [map_sum, map_smul, integralVectors, Submodule.subtype_apply,
    Int.cast_smul_eq_zsmul]

theorem integralCoordinates_cast (x : integralLattice A) :
    (fun i => (integralCoordinates x i : ℚ)) = rationalCoordinates x.val := by
  have h := coordinates_map ℤ (Int.castRingHom ℚ)
    (integralRepresentation (realizationData 2) x)
  change matrixCoordinates ℚ (integerCast (Fin 3)
    (integralRepresentation (realizationData 2) x)) = _ at h
  rw [integralRepresentation_cast] at h
  exact h.symm

theorem integralCombination_coordinates (x : integralLattice A) :
    integralCombination (integralCoordinates x) = x := by
  apply Subtype.ext
  rw [integralCombination_val, integralCoordinates_cast, combination_coordinates]

def integralBasisEquiv : integralLattice A ≃ₗ[ℤ] (Fin 8 → ℤ) where
  __ := integralCoordinates
  invFun := integralCombination
  left_inv := integralCombination_coordinates
  right_inv := integralCoordinates_combination

theorem integralCombination_surjective : Function.Surjective integralCombination :=
  fun x => ⟨integralCoordinates x, integralCombination_coordinates x⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalRelations
