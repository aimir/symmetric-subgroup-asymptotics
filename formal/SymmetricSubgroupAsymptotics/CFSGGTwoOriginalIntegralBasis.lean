import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalRationalBasis
import SymmetricSubgroupAsymptotics.CFSGGTwoIntegralRealization
import Mathlib.Algebra.Module.NatInt

/-! An exact basis of the ORIGINAL least divided-power-stable G2 lattice.
Every lattice element has integral matrix entries under the established
integral representation. Unit-pivot extraction therefore recovers its
integral coefficients in the original fourteen-vector family. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalIntegralBasis
open CFSG.Models.Chevalley CFSGGTwoSerreMatrices
open CFSGGTwoOriginalFourteenFamily CFSGGTwoOriginalMatrixCoordinates
open CFSGGTwoOriginalRationalBasis CFSGSerreQuadraticMatrix
open CFSGSerreSquareZeroMatrix
local notation "A" => CartanMatrix.G₂

theorem integralRepresentation_vectors (i : BasisIndex) :
    integralRepresentation realizationData (integralVectors i)=matrixVectors ℤ i := by
  apply integerCast_injective CFSGGTwoSerreMatrices.Index
  rw [CFSGSerreQuadraticMatrix.integralRepresentation_cast]
  change rationalRepresentation (vectors i)=(Int.castRingHom ℚ).mapMatrix (matrixVectors ℤ i)
  rw [rationalRepresentation_vectors,map_matrixVectors]

def integralCoordinates : integralLattice A →ₗ[ℤ] (BasisIndex → ℤ) :=
  (matrixCoordinates ℤ).comp (integralRepresentation realizationData)

def integralCombination : (BasisIndex → ℤ) →ₗ[ℤ] integralLattice A :=
  Fintype.linearCombination ℤ integralVectors

theorem integralCoordinates_vectors (i : BasisIndex) :
    integralCoordinates (integralVectors i)=Pi.single i 1 := by
  change matrixCoordinates ℤ (integralRepresentation realizationData (integralVectors i))=_
  rw [integralRepresentation_vectors,coordinates_vector]

theorem integralCoordinates_combination (a : BasisIndex → ℤ) :
    integralCoordinates (integralCombination a)=a := by
  classical
  change integralCoordinates (∑ i,a i • integralVectors i)=a
  rw [map_sum]
  simp only [map_smul,integralCoordinates_vectors]
  funext j
  simp [Finset.sum_apply,Pi.single_apply]

theorem integralCombination_val (a : BasisIndex → ℤ) :
    (integralCombination a).val=rationalCombination (fun i => (a i : ℚ)) := by
  change (integralLattice A).subtype (∑ i,a i • integralVectors i)=
    ∑ i,(a i : ℚ) • vectors i
  simp only [map_sum,map_smul,integralVectors,Submodule.subtype_apply,
    Int.cast_smul_eq_zsmul]

theorem integralCoordinates_cast (x : integralLattice A) :
    (fun i => (integralCoordinates x i : ℚ))=rationalCoordinates x.val := by
  have h := coordinates_map ℤ (Int.castRingHom ℚ) (integralRepresentation realizationData x)
  change matrixCoordinates ℚ (integerCast CFSGGTwoSerreMatrices.Index
    (integralRepresentation realizationData x))=_ at h
  rw [CFSGSerreQuadraticMatrix.integralRepresentation_cast] at h
  exact h.symm

theorem integralCombination_coordinates (x : integralLattice A) :
    integralCombination (integralCoordinates x)=x := by
  apply Subtype.ext
  rw [integralCombination_val,integralCoordinates_cast,combination_coordinates]

def integralBasisEquiv : integralLattice A ≃ₗ[ℤ] (BasisIndex → ℤ) where
  __ := integralCoordinates
  invFun := integralCombination
  left_inv := integralCombination_coordinates
  right_inv := integralCoordinates_combination

theorem integralCombination_surjective : Function.Surjective integralCombination :=
  fun x => ⟨integralCoordinates x,integralCombination_coordinates x⟩

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalIntegralBasis
