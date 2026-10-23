import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalMatrixCoordinates

/-! An actual basis of the ORIGINAL rational G2 Serre quotient.
Spanning comes from generator invariance in that quotient; independence
comes from integral unit-pivot coordinates on its actual matrix image.
No simplicity or faithful-realization hypothesis occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalRationalBasis
open CFSGGTwoOriginalFourteenFamily CFSGGTwoOriginalPositiveBracketTable
open CFSGGTwoOriginalPositiveSerreStrings CFSGGTwoSerreMatrices
open CFSGGTwoOriginalBasisMatrixPilot CFSGGTwoOriginalBasisMatrices
open CFSGGTwoOriginalMatrixCoordinates CFSG.Models.Chevalley
local notation "L" => RationalLie CartanMatrix.G₂

theorem rationalRepresentation_vectors (i : BasisIndex) :
    rationalRepresentation (vectors i)=matrixVectors ℚ i := by
  cases i with
  | inl z =>
    obtain ⟨b,j⟩ := z
    cases b
    · fin_cases j
      · change rationalRepresentation (shortVector false)=positive ℚ 0
        simp only [shortVector,rootVector,Bool.false_eq_true,if_false,rationalRepresentation_E]
      · change rationalRepresentation (longVector false)=positive ℚ 1
        simp only [longVector,rootVector,Bool.false_eq_true,if_false,rationalRepresentation_E]
      · exact rationalRepresentation_first
      · exact rationalRepresentation_second
      · exact rationalRepresentation_third
      · exact rationalRepresentation_highest
    · fin_cases j
      · change rationalRepresentation (shortVector true)=negative ℚ 0
        simp only [shortVector,rootVector,if_true,rationalRepresentation_F]
      · change rationalRepresentation (longVector true)=negative ℚ 1
        simp only [longVector,rootVector,if_true,rationalRepresentation_F]
      · exact rationalRepresentation_negative_first
      · exact rationalRepresentation_negative_second
      · exact rationalRepresentation_negative_third
      · exact rationalRepresentation_negative_highest
  | inr j => exact rationalRepresentation_H j

def rationalCoordinates : L →ₗ[ℚ] (BasisIndex → ℚ) :=
  (matrixCoordinates ℚ).comp rationalRepresentation.toLinearMap

theorem rationalRepresentation_combination (a : BasisIndex → ℚ) :
    rationalRepresentation (rationalCombination a)=matrixCombination ℚ a := by
  change rationalRepresentation (∑ i,a i • vectors i)=∑ i,a i • matrixVectors ℚ i
  simp only [map_sum,map_smul,rationalRepresentation_vectors]

theorem coordinates_combination (a : BasisIndex → ℚ) :
    rationalCoordinates (rationalCombination a)=a := by
  change matrixCoordinates ℚ (rationalRepresentation (rationalCombination a))=a
  rw [rationalRepresentation_combination,CFSGGTwoOriginalMatrixCoordinates.coordinates_combination]

theorem combination_coordinates (x : L) :
    rationalCombination (rationalCoordinates x)=x := by
  obtain ⟨a,rfl⟩ := rationalCombination_surjective x
  rw [coordinates_combination]

def rationalBasisEquiv : L ≃ₗ[ℚ] (BasisIndex → ℚ) where
  __ := rationalCoordinates
  invFun := rationalCombination
  left_inv := combination_coordinates
  right_inv := coordinates_combination

theorem rationalRepresentation_injective : Function.Injective rationalRepresentation := by
  intro x y h
  apply rationalBasisEquiv.injective
  exact congrArg (matrixCoordinates ℚ) h

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalRationalBasis
