import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveSerreStrings
import SymmetricSubgroupAsymptotics.CFSGGTwoSerreRepresentation
import Mathlib.Tactic.Abel

/-! One selected sparse matrix certificate for the ORIGINAL G2 rational
basis route. This proves the first non-simple vector's actual image; it
does not reflect image equality into the source before spanning and
coordinate independence have been proved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalBasisMatrixPilot
open CFSGGTwoOriginalPositiveSerreStrings CFSGGTwoSerreMatrices
open CFSG.Models.Chevalley
variable (R : Type*) [CommRing R]

def firstMatrix : Mat R :=
  Matrix.single (pos 0) (pos 2) 1 - Matrix.single (pos 1) (pos 3) 1 -
    Matrix.single (pos 1) (neg 3) 1 + Matrix.single (pos 3) (neg 1) 1 -
      Matrix.single (neg 2) (neg 0) 1 + Matrix.single (neg 3) (neg 1) 1

theorem first_bracket : ⁅positive R 0,positive R 1⁆=firstMatrix R := by
  rw [Ring.lie_def,positive_zero_explicit,positive_one_explicit]
  simp only [add_mul,sub_mul,mul_add,mul_sub]
  simp [pos,neg,Matrix.single_mul_single_same,Matrix.single_mul_single_of_ne,
    firstMatrix] <;> abel

theorem rationalRepresentation_first :
    rationalRepresentation (stringVector false 1)=firstMatrix ℚ := by
  rw [string_one,LieHom.map_lie]
  change ⁅rationalRepresentation (generator CartanMatrix.G₂ (.E 0)),
    rationalRepresentation (generator CartanMatrix.G₂ (.E 1))⁆=firstMatrix ℚ
  rw [rationalRepresentation_E,rationalRepresentation_E]
  exact first_bracket ℚ

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalBasisMatrixPilot
