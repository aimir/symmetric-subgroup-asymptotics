import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalRationalFirstActionSpan
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIntegralDoubledCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSignedPathImages
import SymmetricSubgroupAsymptotics.FiniteIntegralRationalFamilyScaledRetraction

/-! Odd-characteristic faithfulness for the SAME original D integral
lattice. Actual rational spanning and a FULL integer doubled-coordinate
map give an integral retraction up to two. No Z-spanning or realization
faithfulness hypothesis occurs, and characteristic two is not asserted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalScaledRealization
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGOrthogonalDSerreMatrices
open CFSGOrthogonalDOriginalRootCandidates CFSGOrthogonalDOriginalIntegralAction
open CFSGOrthogonalDOriginalPositiveRootImages CFSGOrthogonalDSignedPathImages
variable (r : ℕ) (hr : 4 ≤ r)
local instance : DecidableEq (BasisIndex r):=Classical.decEq _

def integerMatrix : BasisIndex r→Mat ℤ r
  | .inl i=>cartan ℤ r i
  | .inr j=>CFSGOrthogonalDUniformRootCoordinates.matrix ℤ r j

theorem vector_image (j : BasisIndex r) :
    integralOrthogonalRepresentation r hr (vector r hr j)=integerMatrix r j := by
  rcases j with i | ⟨neg,ij | ij⟩
  · exact generator_image r hr (.H i)
  · cases neg
    · exact difference_image r hr ij
    · exact difference_negative_image r hr ij
  · cases neg
    · exact sum_image r hr ij
    · exact sum_negative_image r hr ij

theorem integerMatrix_cast (j : BasisIndex r) :
    (Int.castRingHom ℚ).mapMatrix (integerMatrix r j)=
      CFSGOrthogonalDUniformRationalFamily.matrix r j := by
  rcases j with i | ⟨neg,ij | ij⟩
  · exact map_cartan ℤ r (Int.castRingHom ℚ) i
  all_goals
    cases neg <;> ext x y <;>
      simp [integerMatrix,CFSGOrthogonalDUniformRationalFamily.matrix,
        CFSGOrthogonalDUniformRootCoordinates.matrix,
        CFSGOrthogonalDUniformRootMatrixArithmetic.difference,
        CFSGOrthogonalDUniformRootMatrixArithmetic.sumRoot,
        RingHom.mapMatrix,Matrix.map_apply,Matrix.transpose_apply,
        Matrix.sub_apply,Matrix.single_apply,and_comm]

theorem rational_vector_image (j : BasisIndex r) :
    rationalOrthogonalRepresentation r hr (vector r hr j).val=
      CFSGOrthogonalDUniformRationalFamily.matrix r j := by
  have h:=CFSGSerreSquareZeroMatrix.integralRepresentation_cast
    (realizationData r hr) (vector r hr j)
  change (Int.castRingHom ℚ).mapMatrix
    (integralOrthogonalRepresentation r hr (vector r hr j))=
      rationalOrthogonalRepresentation r hr (vector r hr j).val at h
  rw [vector_image,integerMatrix_cast] at h
  exact h.symm

def rationalCoordinates : RationalLie (CartanMatrix.D r)→ₗ[ℚ](BasisIndex r→ℚ) :=
  (2:ℚ) • (CFSGOrthogonalDUniformRationalFamily.coordinates r hr).comp
    (rationalOrthogonalRepresentation r hr).toLinearMap

theorem coordinates_vector (j : BasisIndex r) :
    rationalCoordinates r hr (vector r hr j).val=(2:ℚ) • Pi.single j 1 := by
  change (2:ℚ) • CFSGOrthogonalDUniformRationalFamily.coordinates r hr
    (rationalOrthogonalRepresentation r hr (vector r hr j).val)=_
  rw [rational_vector_image,CFSGOrthogonalDUniformRationalFamily.coordinates_matrix]

theorem coordinates_cast (x : Source r) :
    rationalCoordinates r hr x.val=fun j=>
      (CFSGOrthogonalDIntegralDoubledCoordinates.coordinates r hr
        (integralOrthogonalRepresentation r hr x) j:ℚ) := by
  funext j
  have h:=CFSGOrthogonalDIntegralDoubledCoordinates.cast_coordinates r hr
    (integralOrthogonalRepresentation r hr x) j
  have hcast:=CFSGSerreSquareZeroMatrix.integralRepresentation_cast (realizationData r hr) x
  change (Int.castRingHom ℚ).mapMatrix (integralOrthogonalRepresentation r hr x)=
    rationalOrthogonalRepresentation r hr x.val at hcast
  rw [hcast] at h
  exact h.symm

theorem retraction_comp :
    (FiniteIntegralFamilyScaledRetraction.retraction (vector r hr)
      (CFSGOrthogonalDIntegralDoubledCoordinates.coordinates r hr)).comp
        (integralOrthogonalRepresentation r hr)=(2:ℤ) • LinearMap.id :=
  FiniteIntegralRationalFamilyScaledRetraction.retraction_comp_of_rational_span
    (integralLattice (CartanMatrix.D r)) (integralOrthogonalRepresentation r hr)
    (vector r hr) (CFSGOrthogonalDIntegralDoubledCoordinates.coordinates r hr)
    (rationalCoordinates r hr) 2 (coordinates_vector r hr) (coordinates_cast r hr)
    (CFSGOrthogonalDOriginalRationalFirstActionSpan.span_eq_top r hr)

theorem baseChange_injective (K : Type*) [Field K] (h2 : (2:K)≠0) :
    Function.Injective ((integralOrthogonalRepresentation r hr).baseChange K) :=
  FiniteIntegralRationalFamilyScaledRetraction.baseChange_injective_of_rational_span
    (integralLattice (CartanMatrix.D r)) (integralOrthogonalRepresentation r hr)
    (vector r hr) (CFSGOrthogonalDIntegralDoubledCoordinates.coordinates r hr)
    (rationalCoordinates r hr) 2 (coordinates_vector r hr) (coordinates_cast r hr)
    (CFSGOrthogonalDOriginalRationalFirstActionSpan.span_eq_top r hr) K (by simpa using h2)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalScaledRealization
