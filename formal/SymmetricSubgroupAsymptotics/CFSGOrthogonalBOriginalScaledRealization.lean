import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalRationalSpan
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSignedPathImages
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBDoubledFamilyCoordinates
import SymmetricSubgroupAsymptotics.FiniteIntegralRationalFamilyScaledRetraction
import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixTensorEquiv

/-! Faithfulness of the SAME original B integral source in every field
where two is invertible. Whole rational source spanning and literal
integer doubled coordinates give a genuine scaled retraction. No source
simplicity, integral saturation, or model-recognition premise occurs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalScaledRealization
open CFSG.Models.Chevalley CFSGOrthogonalBSerreMatrices
open CFSGOrthogonalBOriginalRootCandidates CFSGOrthogonalBDoubledFamilyCoordinates
variable (r : ℕ)
local instance : DecidableEq (BasisIndex r) := Classical.decEq _

theorem rational_vector_image (j : BasisIndex r) :
    rationalOrthogonalRepresentation r (vector r j).val = familyMatrix ℚ r j := by
  rcases j with i | ⟨b, z⟩
  · exact rationalOrthogonalRepresentation_H r i
  · cases b
    · exact CFSGOrthogonalBOriginalPositivePrimitiveFamily.source_image r (.inr z)
    · exact CFSGOrthogonalBSignedPathImages.root_negative_image r z

def rationalCoordinates : RationalLie (CartanMatrix.B r).transpose →ₗ[ℚ]
    (BasisIndex r → ℚ) :=
  (doubled ℚ r).comp (rationalOrthogonalRepresentation r).toLinearMap

theorem coordinates_vector (j : BasisIndex r) :
    rationalCoordinates r (vector r j).val = (2 : ℚ) • Pi.single j 1 := by
  change doubled ℚ r (rationalOrthogonalRepresentation r (vector r j).val) = _
  rw [rational_vector_image, doubled_familyMatrix]

theorem coordinates_cast (x : Source r) :
    rationalCoordinates r x.val = fun j =>
      (doubled ℤ r (integralOrthogonalRepresentation r x) j : ℚ) := by
  change doubled ℚ r (rationalOrthogonalRepresentation r x.val) = _
  have h := CFSGSerreQuadraticMatrix.integralRepresentation_cast (realizationData r) x
  change CFSGSerreSquareZeroMatrix.integerCast (Index r)
    (integralOrthogonalRepresentation r x) = rationalOrthogonalRepresentation r x.val at h
  rw [← h]
  exact doubled_integerCast r _

theorem retraction_comp :
    (FiniteIntegralFamilyScaledRetraction.retraction (vector r) (doubled ℤ r)).comp
      (integralOrthogonalRepresentation r) = (2 : ℤ) • LinearMap.id :=
  FiniteIntegralRationalFamilyScaledRetraction.retraction_comp_of_rational_span
    (integralLattice (CartanMatrix.B r).transpose) (integralOrthogonalRepresentation r)
    (vector r) (doubled ℤ r) (rationalCoordinates r) 2
    (coordinates_vector r) (coordinates_cast r) (CFSGOrthogonalBOriginalRationalSpan.span_eq_top r)

theorem integral_baseChange_injective (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) :
    Function.Injective ((integralOrthogonalRepresentation r).baseChange K) :=
  FiniteIntegralRationalFamilyScaledRetraction.baseChange_injective_of_rational_span
    (integralLattice (CartanMatrix.B r).transpose) (integralOrthogonalRepresentation r)
    (vector r) (doubled ℤ r) (rationalCoordinates r) 2
    (coordinates_vector r) (coordinates_cast r) (CFSGOrthogonalBOriginalRationalSpan.span_eq_top r)
    K (by simpa only [Int.cast_ofNat] using h2)

theorem baseChange_injective (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) :
    Function.Injective (orthogonalBaseChange K r) := by
  exact (CFSGIntegerMatrixTensorEquiv.tensorMap_injective K (Index r)).comp
    (integral_baseChange_injective r K h2)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalScaledRealization
