import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPrimitiveFamily
import SymmetricSubgroupAsymptotics.PrimitiveIntegralFamilyRationalSpan

/-! Integral detection inside the rational span of the ACTUAL original
primitive family. Exact integer coordinate entries exclude denominators;
this does not assume the family spans the original source. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalIntegralSpanDetection
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSymplecticSerreMatrices
open CFSGSymplecticOriginalRootCandidates CFSGSymplecticOriginalPrimitiveFamily
open CFSGSymplecticUniformRootCoordinates
variable (r : ℕ)
local instance : DecidableEq (BasisIndex r) := Classical.decEq _

def rationalCoordinates : RationalLie (CartanMatrix.C r).transpose→ₗ[ℚ](BasisIndex r→ℚ) :=
  (coordinates ℚ r).comp (rationalSymplecticRepresentation r).toLinearMap

theorem rationalCoordinates_cast (x : Source r) :
    rationalCoordinates r x.val=fun j=>(matrixCoordinates r (integralSymplecticRepresentation r x) j:ℚ) := by
  change coordinates ℚ r (rationalSymplecticRepresentation r x.val)=_
  rw [←integralSymplecticRepresentation_cast r x]
  rfl

theorem rationalCoordinates_primitive (j : BasisIndex r) :
    rationalCoordinates r (primitiveVector r j).val=Pi.single j 1 := by
  rw [rationalCoordinates_cast,primitive_coordinates]
  funext k
  simp [Pi.single_apply]

theorem integral_mem_of_rational_mem (x : Source r)
    (hx : x.val∈Submodule.span ℚ (Set.range (fun j=>(primitiveVector r j).val))) :
    x∈Submodule.span ℤ (Set.range (primitiveVector r)) :=
  PrimitiveIntegralFamilyRationalSpan.integral_mem_of_rational_mem
    (integralLattice (CartanMatrix.C r).transpose) (primitiveVector r)
    (rationalCoordinates r) (rationalCoordinates_primitive r) x
    (matrixCoordinates r (integralSymplecticRepresentation r x))
    (rationalCoordinates_cast r x) hx

end SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalIntegralSpanDetection
