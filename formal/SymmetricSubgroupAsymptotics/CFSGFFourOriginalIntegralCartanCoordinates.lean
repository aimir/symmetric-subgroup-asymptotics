import SymmetricSubgroupAsymptotics.CFSGFFourOriginalIntegralSimpleCoordinates
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalCartanCoordinateOrthogonality
import SymmetricSubgroupAsymptotics.CFSGFFourRelativeScalarIndex

/-! Four integral Cartan unit coordinates. The raw functionals are the
simple unit entries after ad(integerE_i); the existing integral inverse
of the F4 Cartan transpose turns their -A entries into Kronecker values.
All root crosszeros are exact integer statements before base change. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalIntegralCartanCoordinates
open CFSG.Models.Chevalley CFSGSerreQuadraticMatrix CFSGFFourSerreMatrices
open CFSGFFourOriginalFiftyTwoFamily CFSGFFourOriginalIntegralSimpleCoordinates
open CFSGFFourOriginalSimpleCoordinateWeights CFSGFFourOriginalCartanCoordinateOrthogonality
open CFSGFFourRelativeScalarIndex CFSGNormTwoRootPairing
local instance : DecidableEq (Roots CartanMatrix.E₆):=Classical.decEq _
local notation "A" => CartanMatrix.F₄

def integerCartanRawCoordinate (i:Fin 4) : IntMat→ₗ[ℤ]ℤ :=
  (integerSimpleCoordinate i).comp (LieAlgebra.ad ℤ IntMat (integerE i))

theorem raw_coordinate_cast (i:Fin 4) (M:IntMat) :
    (integerCartanRawCoordinate i M:ℚ)=
      cartanRawCoordinate i ((Int.castRingHom ℚ).mapMatrix M) := by
  have h:=signed_coordinate_cast false i ⁅integerE i,M⁆
  change (integerSimpleCoordinate i ⁅integerE i,M⁆:ℚ)=
    simpleCoordinate i ((Int.castRingHom ℚ).mapMatrix ⁅integerE i,M⁆) at h
  change (integerSimpleCoordinate i ⁅integerE i,M⁆:ℚ)=
    simpleCoordinate i ⁅positive i,(Int.castRingHom ℚ).mapMatrix M⁆
  simpa only [Ring.lie_def,map_sub,map_mul,map_integerE] using h

theorem raw_coordinate_integral_vector (i:Fin 4) (k:BasisIndex) :
    integerCartanRawCoordinate i (integralRepresentation realizationData (integralVectors k))=
      cartanEntry i k := by
  apply (Int.cast_injective (α:=ℚ))
  rw [raw_coordinate_cast]
  have hc:=integralRepresentation_cast realizationData (integralVectors k)
  change (Int.castRingHom ℚ).mapMatrix (integralRepresentation realizationData (integralVectors k))=
    rationalRepresentation (vectors k) at hc
  rw [hc]
  exact cartan_coordinate_vector i k

def integerCartanCoordinate (b:Fin 4) : IntMat→ₗ[ℤ]ℤ :=
  -∑i:Fin 4,inverseExponents b i • integerCartanRawCoordinate i

private theorem inverse_cartan_entry : ∀b c:Fin 4,
    -(∑i:Fin 4,inverseExponents b i*(-A c i))=if c=b then 1 else 0 := by decide +kernel

theorem coordinate_integral_vector (b:Fin 4) (k:BasisIndex) :
    integerCartanCoordinate b (integralRepresentation realizationData (integralVectors k))=
      if k=.inr b then 1 else 0 := by
  simp only [integerCartanCoordinate,LinearMap.neg_apply,LinearMap.sum_apply,
    LinearMap.smul_apply,raw_coordinate_integral_vector,Int.zsmul_eq_mul]
  cases k with
  | inl z=>
    simp only [cartanEntry,mul_zero,Finset.sum_const_zero,neg_zero,Sum.inl_ne_inr,if_false]
  | inr c=>simpa only [cartanEntry,Sum.inr.injEq] using inverse_cartan_entry b c

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalIntegralCartanCoordinates
