import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntegralRealization
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRationalForm

/-! The proved original rational image constraint descends to the SAME
integer image and then to its actual tensor base change in every field.
This is the missing fourth-coefficient cancellation for pinned roots. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
open CFSG.Models.Chevalley

theorem integral_image_fourth_coefficient_zero (r : ℕ)
    (x : integralLattice (CartanMatrix.B r).transpose) (neg : Bool) (i : Fin r) :
    rootSecond ℤ r neg i*integralOrthogonalRepresentation r x*rootSecond ℤ r neg i=0 := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective (Index r)
  change (Int.castRingHom ℚ).mapMatrix
      (rootSecond ℤ r neg i*integralOrthogonalRepresentation r x*rootSecond ℤ r neg i)=
    (Int.castRingHom ℚ).mapMatrix 0
  simp only [map_mul,map_zero]
  change CFSGSerreQuadraticMatrix.fieldSecond (realizationData r) ℚ neg i*
      CFSGSerreSquareZeroMatrix.integerCast (Index r) (integralOrthogonalRepresentation r x)*
      CFSGSerreQuadraticMatrix.fieldSecond (realizationData r) ℚ neg i=0
  rw [CFSGSerreQuadraticMatrix.integralRepresentation_cast]
  simp only [realizationData_fieldSecond]
  exact rational_image_fourth_coefficient_zero r x.val neg i

theorem mapped_integral_image_fourth_coefficient_zero (K : Type*) [CommRing K] (r : ℕ)
    (x : integralLattice (CartanMatrix.B r).transpose) (neg : Bool) (i : Fin r) :
    rootSecond K r neg i*(Int.castRingHom K).mapMatrix (integralOrthogonalRepresentation r x)*
      rootSecond K r neg i=0 := by
  have hh := congrArg (Int.castRingHom K).mapMatrix
    (integral_image_fourth_coefficient_zero r x neg i)
  simp only [map_mul,map_zero] at hh
  change CFSGSerreQuadraticMatrix.fieldSecond (realizationData r) K neg i*
      (Int.castRingHom K).mapMatrix (integralOrthogonalRepresentation r x)*
      CFSGSerreQuadraticMatrix.fieldSecond (realizationData r) K neg i=0 at hh
  simpa only [realizationData_fieldSecond] using hh

theorem baseChange_image_fourth_coefficient_zero (K : Type*) [CommRing K] (r : ℕ)
    (neg : Bool) (i : Fin r) (x : K ⊗[ℤ] integralLattice (CartanMatrix.B r).transpose) :
    rootSecond K r neg i*orthogonalBaseChange K r x*rootSecond K r neg i=0 := by
  induction x using TensorProduct.induction_on with
  | zero=>simp only [map_zero,mul_zero,zero_mul]
  | tmul a x=>
    rw [CFSGSerreQuadraticMatrix.baseChange_tmul,mul_smul_comm,smul_mul_assoc,
      mapped_integral_image_fourth_coefficient_zero,smul_zero]
  | add x y hx hy=>
    simp only [map_add,mul_add,add_mul,hx,hy,add_zero]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
