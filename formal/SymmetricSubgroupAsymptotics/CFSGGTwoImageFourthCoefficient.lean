import SymmetricSubgroupAsymptotics.CFSGGTwoIntegralRealization
import SymmetricSubgroupAsymptotics.CFSGGTwoRationalForm

/-! The proved original rational image constraint descends to the SAME
integer image and then to its actual tensor base change in every field.
This is the missing fourth-coefficient cancellation for pinned roots. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
open CFSG.Models.Chevalley

theorem integral_image_fourth_coefficient_zero 
    (x : integralLattice CartanMatrix.G₂) (neg : Bool) (i : Fin 2) :
    rootSecond ℤ neg i*(CFSGSerreQuadraticMatrix.integralRepresentation realizationData) x*rootSecond ℤ neg i=0 := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective Index
  change (Int.castRingHom ℚ).mapMatrix
      (rootSecond ℤ neg i*(CFSGSerreQuadraticMatrix.integralRepresentation realizationData) x*rootSecond ℤ neg i)=
    (Int.castRingHom ℚ).mapMatrix 0
  simp only [map_mul,map_zero]
  change CFSGSerreQuadraticMatrix.fieldSecond (realizationData) ℚ neg i*
      CFSGSerreSquareZeroMatrix.integerCast Index ((CFSGSerreQuadraticMatrix.integralRepresentation realizationData) x)*
      CFSGSerreQuadraticMatrix.fieldSecond (realizationData) ℚ neg i=0
  rw [CFSGSerreQuadraticMatrix.integralRepresentation_cast]
  simp only [realizationData_fieldSecond]
  exact rational_image_fourth_coefficient_zero x.val neg i

theorem mapped_integral_image_fourth_coefficient_zero (K : Type*) [CommRing K] 
    (x : integralLattice CartanMatrix.G₂) (neg : Bool) (i : Fin 2) :
    rootSecond K neg i*(Int.castRingHom K).mapMatrix ((CFSGSerreQuadraticMatrix.integralRepresentation realizationData) x)*
      rootSecond K neg i=0 := by
  have hh := congrArg (Int.castRingHom K).mapMatrix
    (integral_image_fourth_coefficient_zero x neg i)
  simp only [map_mul,map_zero] at hh
  change CFSGSerreQuadraticMatrix.fieldSecond (realizationData) K neg i*
      (Int.castRingHom K).mapMatrix ((CFSGSerreQuadraticMatrix.integralRepresentation realizationData) x)*
      CFSGSerreQuadraticMatrix.fieldSecond (realizationData) K neg i=0 at hh
  simpa only [realizationData_fieldSecond] using hh

theorem baseChange_image_fourth_coefficient_zero (K : Type*) [CommRing K] 
    (neg : Bool) (i : Fin 2) (x : K ⊗[ℤ] integralLattice CartanMatrix.G₂) :
    rootSecond K neg i*foldedBaseChange K x*rootSecond K neg i=0 := by
  induction x using TensorProduct.induction_on with
  | zero=>simp only [map_zero,mul_zero,zero_mul]
  | tmul a x=>
    rw [CFSGSerreQuadraticMatrix.baseChange_tmul,mul_smul_comm,smul_mul_assoc,
      mapped_integral_image_fourth_coefficient_zero,smul_zero]
  | add x y hx hy=>
    simp only [map_add,mul_add,add_mul,hx,hy,add_zero]

end SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
