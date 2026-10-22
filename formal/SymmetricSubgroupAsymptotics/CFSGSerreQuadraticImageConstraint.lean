import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrixOperators

/-! A proved rational fourth-coefficient equation descends through the
actual integral lattice image and tensor base change. This shared lemma
retains every lattice element; it does not replace the image by all matrices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
open CFSG.Models.Chevalley
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)
    (hfour : ∀ (neg : Bool) (i : Fin n) (x : RationalLie A),
      fieldSecond D ℚ neg i*D.rational x*fieldSecond D ℚ neg i=0)

include hfour

theorem integral_image_fourth_coefficient_zero
    (x : integralLattice A) (neg : Bool) (i : Fin n) :
    D.integerSecond neg i*integralRepresentation D x*D.integerSecond neg i=0 := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective I
  change (Int.castRingHom ℚ).mapMatrix
      (D.integerSecond neg i*integralRepresentation D x*D.integerSecond neg i)=
    (Int.castRingHom ℚ).mapMatrix 0
  simp only [map_mul,map_zero]
  change fieldSecond D ℚ neg i*
    CFSGSerreSquareZeroMatrix.integerCast I (integralRepresentation D x)*
    fieldSecond D ℚ neg i=0
  rw [integralRepresentation_cast]
  exact hfour neg i x.val

theorem mapped_integral_image_fourth_coefficient_zero (K : Type*) [CommRing K]
    (x : integralLattice A) (neg : Bool) (i : Fin n) :
    fieldSecond D K neg i*(Int.castRingHom K).mapMatrix (integralRepresentation D x)*
      fieldSecond D K neg i=0 := by
  have hh := congrArg (Int.castRingHom K).mapMatrix
    (integral_image_fourth_coefficient_zero D hfour x neg i)
  simpa only [map_mul,map_zero,fieldSecond] using hh

theorem baseChange_image_fourth_coefficient_zero (K : Type*) [CommRing K]
    (neg : Bool) (i : Fin n) (x : K⊗[ℤ]integralLattice A) :
    fieldSecond D K neg i*baseChange D K x*fieldSecond D K neg i=0 := by
  induction x using TensorProduct.induction_on with
  | zero=>simp only [map_zero,mul_zero,zero_mul]
  | tmul a x=>
    rw [baseChange_tmul,mul_smul_comm,smul_mul_assoc,
      mapped_integral_image_fourth_coefficient_zero D hfour,smul_zero]
  | add x y hx hy=>simp only [map_add,mul_add,add_mul,hx,hy,add_zero]

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
