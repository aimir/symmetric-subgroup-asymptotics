import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrixActions

/-! Localizing the proved image constraint to one selected actual root.
This supports folded representations without asserting any truncation
identity for the other source roots. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
open CFSG.Models.Chevalley
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)
    (neg : Bool) (i : Fin n)
    (hfour : ∀x : RationalLie A,fieldSecond D ℚ neg i*D.rational x*fieldSecond D ℚ neg i=0)
include hfour

theorem integral_selected_fourth (x : integralLattice A) :
    D.integerSecond neg i*integralRepresentation D x*D.integerSecond neg i=0 := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective I
  change (Int.castRingHom ℚ).mapMatrix (_*_*_)=(Int.castRingHom ℚ).mapMatrix 0
  simp only [map_mul,map_zero]
  change fieldSecond D ℚ neg i*
    CFSGSerreSquareZeroMatrix.integerCast I (integralRepresentation D x)*fieldSecond D ℚ neg i=0
  rw [integralRepresentation_cast]
  exact hfour x.val

theorem mapped_integral_selected_fourth (K : Type*) [CommRing K] (x : integralLattice A) :
    fieldSecond D K neg i*(Int.castRingHom K).mapMatrix (integralRepresentation D x)*
      fieldSecond D K neg i=0 := by
  have hh := congrArg (Int.castRingHom K).mapMatrix (integral_selected_fourth D neg i hfour x)
  simpa only [map_mul,map_zero,fieldSecond] using hh

theorem baseChange_selected_fourth (K : Type*) [CommRing K] (x : K⊗[ℤ]integralLattice A) :
    fieldSecond D K neg i*baseChange D K x*fieldSecond D K neg i=0 := by
  induction x using TensorProduct.induction_on with
  | zero=>simp only [map_zero,mul_zero,zero_mul]
  | tmul a x=>
    rw [baseChange_tmul,mul_smul_comm,smul_mul_assoc,
      mapped_integral_selected_fourth D neg i hfour,smul_zero]
  | add x y hx hy=>simp only [map_add,mul_add,add_mul,hx,hy,add_zero]

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
