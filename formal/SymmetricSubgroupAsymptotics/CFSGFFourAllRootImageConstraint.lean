import SymmetricSubgroupAsymptotics.CFSGFFourShortRootAdjoint
import SymmetricSubgroupAsymptotics.CFSGFFourLongRootFourthCoefficient
import SymmetricSubgroupAsymptotics.CFSGQuadraticAdjointCubeConstraint
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticImageConstraint

/-! All four original F4 simple roots, of both lengths and signs,
have vanishing fourth conjugation coefficient on the SAME rational
source image. Integral lattice descent proves the same over every
commutative ring, including characteristics two and three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
open CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGSerreQuadraticMatrix
local instance allRootImageConstraintDecEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

theorem rationalRoot_false (i : Fin 4) : fieldRoot realizationData ℚ false i=positive i := by
  change (Int.castRingHom ℚ).mapMatrix (integerE i)=positive i
  exact map_integerE i

theorem rationalRoot_true (i : Fin 4) : fieldRoot realizationData ℚ true i=negative i := by
  change (Int.castRingHom ℚ).mapMatrix (integerF i)=negative i
  exact map_integerF i

theorem rationalSecond_false (i : Fin 4) :
    fieldSecond realizationData ℚ false i=positiveSecond i := by
  change (Int.castRingHom ℚ).mapMatrix (positiveSecondZ i)=positiveSecond i
  exact map_positiveSecondZ i

theorem rationalSecond_true (i : Fin 4) :
    fieldSecond realizationData ℚ true i=negativeSecond i := by
  change (Int.castRingHom ℚ).mapMatrix (negativeSecondZ i)=negativeSecond i
  exact map_negativeSecondZ i

theorem rational_short_fourth (neg : Bool) (i : Fin 4) (hi : i=0 ∨ i=1)
    (x : CFSG.Models.Chevalley.RationalLie CartanMatrix.F₄) :
    fieldSecond realizationData ℚ neg i*realizationData.rational x*
      fieldSecond realizationData ℚ neg i=0 := by
  apply CFSGQuadraticAdjointCubeConstraint.second_sandwich_zero
    (fieldRoot realizationData ℚ neg i) (fieldSecond realizationData ℚ neg i)
    (realizationData.rational x) (fieldRoot_square realizationData ℚ neg i)
    (fieldRoot_mul_second realizationData ℚ neg i) (fieldSecond_mul_root realizationData ℚ neg i)
  cases neg
  · rw [rationalRoot_false]
    exact short_positive_ad_cube i hi _ (rational_image_mem_geck x)
  · rw [rationalRoot_true]
    exact short_negative_ad_cube i hi _ (rational_image_mem_geck x)

theorem rational_last_fourth (neg : Bool)
    (x : CFSG.Models.Chevalley.RationalLie CartanMatrix.F₄) :
    fieldSecond realizationData ℚ neg 3*realizationData.rational x*
      fieldSecond realizationData ℚ neg 3=0 := by
  have hx := rational_image_mem_geck x
  cases neg
  · rw [rationalSecond_false]
    change e6Second 1*realizationData.rational x*e6Second 1=0
    exact CFSGNormTwoGeckBasedForm.positive_fourth_coefficient_zero
      CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base
      CFSGExceptionalGeckIntegralData.E6_simple_sign _ hx (E6Index 1)
  · rw [rationalSecond_true]
    change CFSGNormTwoGeckNegative.negativeSecondMatrix CartanMatrix.E₆
      CartanMatrix.E₆_transpose E6_positive_definite E6Base (E6Index 1)*
      realizationData.rational x*CFSGNormTwoGeckNegative.negativeSecondMatrix CartanMatrix.E₆
      CartanMatrix.E₆_transpose E6_positive_definite E6Base (E6Index 1)=0
    exact CFSGNormTwoGeckBasedForm.negative_fourth_coefficient_zero
      CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base
      CFSGExceptionalGeckIntegralData.E6_simple_sign _ hx (E6Index 1)

theorem rational_all_fourth (neg : Bool) (i : Fin 4)
    (x : CFSG.Models.Chevalley.RationalLie CartanMatrix.F₄) :
    fieldSecond realizationData ℚ neg i*realizationData.rational x*
      fieldSecond realizationData ℚ neg i=0 := by
  fin_cases i
  · exact rational_short_fourth neg 0 (Or.inl rfl) x
  · exact rational_short_fourth neg 1 (Or.inr rfl) x
  · exact rational_long_fourth neg x
  · exact rational_last_fourth neg x

theorem baseChange_all_fourth (K : Type*) [CommRing K] (neg : Bool) (i : Fin 4)
    (x : K⊗[ℤ]CFSG.Models.Chevalley.integralLattice CartanMatrix.F₄) :
    fieldSecond realizationData K neg i*baseChange realizationData K x*
      fieldSecond realizationData K neg i=0 :=
  baseChange_image_fourth_coefficient_zero realizationData rational_all_fourth K neg i x

end SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
