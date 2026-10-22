import SymmetricSubgroupAsymptotics.CFSGFFourIntegralRealization
import SymmetricSubgroupAsymptotics.CFSGFFourRationalImage
import SymmetricSubgroupAsymptotics.CFSGExceptionalGeckIntegralData
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBasedForm
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSelectedImageConstraint

/-! Long F4 node 2 is literally E6 node 3. The checked E6 height form
therefore cancels its fourth coefficient on the SAME folded F4 image.
No short-root cancellation or target-group recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
open CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGSerreQuadraticMatrix
local instance fFourLongRootFourthDecEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

theorem rationalSecond_long_false : fieldSecond realizationData ℚ false 2=e6Second 3 := by
  change (Int.castRingHom ℚ).mapMatrix (positiveSecondZ 2)=_
  rw [map_positiveSecondZ]
  rfl

theorem rationalSecond_long_true : fieldSecond realizationData ℚ true 2=
    CFSGNormTwoGeckNegative.negativeSecondMatrix CartanMatrix.E₆ CartanMatrix.E₆_transpose
      E6_positive_definite E6Base (E6Index 3) := by
  change (Int.castRingHom ℚ).mapMatrix (negativeSecondZ 2)=_
  rw [map_negativeSecondZ]
  rfl

theorem rational_long_fourth (neg : Bool)
    (x : CFSG.Models.Chevalley.RationalLie CartanMatrix.F₄) :
    fieldSecond realizationData ℚ neg 2*realizationData.rational x*
      fieldSecond realizationData ℚ neg 2=0 := by
  have hx := rational_image_mem_geck x
  cases neg
  · rw [rationalSecond_long_false]
    exact CFSGNormTwoGeckBasedForm.positive_fourth_coefficient_zero
      CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base
      CFSGExceptionalGeckIntegralData.E6_simple_sign _ hx (E6Index 3)
  · rw [rationalSecond_long_true]
    exact CFSGNormTwoGeckBasedForm.negative_fourth_coefficient_zero
      CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base
      CFSGExceptionalGeckIntegralData.E6_simple_sign _ hx (E6Index 3)

theorem baseChange_long_fourth (K : Type*) [CommRing K] (neg : Bool)
    (x : K⊗[ℤ]CFSG.Models.Chevalley.integralLattice CartanMatrix.F₄) :
    fieldSecond realizationData K neg 2*baseChange realizationData K x*
      fieldSecond realizationData K neg 2=0 :=
  baseChange_selected_fourth realizationData neg 2 (rational_long_fourth neg) K x

end SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
