import SymmetricSubgroupAsymptotics.CFSGExceptionalNormTwoBases
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckImageFourthCoefficient
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSourceTransport

/-! Complete integral quadratic data for the ORIGINAL pinned E6/E7/E8
Serre sources. Actual coordinate height discharges every simple-sign
condition; same-image fourth-coefficient cancellation holds in every ring. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalGeckIntegralData
open CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGExceptionalNormTwoBases CFSGNormTwoGeckHeightData
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckImageFourthCoefficient
open CFSGSerreQuadraticMatrix

local instance exceptionalGeckIntegralDataE6DecEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local instance exceptionalGeckIntegralDataE7DecEq : DecidableEq (Roots CartanMatrix.E₇) := Classical.decEq _
local instance exceptionalGeckIntegralDataE8DecEq : DecidableEq (Roots CartanMatrix.E₈) := Classical.decEq _

theorem E6_simple_sign (i : E6Base.support) : rootSign CartanMatrix.E₆ i= -1 :=
  rootSign_simple CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos i
theorem E7_simple_sign (i : E7Base.support) : rootSign CartanMatrix.E₇ i= -1 :=
  rootSign_simple CartanMatrix.E₇ CartanMatrix.E₇_diag CartanMatrix.E₇_transpose
    E7_positive_definite CartanMatrix.E₇_off_diag_nonpos i
theorem E8_simple_sign (i : E8Base.support) : rootSign CartanMatrix.E₈ i= -1 :=
  rootSign_simple CartanMatrix.E₈ CartanMatrix.E₈_diag CartanMatrix.E₈_transpose
    E8_positive_definite CartanMatrix.E₈_off_diag_nonpos i

def E6Data : Data CartanMatrix.E₆ (E6Base.support⊕Roots CartanMatrix.E₆) :=
  transportSource E6_cartan
    (realizationData CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index)
def E7Data : Data CartanMatrix.E₇ (E7Base.support⊕Roots CartanMatrix.E₇) :=
  transportSource E7_cartan
    (realizationData CartanMatrix.E₇ CartanMatrix.E₇_transpose E7_positive_definite E7Base E7Index)
def E8Data : Data CartanMatrix.E₈ (E8Base.support⊕Roots CartanMatrix.E₈) :=
  transportSource E8_cartan
    (realizationData CartanMatrix.E₈ CartanMatrix.E₈_transpose E8_positive_definite E8Base E8Index)

theorem E6Data_fourth (K : Type) [CommRing K] (neg : Bool) (i : Fin 6)
    (x : K⊗[ℤ]CFSG.Models.Chevalley.integralLattice CartanMatrix.E₆) :
    fieldSecond E6Data K neg i*baseChange E6Data K x*fieldSecond E6Data K neg i=0 :=
  transportSource_fourth E6_cartan _ K
    (CFSGNormTwoGeckImageFourthCoefficient.baseChange_image_fourth_coefficient_zero CartanMatrix.E₆ CartanMatrix.E₆_transpose
      E6_positive_definite E6Base E6Index E6_simple_sign K) neg i x
theorem E7Data_fourth (K : Type) [CommRing K] (neg : Bool) (i : Fin 7)
    (x : K⊗[ℤ]CFSG.Models.Chevalley.integralLattice CartanMatrix.E₇) :
    fieldSecond E7Data K neg i*baseChange E7Data K x*fieldSecond E7Data K neg i=0 :=
  transportSource_fourth E7_cartan _ K
    (CFSGNormTwoGeckImageFourthCoefficient.baseChange_image_fourth_coefficient_zero CartanMatrix.E₇ CartanMatrix.E₇_transpose
      E7_positive_definite E7Base E7Index E7_simple_sign K) neg i x
theorem E8Data_fourth (K : Type) [CommRing K] (neg : Bool) (i : Fin 8)
    (x : K⊗[ℤ]CFSG.Models.Chevalley.integralLattice CartanMatrix.E₈) :
    fieldSecond E8Data K neg i*baseChange E8Data K x*fieldSecond E8Data K neg i=0 :=
  transportSource_fourth E8_cartan _ K
    (CFSGNormTwoGeckImageFourthCoefficient.baseChange_image_fourth_coefficient_zero CartanMatrix.E₈ CartanMatrix.E₈_transpose
      E8_positive_definite E8Base E8Index E8_simple_sign K) neg i x

end SymmetricSubgroupAsymptotics.CFSGExceptionalGeckIntegralData
