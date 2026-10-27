import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalRootCandidates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformRootMatrixArithmetic

/-! The SAME original D integral representation intertwines actual first
root actions with literal matrix brackets. No source faithfulness. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalIntegralAction
open CFSG.Models.Chevalley CFSGSerreDiagram
open CFSGOrthogonalDSerreMatrices
variable (r : ℕ) (hr : 4 ≤ r)

theorem generator_image (g : CartanMatrix.Generators (Fin r)) :
    integralOrthogonalRepresentation r hr (latticeGenerator (CartanMatrix.D r) g)=
      integerGenerator r g :=
  CFSGSerreSquareZeroMatrix.integralRepresentation_generator (realizationData r hr) g

theorem first_image (neg : Bool) (i : Fin r) (x : integralLattice (CartanMatrix.D r)) :
    integralOrthogonalRepresentation r hr (integralOperator (CartanMatrix.D r) neg i 1 x)=
      ⁅rootMatrix ℤ r neg i,integralOrthogonalRepresentation r hr x⁆ := by
  have h:=CFSGSerreSquareZeroMatrix.integralRepresentation_operator
    (realizationData r hr) neg i 1 x
  cases neg <;> simpa only [CFSGIntegralSquareZeroOperators.operator_one,
    CFSGSerreSquareZeroMatrix.integerRoot,CFSGSerreSquareZeroMatrix.rootGenerator,
    realizationData,integerGenerator,rootMatrix,Bool.false_eq_true,if_false,if_true,Ring.lie_def] using h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalIntegralAction
