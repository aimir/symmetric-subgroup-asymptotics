import SymmetricSubgroupAsymptotics.CFSGGTwoExceptionalCoefficientPilot
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSevenProjection

/-! The constant coefficient certificates are bound to the SAME original
integral tensor operators. The seven-coordinate column is literally the
proved source projection, and sourceOperator is exactly the checked
base-change divided power. No matrix faithfulness assumption is added. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalExceptionalCoefficientBinding
open CFSG.Models.Chevalley CFSGGTwoSerreMatrices
open CFSGGTwoOriginalFieldBasis CFSGGTwoOriginalSevenProjection
open CFSGGTwoExceptionalCoefficients
variable (K : Type) [Field K]
local notation "A" => CartanMatrix.G₂

theorem sevenProjection_val (x : Space A K) :
    (sevenProjection K x).val=column K (foldedBaseChange K x) := by
  funext i
  rcases i with j|j <;> fin_cases j
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change -(-(foldedBaseChange K x) (neg 0) (pos 2))=
      (foldedBaseChange K x) (neg 0) (pos 2)
    exact neg_neg _
  · rfl
  · rfl

theorem baseChange_sourceOperator (neg : Bool) (i : Fin 2) (k : Fin 4) (x : Space A K) :
    foldedBaseChange K ((integralOperator A neg i k.val).baseChange K x)=
      sourceOperator K neg i k (foldedBaseChange K x) := by
  change CFSGSerreQuadraticMatrix.baseChange realizationData K
      ((integralOperator A neg i k.val).baseChange K x)=
    CFSGIntegralQuadraticRootOperators.operator K (rootMatrix K neg i) (rootSecond K neg i)
      k.val (CFSGSerreQuadraticMatrix.baseChange realizationData K x)
  rw [CFSGSerreQuadraticMatrix.baseChange_operator,realizationData_fieldRoot,
    realizationData_fieldSecond]

theorem short_long_divided_power [CharP K 3] (k : Fin 4) :
    (sevenProjection K ((integralOperator A false 0 k.val).baseChange K
      (fieldVectors K (Sum.inl (false,1))))).val=
    targetOperator K false 0 k (sevenProjection K
      (fieldVectors K (Sum.inl (false,1)))).val := by
  rw [sevenProjection_val,sevenProjection_val,baseChange_sourceOperator]
  change column K (sourceOperator K false 0 k
      (CFSGSerreQuadraticMatrix.baseChange realizationData K
        (fieldVectors K (Sum.inl (false,1)))))=
    targetOperator K false 0 k (column K
      (CFSGSerreQuadraticMatrix.baseChange realizationData K
        (fieldVectors K (Sum.inl (false,1)))))
  rw [baseChange_vectors]
  exact CFSGGTwoExceptionalCoefficientPilot.field_coefficients K k

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalExceptionalCoefficientBinding
