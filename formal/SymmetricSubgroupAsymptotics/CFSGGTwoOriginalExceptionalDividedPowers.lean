import SymmetricSubgroupAsymptotics.CFSGGTwoExceptionalAllCoefficients
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalExceptionalCoefficientBinding
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Full exceptional divided-power covariance on the ORIGINAL tensor
space. The finite coefficient tables are applied to the proved original
basis and extended by linearity. No original image faithfulness or
simplicity hypothesis is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalExceptionalDividedPowers
open CFSG.Models.Chevalley CFSGGTwoSerreMatrices CFSGGTwoAxisCoordinates
open CFSGGTwoOriginalFieldBasis CFSGGTwoOriginalSevenProjection
open CFSGGTwoExceptionalCoefficients CFSGGTwoOriginalExceptionalCoefficientBinding
variable (K : Type) [Field K]
local notation "A" => CartanMatrix.G₂

def targetLinearOperator (neg : Bool) (i : Fin 2) (k : Fin 4) :
    (Index → K) →ₗ[K] (Index → K) :=
  if i=0 then match k.val with
    | 0 => LinearMap.id
    | 3 => Matrix.mulVecLin (rootMatrix K neg 1)
    | _ => 0
  else match k.val with
    | 0 => LinearMap.id
    | 1 => Matrix.mulVecLin (rootMatrix K neg 0)
    | 2 => Matrix.mulVecLin (rootSecond K neg 0)
    | _ => 0

theorem targetLinearOperator_apply (neg : Bool) (i : Fin 2) (k : Fin 4) (v : Index → K) :
    targetLinearOperator K neg i k v=targetOperator K neg i k v := by
  fin_cases i <;> fin_cases k <;> rfl

def projectionLinear : Space A K →ₗ[K] (Index → K) :=
  (axisHyperplane K).subtype.comp (sevenProjection K)

theorem basis_divided_power [CharP K 3] (neg : Bool) (i : Fin 2) (k : Fin 4)
    (j : CFSGGTwoOriginalMatrixCoordinates.BasisIndex) :
    (sevenProjection K ((integralOperator A neg i k.val).baseChange K
      (fieldVectors K j))).val=
    targetOperator K neg i k (sevenProjection K (fieldVectors K j)).val := by
  rw [sevenProjection_val,sevenProjection_val,baseChange_sourceOperator]
  change column K (sourceOperator K neg i k
      (CFSGSerreQuadraticMatrix.baseChange realizationData K (fieldVectors K j)))=
    targetOperator K neg i k (column K
      (CFSGSerreQuadraticMatrix.baseChange realizationData K (fieldVectors K j)))
  rw [baseChange_vectors]
  exact CFSGGTwoExceptionalAllCoefficients.field_coefficients K neg i k j

theorem divided_power [CharP K 3] (neg : Bool) (i : Fin 2) (k : Fin 4)
    (x : Space A K) :
    (sevenProjection K ((integralOperator A neg i k.val).baseChange K x)).val=
    targetOperator K neg i k (sevenProjection K x).val := by
  classical
  let L : Space A K →ₗ[K] (Index → K) :=
    (projectionLinear K).comp ((integralOperator A neg i k.val).baseChange K)
  let R : Space A K →ₗ[K] (Index → K) :=
    (targetLinearOperator K neg i k).comp (projectionLinear K)
  have hb (j : CFSGGTwoOriginalMatrixCoordinates.BasisIndex) :
      L (fieldVectors K j)=R (fieldVectors K j) := by
    change (sevenProjection K ((integralOperator A neg i k.val).baseChange K
      (fieldVectors K j))).val=
      targetLinearOperator K neg i k (sevenProjection K (fieldVectors K j)).val
    rw [targetLinearOperator_apply]
    exact basis_divided_power K neg i k j
  rw [←targetLinearOperator_apply]
  change L x=R x
  obtain ⟨c,rfl⟩ := fieldCombination_surjective K x
  change L (∑j,c j • fieldVectors K j)=R (∑j,c j • fieldVectors K j)
  simp only [map_sum,map_smul,hb]

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalExceptionalDividedPowers
