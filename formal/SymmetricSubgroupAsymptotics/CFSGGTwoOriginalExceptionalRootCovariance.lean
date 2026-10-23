import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalExceptionalDividedPowers
import SymmetricSubgroupAsymptotics.CFSGGTwoImageRealization

/-! All signed ORIGINAL simple root operators intertwine with the literal
native seven-space action after long/short exchange. The original short
parameter is cubed and the original long parameter is unchanged. This
uses actual divided-power coefficients, not a presumed twist map. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalExceptionalRootCovariance
open CFSG.Models.Chevalley CFSGGTwoSerreMatrices
open CFSGGTwoOriginalSevenProjection CFSGGTwoOriginalExceptionalDividedPowers
open CFSGGTwoExceptionalCoefficients
variable (K : Type) [Field K] [CharP K 3]
local notation "A" => CartanMatrix.G₂

private theorem projectionLinear_apply (x : Space A K) :
    projectionLinear K x=(sevenProjection K x).val := rfl

private theorem expanded_covariance (neg : Bool) (i : Fin 2) (t : K) (x : Space A K) :
    (sevenProjection K (rootOperator A K neg i t x)).val=
      (sevenProjection K x).val+
      t • targetOperator K neg i 1 (sevenProjection K x).val+
      t^2 • targetOperator K neg i 2 (sevenProjection K x).val+
      t^3 • targetOperator K neg i 3 (sevenProjection K x).val := by
  have hd (k : Fin 4) : projectionLinear K
      ((integralOperator A neg i k.val).baseChange K x)=
      targetOperator K neg i k (projectionLinear K x) := divided_power K neg i k x
  have h0 : projectionLinear K ((integralOperator A neg i 0).baseChange K x)=
      targetOperator K neg i 0 (projectionLinear K x) := hd 0
  have h1 : projectionLinear K ((integralOperator A neg i 1).baseChange K x)=
      targetOperator K neg i 1 (projectionLinear K x) := hd 1
  have h2 : projectionLinear K ((integralOperator A neg i 2).baseChange K x)=
      targetOperator K neg i 2 (projectionLinear K x) := hd 2
  have h3 : projectionLinear K ((integralOperator A neg i 3).baseChange K x)=
      targetOperator K neg i 3 (projectionLinear K x) := hd 3
  change projectionLinear K (rootOperator A K neg i t x)=_
  simp only [rootOperator,Finset.sum_range_succ,Finset.sum_range_zero,
    LinearMap.add_apply,LinearMap.smul_apply,
    pow_zero,pow_one,one_smul,zero_add,map_add,map_smul]
  rw [h0,h1,h2,h3]
  have hz : targetOperator K neg i 0 (projectionLinear K x)=projectionLinear K x := by
    fin_cases i <;> rfl
  rw [hz,projectionLinear_apply]

theorem short_covariance (neg : Bool) (t : K) (x : Space A K) :
    (sevenProjection K (rootOperator A K neg 0 t x)).val=
      (rootTransvection K neg 1 (t^3) : Mat K) *ᵥ (sevenProjection K x).val := by
  rw [expanded_covariance]
  have hs : rootSecond K neg 1=0 := by cases neg <;> rfl
  change (sevenProjection K x).val+t • (0 : Index → K)+
      t^2 • (0 : Index → K)+t^3 • (rootMatrix K neg 1 *ᵥ (sevenProjection K x).val)=_
  simp only [smul_zero,add_zero,rootTransvection_val,Matrix.add_mulVec,
    Matrix.smul_mulVec,Matrix.one_mulVec,hs]

theorem long_covariance (neg : Bool) (t : K) (x : Space A K) :
    (sevenProjection K (rootOperator A K neg 1 t x)).val=
      (rootTransvection K neg 0 t : Mat K) *ᵥ (sevenProjection K x).val := by
  rw [expanded_covariance]
  change (sevenProjection K x).val+t • (rootMatrix K neg 0 *ᵥ (sevenProjection K x).val)+
      t^2 • (rootSecond K neg 0 *ᵥ (sevenProjection K x).val)+t^3 • (0 : Index → K)=_
  simp only [smul_zero,add_zero,rootTransvection_val,Matrix.add_mulVec,
    Matrix.smul_mulVec,Matrix.one_mulVec]

def exchangedNode (i : Fin 2) : Fin 2 := if i=0 then 1 else 0

def exceptionalParameter (i : Fin 2) (t : K) : K := if i=0 then t^3 else t

theorem root_covariance (neg : Bool) (i : Fin 2) (t : K) (x : Space A K) :
    (sevenProjection K (rootOperator A K neg i t x)).val=
      (rootTransvection K neg (exchangedNode i) (exceptionalParameter K i t) : Mat K) *ᵥ
        (sevenProjection K x).val := by
  fin_cases i
  · exact short_covariance K neg t x
  · exact long_covariance K neg t x

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalExceptionalRootCovariance
