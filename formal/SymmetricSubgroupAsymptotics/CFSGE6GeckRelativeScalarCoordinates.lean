import SymmetricSubgroupAsymptotics.CFSGE6GeckRelativeScalarTuples
import Mathlib.Algebra.BigOperators.Pi

/-! Recover the two fixed-subfield unit coordinates from a literal
diagram-field fixed scalar tuple, and decompose the tuple into its four
simple diagram-orbit factors. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckRelativeScalarCoordinates
open CFSGE6GeckRelativeScalarTuples CFSGE6GeckFixedSimpleParameters CFSGSerreDiagram

variable (K : Type) [Field K] (sigma : RingAut K)

theorem fixed_scalar_value (x : relativeScalars K sigma) (i : Fin 6)
    (hi : e6Permutation i=i) : sigma (x.val i : K)=(x.val i : K) := by
  have hx := x.property i
  change scalarTwist K sigma (x.val i)=x.val (e6Permutation i) at hx
  rw [hi] at hx
  exact congrArg Units.val hx

def fixedScalar (x : relativeScalars K sigma) (i : Fin 6) (hi : e6Permutation i=i) :
    (fixedCoefficient K sigma)ˣ :=
  Units.mk0 ⟨(x.val i : K),fixed_scalar_value K sigma x i hi⟩ (by
    intro he
    exact (x.val i).ne_zero (congrArg (fun a : fixedCoefficient K sigma => (a : K)) he))

@[simp] theorem fixedScalar_inclusion (x : relativeScalars K sigma) (i : Fin 6)
    (hi : e6Permutation i=i) : fixedUnit K sigma (fixedScalar K sigma x i hi)=x.val i :=
  Units.ext rfl

theorem scalar_tuple_decomposition (x : relativeScalars K sigma) :
    x.val=(Pi.mulSingle 0 (x.val 0)*Pi.mulSingle 5 (scalarTwist K sigma (x.val 0)))*
      ((Pi.mulSingle 2 (x.val 2)*Pi.mulSingle 4 (scalarTwist K sigma (x.val 2)))*
        (Pi.mulSingle 1 (x.val 1)*Pi.mulSingle 3 (x.val 3))) := by
  have hzero := x.property 0
  have htwo := x.property 2
  change scalarTwist K sigma (x.val 0)=x.val 5 at hzero
  change scalarTwist K sigma (x.val 2)=x.val 4 at htwo
  funext i
  fin_cases i <;> simp [Pi.mulSingle_apply,hzero,htwo]

end SymmetricSubgroupAsymptotics.CFSGE6GeckRelativeScalarCoordinates
