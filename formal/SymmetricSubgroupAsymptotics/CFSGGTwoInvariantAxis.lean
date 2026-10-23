import SymmetricSubgroupAsymptotics.CFSGGTwoShortRootVectorActions
import SymmetricSubgroupAsymptotics.CFSGGTwoImageRealization
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBundledQuadratic

/-! The literal natural G2 matrices fix the SAME nonsingular axis in
their split eight-dimensional quadratic space. This statement includes
characteristic two and retains the quadratic value -1. In particular a
scalar natural G2 matrix is the identity scalar; no adjoint-to-natural
D4 lift or ambient D4 simplicity is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoInvariantAxis
open CFSGGTwoSerreMatrices
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexQuadraticForm

def axis (R : Type*) [CommRing R] : Index→R :=
  Pi.single (pos 3) 1-Pi.single (neg 3) 1

theorem root_fixes_axis (R : Type*) [CommRing R] (isNegative : Bool) (i : Fin 2) (t : R) :
    (rootTransvection R isNegative i t : Mat R)*ᵥaxis R=axis R := by
  fin_cases i
  · cases isNegative
    · change (rootTransvection R false 0 t : Mat R)*ᵥaxis R=axis R
      rw [CFSGGTwoShortRootVectorActions.positive_apply]
      funext x
      rcases x with j|j <;> fin_cases j <;>
        simp [CFSGGTwoShortRootVectorActions.positiveAction,axis,pos,neg,Fin.ext_iff]
    · change (rootTransvection R true 0 t : Mat R)*ᵥaxis R=axis R
      rw [CFSGGTwoShortRootVectorActions.negative_apply]
      funext x
      rcases x with j|j <;> fin_cases j <;>
        simp [CFSGGTwoShortRootVectorActions.negativeAction,axis,pos,neg,Fin.ext_iff]
  · change (rootTransvection R isNegative 1 t : Mat R)*ᵥaxis R=axis R
    have hM : rootMatrix R isNegative 1*ᵥaxis R=0 := by
      cases isNegative
      · change positive R 1*ᵥaxis R=0
        rw [positive_one_explicit,Matrix.sub_mulVec,Matrix.single_mulVec,Matrix.single_mulVec]
        funext x
        simp [axis,pos,neg,Fin.ext_iff]
      · change (positive R 1).transpose*ᵥaxis R=0
        rw [positive_one_explicit,Matrix.transpose_sub,Matrix.transpose_single,
          Matrix.transpose_single,Matrix.sub_mulVec,Matrix.single_mulVec,Matrix.single_mulVec]
        funext x
        simp [axis,pos,neg,Fin.ext_iff]
    have hS : rootSecond R isNegative 1=0 := by
      cases isNegative <;>
        simp [rootSecond,negativeSecond,positiveSecond]
    simp only [rootTransvection_val,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
      hM,hS,smul_zero,add_zero]

private def axisStabilizer (K : Type) [Field K] : Subgroup ((Mat K)ˣ) where
  carrier := {g | (g:Mat K)*ᵥaxis K=axis K}
  one_mem' := Matrix.one_mulVec _
  mul_mem' := by
    intro a b ha hb
    change ((a:Mat K)*(b:Mat K))*ᵥaxis K=axis K
    rw [←Matrix.mulVec_mulVec,hb,ha]
  inv_mem' := by
    intro a ha
    have hh := congrArg (fun v=>(↑(a⁻¹):Mat K)*ᵥv) ha
    dsimp only at hh
    have hia : (↑(a⁻¹):Mat K)*(a:Mat K)=1 :=
      congrArg (fun u : (Mat K)ˣ=>(u:Mat K)) (inv_mul_cancel a)
    rw [Matrix.mulVec_mulVec,hia,Matrix.one_mulVec] at hh
    exact hh.symm

theorem natural_fixes_axis (K : Type) [Field K] (g : naturalGroup K) :
    (g.val:Mat K)*ᵥaxis K=axis K := by
  have hle : naturalGroup K≤axisStabilizer K := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨negative,i,t,rfl⟩
    exact root_fixes_axis K negative i t
  exact hle g.property

theorem axis_norm (K : Type) [Field K] : splitQuadraticForm K 4 (axis K)=-1 := by
  rw [splitQuadraticForm_apply]
  simp [splitQ,leftPart,rightPart,dotProduct,Fin.sum_univ_succ,axis,pos,neg,Fin.ext_iff]

theorem axis_ne_zero (K : Type) [Field K] : axis K≠0 := by
  intro he
  have hh := congrFun he (pos 3)
  simp [axis,pos,neg] at hh

theorem scalar_eq_one_of_mem_natural (K : Type) [Field K] (g : naturalGroup K) (c : K)
    (hc : (g.val:Mat K)=c • (1:Mat K)) : c=1 := by
  have hh := congrFun (natural_fixes_axis K g) (pos 3)
  rw [hc,Matrix.smul_mulVec,Matrix.one_mulVec] at hh
  simpa [axis,pos,neg] using hh

end SymmetricSubgroupAsymptotics.CFSGGTwoInvariantAxis
