import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A finite nonnegative coordinate combination has nonpositive image
when every column occurring in its support has nonpositive image. This
is an integer-linear statement, before any reduction to a field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGNonpositiveCoordinateCone

theorem linearMap_nonpositive_of_support_columns {I J : Type*} [Fintype I] [DecidableEq I]
    (L : (I→ℤ)→ₗ[ℤ](J→ℤ)) (x : I→ℤ)
    (hx : ∀i,0≤x i)
    (hcolumns : ∀i,x i≠0→∀j,L (Pi.single i 1) j≤0) :
    ∀j,L x j≤0 := by
  intro j
  have he := congrArg (fun z : I→ℤ=>L z j) (pi_eq_sum_univ' x)
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at he
  rw [he]
  apply Finset.sum_nonpos
  intro i _
  by_cases hi : x i=0
  · rw [hi,zero_mul]
  · exact mul_nonpos_of_nonneg_of_nonpos (hx i) (hcolumns i hi j)

end SymmetricSubgroupAsymptotics.CFSGNonpositiveCoordinateCone
