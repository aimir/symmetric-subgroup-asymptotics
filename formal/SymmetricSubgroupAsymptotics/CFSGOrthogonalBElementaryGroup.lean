import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
import SymmetricSubgroupAsymptotics.CFSGQuadraticRootExponential
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Independently defined natural B elementary root matrix subgroup.
Short roots use their genuine quadratic polynomial, in all characteristics. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

def rootMatrix (negative : Bool) (i : Fin r) : Mat R r :=
  if negative then CFSGOrthogonalBSerreMatrices.negative R r i else positive R r i

def rootSecond (negative : Bool) (i : Fin r) : Mat R r :=
  if negative then negativeSecond R r i else positiveSecond R r i

theorem rootMatrix_square (negative : Bool) (i : Fin r) :
    rootMatrix R r negative i*rootMatrix R r negative i=rootSecond R r negative i+rootSecond R r negative i := by
  cases negative
  · exact positive_square R r i
  · exact negative_square R r i

theorem rootMatrix_mul_second (negative : Bool) (i : Fin r) :
    rootMatrix R r negative i*rootSecond R r negative i=0 := by
  cases negative
  · exact positive_mul_second R r i
  · exact negative_mul_second R r i

theorem rootSecond_mul_matrix (negative : Bool) (i : Fin r) :
    rootSecond R r negative i*rootMatrix R r negative i=0 := by
  cases negative
  · exact second_mul_positive R r i
  · exact second_mul_negative R r i

theorem rootSecond_square (negative : Bool) (i : Fin r) :
    rootSecond R r negative i*rootSecond R r negative i=0 := by
  cases negative
  · exact positiveSecond_sq_zero R r i
  · exact negativeSecond_sq_zero R r i

def rootTransvection (negative : Bool) (i : Fin r) (t : R) : (Mat R r)ˣ :=
  CFSGQuadraticRootExponential.rootUnit (rootMatrix R r negative i) (rootSecond R r negative i)
    (rootMatrix_square R r negative i) (rootMatrix_mul_second R r negative i)
    (rootSecond_mul_matrix R r negative i) (rootSecond_square R r negative i) t

@[simp] theorem rootTransvection_val (negative : Bool) (i : Fin r) (t : R) :
    (rootTransvection R r negative i t : Mat R r)=
      1+t • rootMatrix R r negative i+t^2 • rootSecond R r negative i := rfl
@[simp] theorem rootTransvection_inv_val (negative : Bool) (i : Fin r) (t : R) :
    (↑((rootTransvection R r negative i t)⁻¹):Mat R r)=
      1-t • rootMatrix R r negative i+t^2 • rootSecond R r negative i :=
  CFSGQuadraticRootExponential.rootUnit_inv_val _ _ _ _ _ _ t

def elementaryRootGroup : Subgroup ((Mat R r)ˣ) :=
  Subgroup.closure {u|∃negative i t,u=rootTransvection R r negative i t}

theorem rootTransvection_mem (negative : Bool) (i : Fin r) (t : R) :
    rootTransvection R r negative i t∈elementaryRootGroup R r :=
  Subgroup.subset_closure ⟨negative,i,t,rfl⟩

def elementaryProjective := elementaryRootGroup R r ⧸ Subgroup.center (elementaryRootGroup R r)
instance elementaryProjective_group : Group (elementaryProjective R r) := inferInstanceAs
  (Group (elementaryRootGroup R r ⧸ Subgroup.center (elementaryRootGroup R r)))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
