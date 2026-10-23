import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! In odd characteristic, every scalar is a difference of two squares.
Thus square-scalar covariance already forces full field multiplication,
and a nonzero additive subgroup stable under squares is the whole field.
These statements require neither a finite field nor a chosen generator. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSquareScalarRigidity
variable {K : Type*} [Field K]

theorem difference_of_two_squares (h2 : (2:K)≠0) (x : K) :
    ((x+1)/2)^2-((x-1)/2)^2=x := by
  field_simp [h2]
  ring

theorem additive_map_mul_of_square_covariance (h2 : (2:K)≠0)
    (f : K→+K) (hsq : ∀ t x : K, f (t^2*x)=f (t^2)*f x) (x y : K) :
    f (x*y)=f x*f y := by
  let a := (x+1)/2
  let b := (x-1)/2
  have hx : a^2-b^2=x := difference_of_two_squares h2 x
  calc
    f (x*y)=f ((a^2-b^2)*y) := by rw [hx]
    _=f (a^2*y)-f (b^2*y) := by rw [sub_mul,map_sub]
    _=f (a^2)*f y-f (b^2)*f y := by rw [hsq,hsq]
    _=(f (a^2)-f (b^2))*f y := (sub_mul _ _ _).symm
    _=f (a^2-b^2)*f y := by rw [map_sub]
    _=f x*f y := by rw [hx]

def ringEquivOfSquareCovariance (h2 : (2:K)≠0) (f : K≃+K)
    (hsq : ∀ t x : K, f (t^2*x)=f (t^2)*f x) : K≃+*K where
  toEquiv := f.toEquiv
  map_add' := f.map_add
  map_mul' := additive_map_mul_of_square_covariance h2 f.toAddMonoidHom hsq

theorem additive_subgroup_square_stable_scalar (h2 : (2:K)≠0)
    (H : AddSubgroup K) (hsq : ∀ t x : K,x∈H → t^2*x∈H)
    (a : K) (ha : a∈H) (t : K) : t*a∈H := by
  have h := H.sub_mem (hsq ((t+1)/2) a ha) (hsq ((t-1)/2) a ha)
  rw [←sub_mul,difference_of_two_squares h2] at h
  exact h

theorem additive_subgroup_square_stable_eq_top (h2 : (2:K)≠0)
    (H : AddSubgroup K) (hsq : ∀ t x : K,x∈H → t^2*x∈H)
    (a : K) (ha : a∈H) (hne : a≠0) : H=⊤ := by
  apply top_unique
  intro x _
  have h := additive_subgroup_square_stable_scalar h2 H hsq a ha (x/a)
  rwa [div_mul_cancel₀ x hne] at h

end SymmetricSubgroupAsymptotics.CFSGSquareScalarRigidity
