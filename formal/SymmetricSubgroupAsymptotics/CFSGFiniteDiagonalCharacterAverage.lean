import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Equiv.Basic

/-! A nontrivial finite scalar character has zero sum. Consequently a
finite diagonal action with no trivial coordinate character has zero
orbit average over every field, including characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFiniteDiagonalCharacterAverage

theorem character_sum_eq_zero {T K : Type*} [Group T] [Fintype T] [Field K]
    (chi : T→*Kˣ) (hchi : ∃a : T,chi a≠1) :
    ∑t : T,(chi t : K)=0 := by
  obtain ⟨a,ha⟩ := hchi
  have hval : (chi a : K)≠1 := fun he=>ha (Units.ext he)
  let e : T≃T := ⟨fun t=>a*t,fun t=>a⁻¹*t,inv_mul_cancel_left a,mul_inv_cancel_left a⟩
  have he : (chi a : K)*(∑t : T,(chi t : K))=∑t : T,(chi t : K) := by
    calc
      _=∑t : T,(chi a : K)*(chi t : K) := Finset.mul_sum _ _ _
      _=∑t : T,(chi (a*t) : K) := by
        apply Finset.sum_congr rfl
        intro t _
        simp only [map_mul,Units.val_mul]
      _=_ := Equiv.sum_comp e (fun t : T=>(chi t : K))
  have hz : ((chi a : K)-1)*(∑t : T,(chi t : K))=0 := by
    rw [sub_mul,one_mul,he,sub_self]
  rcases mul_eq_zero.mp hz with hzero|hzero
  · exact False.elim (hval (sub_eq_zero.mp hzero))
  · exact hzero

theorem diagonal_orbit_sum_eq_zero {I T K : Type*}
    [Group T] [Fintype T] [Field K]
    (chi : I→(T→*Kˣ)) (hchi : ∀i : I,∃a : T,chi i a≠1) (x : I→K) :
    (∑t : T,fun i=>(chi i t : K)*x i)=0 := by
  funext i
  simp only [Finset.sum_apply,Pi.zero_apply]
  rw [←Finset.sum_mul,character_sum_eq_zero (chi i) (hchi i),zero_mul]

end SymmetricSubgroupAsymptotics.CFSGFiniteDiagonalCharacterAverage
