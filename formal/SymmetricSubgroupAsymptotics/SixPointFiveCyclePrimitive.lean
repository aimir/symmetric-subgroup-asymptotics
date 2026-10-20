import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Tactic.FinCases

/-! A five-cycle and any element moving its unique fixed point make the
actual six-point subgroup doubly transitive. Only the five-cycle orbit
identity is finite; no generated-group or subgroup enumeration occurs. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SixPointFiveCyclePrimitive

def cycle : Equiv.Perm (Fin 6) where
  toFun := ![1,2,3,4,0,5]
  invFun := ![4,0,1,2,3,5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem cofinite_orbit (i j : Fin 6) (hi : i ≠ 5) (hj : j ≠ 5) :
    ∃ n : Fin 5, (cycle ^ n.val) i = j := by
  revert i j
  decide +kernel

theorem fixed_pow (n : ℕ) : (cycle ^ n) 5 = 5 := by
  induction n with
  | zero => rfl
  | succ n hn => simpa only [pow_succ',Equiv.Perm.mul_apply,hn] using (show cycle 5 = 5 from rfl)

variable (P : Subgroup (Equiv.Perm (Fin 6))) (a b : P)
  (ha : (a : Equiv.Perm (Fin 6)) = cycle)
  (hb : (b : Equiv.Perm (Fin 6)) 5 ≠ 5)

include ha hb in
theorem exists_fixed_image (i : Fin 6) : ∃ g : P, (g : Equiv.Perm (Fin 6)) 5 = i := by
  by_cases hi : i = 5
  · exact ⟨1,hi.symm⟩
  · obtain ⟨n,hn⟩ := cofinite_orbit ((b : Equiv.Perm (Fin 6)) 5) i hb hi
    refine ⟨a ^ n.val * b,?_⟩
    change ((a : Equiv.Perm (Fin 6)) ^ n.val) ((b : Equiv.Perm (Fin 6)) 5) = i
    rwa [ha]

private theorem inverse_ne_fixed (g : P) {x y : Fin 6}
    (hg : (g : Equiv.Perm (Fin 6)) 5 = x) (hy : y ≠ x) :
    (g : Equiv.Perm (Fin 6))⁻¹ y ≠ 5 := by
  intro he
  apply hy
  calc
    y = (g : Equiv.Perm (Fin 6)) ((g : Equiv.Perm (Fin 6))⁻¹ y) :=
      ((g : Equiv.Perm (Fin 6)).apply_symm_apply y).symm
    _ = (g : Equiv.Perm (Fin 6)) 5 := congrArg (g : Equiv.Perm (Fin 6)) he
    _ = x := hg

include ha hb in
theorem two_pretransitive : MulAction.IsMultiplyPretransitive P (Fin 6) 2 := by
  apply MulAction.is_two_pretransitive_iff.mpr
  intro x y u v hxy huv
  obtain ⟨g,hg⟩ := exists_fixed_image P a b ha hb x
  obtain ⟨h,hh⟩ := exists_fixed_image P a b ha hb u
  obtain ⟨n,hn⟩ := cofinite_orbit
    ((g : Equiv.Perm (Fin 6))⁻¹ y) ((h : Equiv.Perm (Fin 6))⁻¹ v)
    (inverse_ne_fixed P g hg hxy.symm) (inverse_ne_fixed P h hh huv.symm)
  refine ⟨h * a ^ n.val * g⁻¹,?_,?_⟩
  · change (h : Equiv.Perm (Fin 6))
      (((a : Equiv.Perm (Fin 6)) ^ n.val) ((g : Equiv.Perm (Fin 6))⁻¹ x)) = u
    have hx : (g : Equiv.Perm (Fin 6))⁻¹ x = 5 := by
      rw [← hg]
      exact (g : Equiv.Perm (Fin 6)).symm_apply_apply 5
    rw [hx,ha,fixed_pow,hh]
  · change (h : Equiv.Perm (Fin 6))
      (((a : Equiv.Perm (Fin 6)) ^ n.val) ((g : Equiv.Perm (Fin 6))⁻¹ y)) = v
    rw [ha,hn]
    exact (h : Equiv.Perm (Fin 6)).apply_symm_apply v

include ha hb in
theorem preprimitive : MulAction.IsPreprimitive P (Fin 6) :=
  MulAction.isPreprimitive_of_is_two_pretransitive (two_pretransitive P a b ha hb)

end SymmetricSubgroupAsymptotics.SixPointFiveCyclePrimitive

end
