import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Literal rotation and reflection on a cycle of length `4*k+1`.
Both permutations are even. The reflection fixes exactly one point and
inverts the odd-order rotation. No primality of the cycle length is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingCyclicReflection

abbrev Cycle (k : ℕ) := ZMod (4 * k + 1)

instance cycle_neZero (k : ℕ) : NeZero (4 * k + 1) := ⟨by omega⟩

def rotation (k : ℕ) : Equiv.Perm (Cycle k) where
  toFun x := x + 1
  invFun x := x - 1
  left_inv x := by ring
  right_inv x := by ring

def reflection (k : ℕ) : Equiv.Perm (Cycle k) where
  toFun x := 3 - x
  invFun x := 3 - x
  left_inv x := by ring
  right_inv x := by ring

@[simp] theorem rotation_apply (k : ℕ) (x : Cycle k) : rotation k x = x + 1 := rfl
@[simp] theorem rotation_inv_apply (k : ℕ) (x : Cycle k) :
    (rotation k)⁻¹ x = x - 1 := rfl
@[simp] theorem reflection_apply (k : ℕ) (x : Cycle k) : reflection k x = 3 - x := rfl

theorem rotation_pow_apply (k j : ℕ) (x : Cycle k) :
    (rotation k ^ j) x = x + j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, rotation_apply, Nat.cast_succ]
      ring

theorem rotation_odd_power (k : ℕ) : rotation k ^ (4 * k + 1) = 1 := by
  apply Equiv.ext
  intro x
  rw [rotation_pow_apply, ZMod.natCast_self, add_zero, Equiv.Perm.one_apply]

theorem reflection_square (k : ℕ) : reflection k ^ 2 = 1 := by
  apply Equiv.ext
  intro x
  change 3 - (3 - x) = x
  ring

theorem reflection_inverts (k : ℕ) :
    reflection k * rotation k * (reflection k)⁻¹ = (rotation k)⁻¹ := by
  apply Equiv.ext
  intro x
  change 3 - ((3 - x) + 1) = x - 1
  ring

theorem two_isUnit (k : ℕ) : IsUnit (2 : Cycle k) := by
  apply (ZMod.isUnit_iff_coprime 2 (4 * k + 1)).mpr
  exact Nat.coprime_two_left.mpr ⟨2 * k, by omega⟩

theorem reflection_fixed_iff (k : ℕ) (x : Cycle k) :
    reflection k x = x ↔ (2 : Cycle k) * x = 3 := by
  change 3 - x = x ↔ 2 * x = 3
  constructor <;> intro h <;> linear_combination -h

theorem reflection_fixed_card (k : ℕ) :
    Fintype.card (Function.fixedPoints (reflection k)) = 1 := by
  obtain ⟨c, hc⟩ := (IsUnit.isUnit_iff_mulLeft_bijective.mp (two_isUnit k)).2 3
  let z : Function.fixedPoints (reflection k) :=
    ⟨c, (reflection_fixed_iff k c).mpr hc⟩
  letI : Unique (Function.fixedPoints (reflection k)) := {
    default := z
    uniq := by
      intro x
      apply Subtype.ext
      exact (two_isUnit k).mul_right_injective
        (((reflection_fixed_iff k x.val).mp x.property).trans hc.symm) }
  exact Fintype.card_unique

theorem reflection_even (k : ℕ) : Equiv.Perm.sign (reflection k) = 1 := by
  rw [Equiv.Perm.sign_of_pow_two_eq_one (reflection_square k), reflection_fixed_card]
  simp only [ZMod.card]
  rw [show (4 * k + 1 - 1) / 2 = 2 * k by omega, pow_mul]
  norm_num

theorem rotation_even (k : ℕ) : Equiv.Perm.sign (rotation k) = 1 := by
  have h := congrArg Equiv.Perm.sign (rotation_odd_power k)
  rw [map_pow, map_one] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign (rotation k)) with hs | hs
  · exact hs
  · rw [hs, pow_add, pow_mul] at h
    have hfour : (-1 : ℤˣ) ^ 4 = 1 := by decide
    have hne : (-1 : ℤˣ) ≠ 1 := by decide
    exact False.elim (hne (by simpa only [hfour, one_pow, pow_one, one_mul] using h))

end SymmetricSubgroupAsymptotics.CFSGAlternatingCyclicReflection
