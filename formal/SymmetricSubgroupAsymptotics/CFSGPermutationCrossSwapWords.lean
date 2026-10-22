import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Group

/-! Symbolic cross-swap relations on four distinct original points.
An involution interchanging the inner pair and fixing the outer pair has
dihedral product exponent four with the two crossing transpositions.
All identities are proved by the five possible point locations, without
enumerating the ambient symmetric group. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGPermutationCrossSwapWords
open Equiv Equiv.Perm

variable {X : Type*} [DecidableEq X]

def doubleSwap (a b c d : X) : Equiv.Perm X := Equiv.swap a b * Equiv.swap c d

theorem doubleSwap_square (a b c d : X)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    doubleSwap a b c d ^ 2 = 1 := by
  ext x
  by_cases hxa : x = a
  · subst x
    simp [doubleSwap, pow_two, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      hac, had, hbc, hbd, Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd]
  by_cases hxb : x = b
  · subst x
    simp [doubleSwap, pow_two, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      hac, had, hbc, hbd, Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd]
  by_cases hxc : x = c
  · subst x
    simp [doubleSwap, pow_two, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      hac, had, hbc, hbd, Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd]
  by_cases hxd : x = d
  · subst x
    simp [doubleSwap, pow_two, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      hac, had, hbc, hbd, Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd]
  simp [doubleSwap, pow_two, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hxa, hxb, hxc, hxd]

theorem cross_switch_mul_square (u v a b : X)
    (huv : u ≠ v) (hua : u ≠ a) (hub : u ≠ b)
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b) :
    (doubleSwap v a u b * doubleSwap u a v b) ^ 2 = 1 := by
  ext x
  by_cases hxu : x = u
  · subst x
    simp [doubleSwap, pow_two, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      huv, hua, hub, hva, hvb, hab,
      Ne.symm huv, Ne.symm hua, Ne.symm hub, Ne.symm hva, Ne.symm hvb, Ne.symm hab]
  by_cases hxv : x = v
  · subst x
    simp [doubleSwap, pow_two, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      huv, hua, hub, hva, hvb, hab,
      Ne.symm huv, Ne.symm hua, Ne.symm hub, Ne.symm hva, Ne.symm hvb, Ne.symm hab]
  by_cases hxa : x = a
  · subst x
    simp [doubleSwap, pow_two, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      huv, hua, hub, hva, hvb, hab,
      Ne.symm huv, Ne.symm hua, Ne.symm hub, Ne.symm hva, Ne.symm hvb, Ne.symm hab]
  by_cases hxb : x = b
  · subst x
    simp [doubleSwap, pow_two, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      huv, hua, hub, hva, hvb, hab,
      Ne.symm huv, Ne.symm hua, Ne.symm hub, Ne.symm hva, Ne.symm hvb, Ne.symm hab]
  simp [doubleSwap, pow_two, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hxu, hxv, hxa, hxb]

theorem involution_cross_rotation_pow_four (p : Equiv.Perm X) (u v a b : X)
    (hp : p ^ 2 = 1) (hpu : p u = v) (hpv : p v = u)
    (hpa : p a = a) (hpb : p b = b)
    (huv : u ≠ v) (hua : u ≠ a) (hub : u ≠ b)
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b) :
    (p * doubleSwap u a v b) ^ 4 = 1 := by
  have hpi : p⁻¹ = p := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hp)
  have hc : p * doubleSwap u a v b * p⁻¹ = doubleSwap v a u b := by
    change (MulAut.conj p) (Equiv.swap u a * Equiv.swap v b) = _
    rw [map_mul]
    change (p * Equiv.swap u a * p⁻¹) * (p * Equiv.swap v b * p⁻¹) = _
    rw [← Equiv.swap_apply_apply, ← Equiv.swap_apply_apply, hpu, hpv, hpa, hpb]
    rfl
  have hs : (p * doubleSwap u a v b) ^ 2 =
      doubleSwap v a u b * doubleSwap u a v b := by
    calc
      (p * doubleSwap u a v b) ^ 2 =
          (p * doubleSwap u a v b * p⁻¹) * doubleSwap u a v b := by
        rw [hpi, pow_two]
        group
      _ = _ := by rw [hc]
  rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hs]
  exact cross_switch_mul_square u v a b huv hua hub hva hvb hab

end SymmetricSubgroupAsymptotics.CFSGPermutationCrossSwapWords
