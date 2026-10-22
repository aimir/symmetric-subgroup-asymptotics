import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! Transpositions in an actual permutation two-group form a matching:
two different partners of one point would produce an element of order
three. A fixed-point-free pairing whose every pair flip lies in the
two-group is therefore preserved by its full normalizer. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGTwoGroupTranspositionMatching
open Equiv Equiv.Perm

variable {X : Type*} [Finite X] [DecidableEq X]

theorem swap_partner_unique (P : Subgroup (Equiv.Perm X)) (hP : IsPGroup 2 P)
    {x y z : X} (hxy : x ≠ y) (hxz : x ≠ z)
    (hxyP : Equiv.swap x y ∈ P) (hxzP : Equiv.swap x z ∈ P) : y = z := by
  letI : Fintype X := Fintype.ofFinite X
  by_contra hyz
  let a : P := ⟨Equiv.swap x y * Equiv.swap x z, P.mul_mem hxyP hxzP⟩
  have ha : orderOf a = 3 := by
    rw [Subgroup.orderOf_mk]
    exact (isThreeCycle_swap_mul_swap_same hxy hxz hyz).orderOf
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) a
  have hd : 3 ∣ 2 ^ k := by rw [← hk, ha]
  exact (by decide : (3 : ℕ) ≠ 2)
    (Nat.prime_eq_prime_of_dvd_pow Nat.prime_three Nat.prime_two hd)

theorem normalizer_preserves_pairing
    (P : Subgroup (Equiv.Perm X)) (hP : IsPGroup 2 P)
    (pairing : Equiv.Perm X) (hfree : ∀ x : X, pairing x ≠ x)
    (hflip : ∀ x : X, Equiv.swap x (pairing x) ∈ P)
    (g : Equiv.Perm X) (hg : g ∈ Subgroup.normalizer (P : Set (Equiv.Perm X)))
    (x : X) : g (pairing x) = pairing (g x) := by
  have hm : g * Equiv.swap x (pairing x) * g⁻¹ ∈ P :=
    ((Subgroup.mem_normalizer_iff.mp hg) (Equiv.swap x (pairing x))).mp (hflip x)
  rw [Equiv.mul_swap_eq_swap_mul, mul_inv_cancel_right] at hm
  exact swap_partner_unique P hP
    (fun h => hfree x (g.injective h).symm) (Ne.symm (hfree (g x))) hm (hflip (g x))

end SymmetricSubgroupAsymptotics.CFSGTwoGroupTranspositionMatching
