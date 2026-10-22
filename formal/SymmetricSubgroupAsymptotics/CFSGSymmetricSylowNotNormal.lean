import SymmetricSubgroupAsymptotics.CFSGSymmetricSylowSelfNormalizer
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! A symmetric Sylow two-subgroup on at least three points is not
normal: self-normalization would make it the whole symmetric group,
which contains an actual element of order three. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGSymmetricSylowNotNormal
open Equiv Perm

theorem not_isPGroup {X : Type*} [Fintype X] [DecidableEq X]
    (hsize : 3 ≤ Nat.card X) : ¬ IsPGroup 2 (Perm X) := by
  intro h
  have hthree : 2 < (Set.univ : Set X).ncard := by simpa using hsize
  rw [Set.two_lt_ncard_iff] at hthree
  obtain ⟨a, b, c, _, _, _, hab, hac, hbc⟩ := hthree
  let u : Perm X := Equiv.swap a b * Equiv.swap a c
  have hu : IsThreeCycle u := isThreeCycle_swap_mul_swap_same hab hac hbc
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h) u
  have hd : 3 ∣ 2 ^ k := by rw [← hk, hu.orderOf]
  exact (by decide : (3 : ℕ) ≠ 2)
    (Nat.prime_eq_prime_of_dvd_pow Nat.prime_three Nat.prime_two hd)

theorem not_normal {X : Type*} [Fintype X] [DecidableEq X]
    (hsize : 3 ≤ Nat.card X) (Q : Sylow 2 (Perm X)) :
    ¬ (Q : Subgroup (Perm X)).Normal := by
  intro hN
  have htop : Subgroup.normalizer (Q : Set (Perm X)) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr hN
  rw [CFSGSymmetricSylowSelfNormalizer.normalizer_eq_self Q] at htop
  apply not_isPGroup hsize
  have hp : IsPGroup 2 (⊤ : Subgroup (Perm X)) := by
    rw [← htop]
    exact Q.isPGroup'
  exact hp.of_equiv Subgroup.topEquiv

end SymmetricSubgroupAsymptotics.CFSGSymmetricSylowNotNormal
