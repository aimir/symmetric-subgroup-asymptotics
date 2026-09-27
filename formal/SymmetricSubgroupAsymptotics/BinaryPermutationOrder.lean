import Mathlib.GroupTheory.Sylow
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Nat.Choose.Factorization

/-! Exact Sylow order on a power-of-two point set, and the resulting
order bound for every actual binary permutation subgroup. Transitivity
is not needed. The factorial valuation is derived by its exact doubling
recurrence; no catalogue order is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem binary_power_factorial_valuation (k : ℕ) :
    (Nat.factorial (2^k)).factorization 2 = 2^k-1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Nat.factorization_factorial_mul Nat.prime_two, ih]
    have hp : 0 < 2^k := pow_pos (by decide) _
    omega

theorem binary_sylow_permutation_card {X : Type*} [Finite X]
    (k : ℕ) (hdegree : Nat.card X = 2^k) (P : Sylow 2 (Equiv.Perm X)) :
    Nat.card P = 2^(2^k-1) := by
  rw [P.card_eq_multiplicity, Nat.card_perm, hdegree, binary_power_factorial_valuation]

theorem binary_permutation_card_le {X : Type*} [Finite X]
    (k : ℕ) (hdegree : Nat.card X = 2^k)
    (U : Subgroup (Equiv.Perm X)) (hU : IsPGroup 2 U) :
    Nat.card U ≤ 2^(2^k-1) := by
  obtain ⟨P, hUP⟩ := hU.exists_le_sylow
  calc
    Nat.card U ≤ Nat.card P := Nat.card_le_card_of_injective
      (Subgroup.inclusion hUP) (Subgroup.inclusion_injective hUP)
    _ = _ := binary_sylow_permutation_card k hdegree P

end SymmetricSubgroupAsymptotics
