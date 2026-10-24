import SymmetricSubgroupAsymptotics.CFSGSLTwoProperIndexLower
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.GroupTheory.OrderOfElement

/-! Every proper SL2 subgroup has index at least the characteristic
prime. A nonzero actual upper-root element moves a coset, so its image
is a permutation of order p. Simplicity of SL2 or PSL2 is not required. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSLTwoPrimeIndexLower
open CFSGTypeASLTwoWeyl CFSGSLTwoUpperRoots
variable {K : Type*} [Field K] [Finite K]

theorem prime_le_proper_index (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : Subgroup (SL2 (F := K))) (hH : H ≠ ⊤) : p ≤ H.index := by
  let f := MulAction.toPermHom (SL2 (F := K)) (SL2 (F := K) ⧸ H)
  have hne : f (upper (1 : K)) ≠ 1 := by
    intro h
    obtain ⟨x, hx⟩ := CFSGSLTwoProperIndexLower.exists_moved_coset H hH 1 one_ne_zero
    exact hx (congrArg (fun g : Equiv.Perm (SL2 (F := K) ⧸ H) => g x) h)
  have hu : (upper (1 : K))^p = 1 := by
    change (upperHom (F := K) (Multiplicative.ofAdd 1))^p = 1
    rw [← map_pow]
    have he : (Multiplicative.ofAdd (1 : K))^p = 1 := by
      apply Multiplicative.toAdd.injective
      simp only [toAdd_pow, toAdd_ofAdd, toAdd_one, nsmul_eq_mul, mul_one]
      exact CharP.cast_eq_zero K p
    rw [he, map_one]
  have horder : orderOf (f (upper (1 : K))) = p :=
    orderOf_eq_prime (by rw [← map_pow, hu, map_one]) hne
  have hd : p ∣ Nat.card (Equiv.Perm (SL2 (F := K) ⧸ H)) :=
    horder ▸ orderOf_dvd_natCard (f (upper (1 : K)))
  rw [Nat.card_perm, ← H.index_eq_card] at hd
  exact (Fact.out : p.Prime).dvd_factorial.mp hd

end SymmetricSubgroupAsymptotics.CFSGSLTwoPrimeIndexLower
