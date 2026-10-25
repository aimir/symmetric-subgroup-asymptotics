import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Subgroup.Basic

/-! Recover commuting factors of an actual product from coprime PERIODS.
Exact element orders, finite ambient groups and supplied generator bounds
are unnecessary. The proof powers inside the original subgroup. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CommutingCoprimePeriodProductGeneration
variable {G : Type*} [Group G]

theorem left_mem (H : Subgroup G) (x y : G) (m n : ℕ)
    (hcop : m.Coprime n) (hcomm : Commute x y)
    (hx : x^m = 1) (hy : y^n = 1) (hprod : x*y ∈ H) : x ∈ H := by
  have hp : n.Coprime (orderOf x) :=
    Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hx) hcop.symm
  obtain ⟨k,hk⟩ := exists_pow_eq_self_of_coprime (x := x) hp
  have hpower : (x*y)^n = x^n := by rw [hcomm.mul_pow,hy,mul_one]
  have hn : x^n ∈ H := by simpa only [hpower] using H.pow_mem hprod n
  have hh := H.pow_mem hn k
  rwa [hk] at hh

theorem right_mem (H : Subgroup G) (x y : G) (m n : ℕ)
    (hcop : m.Coprime n) (hcomm : Commute x y)
    (hx : x^m = 1) (hy : y^n = 1) (hprod : x*y ∈ H) : y ∈ H := by
  have hswap : y*x ∈ H := hcomm.eq ▸ hprod
  exact left_mem H y x n m hcop.symm hcomm.symm hy hx hswap

end SymmetricSubgroupAsymptotics.CommutingCoprimePeriodProductGeneration
