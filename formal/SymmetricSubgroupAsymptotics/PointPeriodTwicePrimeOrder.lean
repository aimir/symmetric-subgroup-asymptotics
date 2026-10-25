import SymmetricSubgroupAsymptotics.PermutationTwicePrimeOrderDegree
import Mathlib.GroupTheory.GroupAction.Period
import Mathlib.Data.Nat.GCD.Prime

/-! A return at twice an odd prime together with nonreturns at the two
prime factors fixes the exact point period, hence divides the order of
the SAME acting element. No equality of the whole linear operator with
one is needed. An injective permutation action then retains this element
order and pays the sum of its required cycle supports. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PointPeriodTwicePrimeOrder

variable {G V : Type*} [Group G] [MulAction G V]

theorem period_eq_twice_prime (g : G) (v : V) (p : ℕ) (hp : p.Prime)
    (hcop : Nat.Coprime 2 p) (hreturn : g^(2*p) • v = v)
    (htwo : g^2 • v ≠ v) (hprime : g^p • v ≠ v) : MulAction.period g v = 2*p := by
  have hd : MulAction.period g v ∣ 2*p :=
    MulAction.pow_smul_eq_iff_period_dvd.mp hreturn
  have h2 : 2 ∣ MulAction.period g v := by
    by_contra hn
    have hc : Nat.Coprime (MulAction.period g v) 2 :=
      (Nat.prime_two.coprime_iff_not_dvd.mpr hn).symm
    exact hprime (MulAction.pow_smul_eq_iff_period_dvd.mpr
      (hc.dvd_of_dvd_mul_left hd))
  have hpdiv : p ∣ MulAction.period g v := by
    by_contra hn
    have hc : Nat.Coprime (MulAction.period g v) p :=
      (hp.coprime_iff_not_dvd.mpr hn).symm
    exact htwo (MulAction.pow_smul_eq_iff_period_dvd.mpr
      (hc.dvd_of_dvd_mul_right hd))
  exact Nat.dvd_antisymm hd (hcop.mul_dvd_of_dvd_of_dvd h2 hpdiv)

theorem twice_prime_dvd_orderOf (g : G) (v : V) (p : ℕ) (hp : p.Prime)
    (hcop : Nat.Coprime 2 p) (hreturn : g^(2*p) • v = v)
    (htwo : g^2 • v ≠ v) (hprime : g^p • v ≠ v) : 2*p ∣ orderOf g := by
  rw [←period_eq_twice_prime g v p hp hcop hreturn htwo hprime]
  exact MulAction.period_dvd_orderOf g v

theorem fourteen_dvd_orderOf (g : G) (v : V) (hreturn : g^14 • v = v)
    (htwo : g^2 • v ≠ v) (hseven : g^7 • v ≠ v) : 14 ∣ orderOf g :=
  twice_prime_dvd_orderOf g v 7 (by decide) (by decide) hreturn htwo hseven

theorem nine_le_card_of_faithful_permutation_action {X : Type*} [Finite X]
    (f : G →* Equiv.Perm X) (hf : Function.Injective f)
    (g : G) (v : V) (hreturn : g^14 • v = v)
    (htwo : g^2 • v ≠ v) (hseven : g^7 • v ≠ v) : 9 ≤ Nat.card X := by
  apply PermutationTwicePrimeOrderDegree.nine_le_card_of_fourteen_dvd_orderOf (f g)
  rw [orderOf_injective f hf g]
  exact fourteen_dvd_orderOf g v hreturn htwo hseven

end SymmetricSubgroupAsymptotics.PointPeriodTwicePrimeOrder
