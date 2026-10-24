import SymmetricSubgroupAsymptotics.RankOneSharpOrderCubeNumerics
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsParameters

/-! A uniform scalar budget for a prospective actual middle-pairing
index. This is a numerical lemma only: no G2 pairing or index theorem
is inferred from it. One quadratic-degree tail covers every q>=6;
the prime field of order five is an exact scalar seed. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.GTwoMiddlePairingClassNumerics

theorem quadratic_index_budget (q : ℕ) (hq : 6 ≤ q) :
    q^60 ≤ 5^(2*q^2-1) := by
  have hq2 : 36 ≤ q^2 := Nat.pow_le_pow_left hq 2
  have ht := RankOneSharpOrderCubeNumerics.polynomial_tail 1 30 25 36
    (by decide) (by decide +kernel) (by decide +kernel) (q^2) hq2
  calc
    q^60 = (q^2)^30 := by rw [←pow_mul]
    _ ≤ 25^(q^2-1) := by simpa only [one_mul] using ht
    _ = 5^(2*(q^2-1)) := by rw [show (25:ℕ)=5^2 by decide,←pow_mul]
    _ ≤ 5^(2*q^2-1) := Nat.pow_le_pow_right (by decide) (by omega)

theorem primePower_middle_index_budget (q : CFSG.PrimePower) (hq : 5 ≤ q.order) :
    q.order^60 ≤ 5^(q.prime*q.order^2-1) := by
  by_cases hf : q.order=5
  · have hd : q.prime ∣ 5 := by
      rw [←hf]
      change q.prime ∣ q.prime^q.exponent
      exact dvd_pow_self _ q.exponent_pos.ne'
    have hp : q.prime=5 := (Nat.prime_dvd_prime_iff_eq q.prime_isPrime (by decide)).mp hd
    rw [hf,hp]
    exact Nat.pow_le_pow_right (by decide) (by decide)
  · exact (quadratic_index_budget q.order (by omega)).trans
      (Nat.pow_le_pow_right (by decide)
        (Nat.sub_le_sub_right (Nat.mul_le_mul_right _ q.prime_isPrime.two_le) 1))

end SymmetricSubgroupAsymptotics.GTwoMiddlePairingClassNumerics
