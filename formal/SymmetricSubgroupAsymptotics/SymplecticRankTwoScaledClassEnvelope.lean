import SymmetricSubgroupAsymptotics.QuadraticExponentialPolynomialTail

/-! The exact first odd-field seed and one quadratic-exponential tail
pay the rank-two class-equation envelope at the actual prime-times-
field-square index. No list of fields or actions is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.SymplecticRankTwoScaledClassEnvelope

theorem scaled_class_equation_budget (q : ℕ) (hq : 3 ≤ q) :
    25*((q^10/(3*q^2)+1)*q)^3 ≤ 3^(3*q^2) := by
  by_cases hq3 : q=3
  · subst q
    decide +kernel
  · have hq4 : 4 ≤ q := by omega
    have hqpos : 0 < q := by omega
    have hdiv : q^10/(3*q^2) ≤ q^8 := by
      calc
        _ ≤ q^10/q^2 := Nat.div_le_div_left
          (Nat.le_mul_of_pos_left _ (by decide : 0 < (3:ℕ))) (pow_pos hqpos _)
        _ = q^8 := by
          rw [show q^10=q^8*q^2 by ring,Nat.mul_div_cancel _ (pow_pos hqpos _)]
    have hadd : q^8+1 ≤ q^9 := by
      have hp : 1 ≤ q^8 := Nat.one_le_pow _ _ (by omega : 1 ≤ q)
      have hh := Nat.mul_le_mul_right (q^8) (by omega : 2 ≤ q)
      rw [show q^9=q*q^8 from pow_succ' q 8]
      omega
    have hc : (q^10/(3*q^2)+1)*q ≤ q^10 := by
      calc
        _ ≤ (q^8+1)*q := Nat.mul_le_mul_right _ (Nat.add_le_add_right hdiv 1)
        _ ≤ q^9*q := Nat.mul_le_mul_right _ hadd
        _ = q^10 := by ring
    have hp := Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hc 3)
    have he : (q^10)^3=q^30 := by rw [←pow_mul]
    rw [he] at hp
    exact hp.trans (QuadraticExponentialPolynomialTail.polynomial_tail 25 30 3 3 4
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) q hq4)

end SymmetricSubgroupAsymptotics.SymplecticRankTwoScaledClassEnvelope
