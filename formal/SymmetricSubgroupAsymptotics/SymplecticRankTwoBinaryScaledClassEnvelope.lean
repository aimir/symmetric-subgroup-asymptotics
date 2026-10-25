import SymmetricSubgroupAsymptotics.QuadraticExponentialPolynomialTail

/-! One quadratic-exponential polynomial tail pays the literal binary
rank-two class-equation envelope from field size8. The existing actual
q^2 index and outer≤q^2 bound suffice; no rounded q^3 index is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.SymplecticRankTwoBinaryScaledClassEnvelope

theorem scaled_class_equation_budget (q : ℕ) (hq : 8 ≤ q) :
    25*((q^10/q^2+1)*q^2)^3 ≤ 3^(q^2) := by
  have hqpos : 0 < q := by omega
  have hdiv : q^10/q^2=q^8 := by
    rw [show q^10=q^8*q^2 by ring,Nat.mul_div_cancel _ (pow_pos hqpos _)]
  have hadd : q^8+1 ≤ 2*q^8 := by
    have hp : 1 ≤ q^8 := Nat.one_le_pow _ _ (by omega : 1 ≤ q)
    omega
  have hc : (q^10/q^2+1)*q^2 ≤ 2*q^10 := by
    rw [hdiv]
    exact (Nat.mul_le_mul_right _ hadd).trans_eq (by ring)
  calc
    _ ≤ 25*(2*q^10)^3 := Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hc 3)
    _ = 200*q^30 := by ring
    _ ≤ 3^(q^2) := by
      simpa only [one_mul] using
        QuadraticExponentialPolynomialTail.polynomial_tail 200 30 3 1 8
          (by decide) (by decide) (by decide +kernel) (by decide +kernel) q hq

end SymmetricSubgroupAsymptotics.SymplecticRankTwoBinaryScaledClassEnvelope
