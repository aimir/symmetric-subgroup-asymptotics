import SymmetricSubgroupAsymptotics.RankOneSharpOrderCubeNumerics

/-! A polynomial is absorbed by a quadratic exponential from one
ratio comparison and one seed. The two scaled degree-sixty corollaries
serve actual prime-times-square and endpoint index bounds. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.QuadraticExponentialPolynomialTail

theorem polynomial_tail (c d b a n₀ : ℕ) (hn₀ : 0 < n₀) (hb : 0 < b)
    (hratio : (n₀+1)^d ≤ b^(a*(2*n₀+1))*n₀^d)
    (hbase : c*n₀^d ≤ b^(a*n₀^2)) (n : ℕ) (hn : n₀ ≤ n) :
    c*n^d ≤ b^(a*n^2) := by
  induction n,hn using Nat.le_induction with
  | base => exact hbase
  | succ n hn ih =>
    have hs := RankOneSharpOrderCubeNumerics.polynomial_step
      (b^(a*(2*n₀+1))) d n₀ n hn₀ hn hratio
    have he : a*(2*n₀+1)+a*n^2 ≤ a*(n+1)^2 := by
      calc
        a*(2*n₀+1)+a*n^2 = a*((2*n₀+1)+n^2) := by ring
        _ ≤ a*(n+1)^2 := Nat.mul_le_mul_left a (by nlinarith)
    calc
      c*(n+1)^d ≤ c*(b^(a*(2*n₀+1))*n^d) := Nat.mul_le_mul_left c hs
      _ = b^(a*(2*n₀+1))*(c*n^d) := by ring
      _ ≤ b^(a*(2*n₀+1))*b^(a*n^2) := Nat.mul_le_mul_left _ ih
      _ = b^(a*(2*n₀+1)+a*n^2) := (pow_add _ _ _).symm
      _ ≤ b^(a*(n+1)^2) := Nat.pow_le_pow_right hb he

theorem scaled_power_sixty_le_three_five_square (q : ℕ) (hq : 5 ≤ q) :
    25*q^60 ≤ 3^(5*q^2) :=
  polynomial_tail 25 60 3 5 5 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) q hq

theorem scaled_power_sixty_le_three_two_square (q : ℕ) (hq : 8 ≤ q) :
    25*q^60 ≤ 3^(2*q^2) :=
  polynomial_tail 25 60 3 2 8 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) q hq

end SymmetricSubgroupAsymptotics.QuadraticExponentialPolynomialTail
