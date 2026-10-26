import SymmetricSubgroupAsymptotics.RankOneSharpOrderCubeNumerics

/-! Polynomial-order affine tops pay the original small-fibre exponent
uniformly. The cutoffs are degree49 for order n^4 and degree64 for n^5;
no prime-power or permutation group is enumerated. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.AffineTopLowDimensionSmallFibreNumerics

private theorem polynomial_budget (n₀ d : ℕ) (hn₀ : 0<n₀)
    (hbase : 8^n₀*n₀^d ≤ 5^(2*n₀-1))
    (hratio : (n₀+1)^d ≤ 2*n₀^d)
    (n : ℕ) (hn : n₀ ≤ n) : 8^n*n^d ≤ 5^(2*n-1) := by
  induction n,hn using Nat.le_induction with
  | base => exact hbase
  | succ n hn ih =>
    have hp : (n+1)^d ≤ 2*n^d :=
      RankOneSharpOrderCubeNumerics.polynomial_step 2 d n₀ n hn₀ hn hratio
    calc
      _ = 8*8^n*(n+1)^d := by rw [pow_succ]; ring
      _ ≤ 8*8^n*(2*n^d) := Nat.mul_le_mul_left _ hp
      _ = 16*(8^n*n^d) := by ring
      _ ≤ 16*5^(2*n-1) := Nat.mul_le_mul_left _ ih
      _ ≤ 25*5^(2*n-1) := Nat.mul_le_mul_right _ (by decide : (16:ℕ) ≤ 25)
      _ = 5^(2*(n+1)-1) := by
        rw [show 2*(n+1)-1=(2*n-1)+2 by omega,pow_add]
        ring

private theorem binary_of_order (n a d : ℕ) (ha : a ≤ n^d)
    (hpoly : 8^n*n^(d*3) ≤ 5^(2*n-1)) : (2^n*a)^3 ≤ 5^(2*n-1) := by
  calc
    _ ≤ (2^n*n^d)^3 := Nat.pow_le_pow_left (Nat.mul_le_mul_left _ ha) 3
    _ = 8^n*n^(d*3) := by
      rw [mul_pow,←pow_mul,←pow_mul,Nat.mul_comm n 3,pow_mul]
      norm_num
    _ ≤ _ := hpoly

private theorem ternary_of_binary (n a : ℕ) (hn : 1 ≤ n)
    (hbinary : (2^n*a)^3 ≤ 5^(2*n-1)) : (3^n*a)^3 ≤ 5^(3*n-1) := by
  have hthree : ((3:ℕ)^n)^3=27^n := by
    rw [←pow_mul,Nat.mul_comm n 3,pow_mul]
    norm_num
  have htwo : ((2:ℕ)^n)^3=8^n := by
    rw [←pow_mul,Nat.mul_comm n 3,pow_mul]
    norm_num
  have h27 : (3^n)^3 ≤ 5^n*(2^n)^3 := by
    rw [hthree,htwo,←mul_pow]
    exact Nat.pow_le_pow_left (by decide : (27:ℕ) ≤ 5*8) n
  calc
    _ = (3^n)^3*a^3 := mul_pow _ _ _
    _ ≤ (5^n*(2^n)^3)*a^3 := Nat.mul_le_mul_right _ h27
    _ = 5^n*(2^n*a)^3 := by rw [mul_pow]; ring
    _ ≤ 5^n*5^(2*n-1) := Nat.mul_le_mul_left _ hbinary
    _ = 5^(3*n-1) := by rw [←pow_add]; congr 1; omega

theorem binary_fourth_order (n a : ℕ) (hn : 49 ≤ n) (ha : a ≤ n^4) :
    (2^n*a)^3 ≤ 5^(2*n-1) :=
  binary_of_order n a 4 ha
    (polynomial_budget 49 12 (by decide) (by decide +kernel) (by decide +kernel) n hn)

theorem binary_fifth_order (n a : ℕ) (hn : 64 ≤ n) (ha : a ≤ n^5) :
    (2^n*a)^3 ≤ 5^(2*n-1) :=
  binary_of_order n a 5 ha
    (polynomial_budget 64 15 (by decide) (by decide +kernel) (by decide +kernel) n hn)

theorem ternary_fourth_order (n a : ℕ) (hn : 49 ≤ n) (ha : a ≤ n^4) :
    (3^n*a)^3 ≤ 5^(3*n-1) :=
  ternary_of_binary n a (by omega) (binary_fourth_order n a hn ha)

theorem ternary_fifth_order (n a : ℕ) (hn : 64 ≤ n) (ha : a ≤ n^5) :
    (3^n*a)^3 ≤ 5^(3*n-1) :=
  ternary_of_binary n a (by omega) (binary_fifth_order n a hn ha)

end SymmetricSubgroupAsymptotics.AffineTopLowDimensionSmallFibreNumerics
