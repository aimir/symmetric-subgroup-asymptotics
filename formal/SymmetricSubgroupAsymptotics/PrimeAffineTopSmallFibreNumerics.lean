import SymmetricSubgroupAsymptotics.RankOneSharpOrderCubeNumerics

/-! Uniform small-fibre arithmetic for the actual prime-degree affine
class budget. The unsigned reserve handles the binary degree-five end. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.PrimeAffineTopSmallFibreNumerics

theorem binary_degree_tail (n : ℕ) (hn : 7 ≤ n) :
    (2^n*n)^3 ≤ 5^(2*n-1) := by
  induction n,hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    have hp : (n+1)^3 ≤ 2*n^3 :=
      RankOneSharpOrderCubeNumerics.polynomial_step 2 3 7 n (by decide) hn (by decide)
    calc
      _ = 8*(2^n)^3*(n+1)^3 := by rw [pow_succ]; ring
      _ ≤ 8*(2^n)^3*(2*n^3) := Nat.mul_le_mul_left _ hp
      _ = 16*(2^n*n)^3 := by ring
      _ ≤ 16*5^(2*n-1) := Nat.mul_le_mul_left _ ih
      _ ≤ 25*5^(2*n-1) := Nat.mul_le_mul_right _ (by decide : (16:ℕ) ≤ 25)
      _ = 5^(2*(n+1)-1) := by
        rw [show 2*(n+1)-1=(2*n-1)+2 by omega,pow_add]
        ring

theorem ternary_degree_tail (n : ℕ) (hn : 5 ≤ n) :
    (3^n*n)^3 ≤ 5^(3*n-1) := by
  induction n,hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    have hp : (n+1)^3 ≤ 2*n^3 :=
      RankOneSharpOrderCubeNumerics.polynomial_step 2 3 5 n (by decide) hn (by decide)
    calc
      _ = 27*(3^n)^3*(n+1)^3 := by rw [pow_succ]; ring
      _ ≤ 27*(3^n)^3*(2*n^3) := Nat.mul_le_mul_left _ hp
      _ = 54*(3^n*n)^3 := by ring
      _ ≤ 54*5^(3*n-1) := Nat.mul_le_mul_left _ ih
      _ ≤ 125*5^(3*n-1) := Nat.mul_le_mul_right _ (by decide : (54:ℕ) ≤ 125)
      _ = 5^(3*(n+1)-1) := by
        rw [show 3*(n+1)-1=(3*n-1)+3 by omega,pow_add]
        ring

theorem binary_unsigned_five : (12*2^(5-2))^3 ≤ 5^(2*5-1) := by
  decide +kernel

end SymmetricSubgroupAsymptotics.PrimeAffineTopSmallFibreNumerics
