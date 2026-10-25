import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate

/-! A uniform small-fibre class budget for an actual quasipolynomial top
order. The order premise is explicit: neither a primitive classification
nor a class-count conclusion is assumed. The binary estimate implies the
ternary estimate with the same top and no independent worst-case choice. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.LargePrimitiveSmallFibreClassNumerics

theorem dyadic_budget (m : ℕ) (hm : 12≤m) :
    3*(m+1)*(4*m+24)+2≤2^m := by
  induction m,hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have hs : 3*(m+1+1)*(4*(m+1)+24)+2≤2*(3*(m+1)*(4*m+24)+2) := by
      nlinarith only [hm,Nat.zero_le (m^2)]
    exact hs.trans ((Nat.mul_le_mul_left 2 ih).trans_eq (by rw [pow_succ];omega))

theorem binary_product_cube_le (n a : ℕ) (hn : 4096≤n)
    (horder : a≤n^(4*Nat.log 2 n+24)) :
    (2^n*a)^3≤5^(2*n-1) := by
  let m := Nat.log 2 n
  have hm : 12≤m := Nat.le_log_of_pow_le (by decide : 1<2)
    (show 2^12≤n by simpa only [show (2:ℕ)^12=4096 by decide] using hn)
  have hn0 : n≠0 := by omega
  have hlow : 2^m≤n := Nat.pow_log_le_self 2 hn0
  have hupp : n≤2^(m+1) := (Nat.lt_pow_succ_log_self (by decide : 1<2) n).le
  have ha : a≤2^((m+1)*(4*m+24)) := by
    apply horder.trans
    simpa only [m,pow_mul] using Nat.pow_le_pow_left hupp (4*m+24)
  have hb : 3*(m+1)*(4*m+24)+2≤n := (dyadic_budget m hm).trans hlow
  rw [Nat.mul_assoc] at hb
  have he : (n+(m+1)*(4*m+24))*3≤2*(2*n-1) := by omega
  calc
    (2^n*a)^3≤(2^n*2^((m+1)*(4*m+24)))^3 :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_left _ ha) 3
    _ = 2^((n+(m+1)*(4*m+24))*3) := by rw [←pow_add,←pow_mul]
    _ ≤ 2^(2*(2*n-1)) := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) he
    _ = 4^(2*n-1) := by rw [show (4:ℕ)=2^2 by decide,pow_mul]
    _ ≤ 5^(2*n-1) := Nat.pow_le_pow_left (by decide) _

theorem ternary_product_cube_le (n a : ℕ) (hn : 4096≤n)
    (horder : a≤n^(4*Nat.log 2 n+24)) :
    (3^n*a)^3≤5^(3*n-1) := by
  have hbinary := binary_product_cube_le n a hn horder
  have hthree : (3^n)^3=27^n := by
    rw [←pow_mul,Nat.mul_comm n 3,pow_mul]
    norm_num
  have htwo : (2^n)^3=8^n := by
    rw [←pow_mul,Nat.mul_comm n 3,pow_mul]
    norm_num
  have h27 : (3^n)^3≤5^n*(2^n)^3 := by
    rw [hthree,htwo,←mul_pow]
    exact Nat.pow_le_pow_left (by decide : 27≤5*8) n
  calc
    (3^n*a)^3=(3^n)^3*a^3 := mul_pow _ _ _
    _ ≤ (5^n*(2^n)^3)*a^3 := Nat.mul_le_mul_right _ h27
    _ = 5^n*(2^n*a)^3 := by rw [mul_pow];ring
    _ ≤ 5^n*5^(2*n-1) := Nat.mul_le_mul_left _ hbinary
    _ = 5^(3*n-1) := by rw [←pow_add];congr 1;omega

end SymmetricSubgroupAsymptotics.LargePrimitiveSmallFibreClassNumerics
