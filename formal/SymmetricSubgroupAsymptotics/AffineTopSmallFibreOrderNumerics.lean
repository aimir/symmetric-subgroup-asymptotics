import SymmetricSubgroupAsymptotics.LargePrimitiveSmallFibreClassNumerics
import SymmetricSubgroupAsymptotics.RankOneSharpOrderCubeNumerics

/-! The actual affine order n^(log₂n+1) pays the small-fibre cube from
128 coordinates. One fixed-exponent polynomial tail handles the first
dyadic interval; a single dyadic induction handles all later intervals.
No primitive action or bounded-degree class table is enumerated. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.AffineTopSmallFibreOrderNumerics

theorem dyadic_budget (m : ℕ) (hm : 8≤m) :
    3*(m+1)*(m+1)+2≤2^m := by
  induction m,hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have hs : 3*(m+1+1)*(m+1+1)+2≤2*(3*(m+1)*(m+1)+2) := by
      nlinarith only [hm,Nat.zero_le (m^2)]
    exact hs.trans ((Nat.mul_le_mul_left 2 ih).trans_eq (by rw [pow_succ]; omega))

theorem fixed_eighth_power_budget (n : ℕ) (hn : 128≤n) :
    8^n*n^24≤5^(2*n-1) := by
  induction n,hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    have hp : (n+1)^24≤2*n^24 :=
      RankOneSharpOrderCubeNumerics.polynomial_step 2 24 128 n (by decide) hn (by decide +kernel)
    calc
      _=8*8^n*(n+1)^24 := by rw [pow_succ]; ring
      _≤8*8^n*(2*n^24) := Nat.mul_le_mul_left _ hp
      _=16*(8^n*n^24) := by ring
      _≤16*5^(2*n-1) := Nat.mul_le_mul_left _ ih
      _≤25*5^(2*n-1) := Nat.mul_le_mul_right _ (by decide : (16:ℕ)≤25)
      _=5^(2*(n+1)-1) := by
        rw [show 2*(n+1)-1=(2*n-1)+2 by omega,pow_add]
        ring

theorem binary_product_cube_le (n a : ℕ) (hn : 128≤n)
    (horder : a≤n^(Nat.log 2 n+1)) :
    (2^n*a)^3≤5^(2*n-1) := by
  by_cases h256 : 256≤n
  · let m := Nat.log 2 n
    have hm : 8≤m := Nat.le_log_of_pow_le (by decide : 1<2)
      (show 2^8≤n by simpa only [show (2:ℕ)^8=256 by decide] using h256)
    have hn0 : n≠0 := by omega
    have hlow : 2^m≤n := Nat.pow_log_le_self 2 hn0
    have hupp : n≤2^(m+1) := (Nat.lt_pow_succ_log_self (by decide : 1<2) n).le
    have ha : a≤2^((m+1)*(m+1)) := by
      apply horder.trans
      simpa only [m,pow_mul] using Nat.pow_le_pow_left hupp (m+1)
    have hb : 3*(m+1)*(m+1)+2≤n := (dyadic_budget m hm).trans hlow
    rw [Nat.mul_assoc] at hb
    have he : (n+(m+1)*(m+1))*3≤2*(2*n-1) := by omega
    calc
      _≤(2^n*2^((m+1)*(m+1)))^3 := Nat.pow_le_pow_left (Nat.mul_le_mul_left _ ha) 3
      _=2^((n+(m+1)*(m+1))*3) := by rw [←pow_add,←pow_mul]
      _≤2^(2*(2*n-1)) := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) he
      _=4^(2*n-1) := by rw [show (4:ℕ)=2^2 by decide,pow_mul]
      _≤5^(2*n-1) := Nat.pow_le_pow_left (by decide) _
  · have hm : Nat.log 2 n<8 := Nat.log_lt_of_lt_pow (by omega : n≠0)
      (by simpa only [show (2:ℕ)^8=256 by decide] using (show n<256 by omega))
    have ha : a≤n^8 := horder.trans (Nat.pow_le_pow_right (by omega) (by omega))
    have htwo : ((2:ℕ)^n)^3=8^n := by
      rw [←pow_mul,Nat.mul_comm n 3,pow_mul]
      norm_num
    have hpoly : (n^8)^3=n^24 := by
      simpa only [show (8:ℕ)*3=24 by decide] using (pow_mul n 8 3).symm
    calc
      _≤(2^n*n^8)^3 := Nat.pow_le_pow_left (Nat.mul_le_mul_left _ ha) 3
      _=8^n*n^24 := by rw [mul_pow,htwo,hpoly]
      _≤5^(2*n-1) := fixed_eighth_power_budget n hn

theorem ternary_product_cube_le (n a : ℕ) (hn : 128≤n)
    (horder : a≤n^(Nat.log 2 n+1)) :
    (3^n*a)^3≤5^(3*n-1) := by
  have hbinary := binary_product_cube_le n a hn horder
  have hthree : ((3:ℕ)^n)^3=27^n := by
    rw [←pow_mul,Nat.mul_comm n 3,pow_mul]
    norm_num
  have htwo : ((2:ℕ)^n)^3=8^n := by
    rw [←pow_mul,Nat.mul_comm n 3,pow_mul]
    norm_num
  have h27 : (3^n)^3≤5^n*(2^n)^3 := by
    rw [hthree,htwo,←mul_pow]
    exact Nat.pow_le_pow_left (by decide : (27:ℕ)≤5*8) n
  calc
    _=(3^n)^3*a^3 := mul_pow _ _ _
    _≤(5^n*(2^n)^3)*a^3 := Nat.mul_le_mul_right _ h27
    _=5^n*(2^n*a)^3 := by rw [mul_pow]; ring
    _≤5^n*5^(2*n-1) := Nat.mul_le_mul_left _ hbinary
    _=5^(3*n-1) := by rw [←pow_add]; congr 1; omega

end SymmetricSubgroupAsymptotics.AffineTopSmallFibreOrderNumerics
