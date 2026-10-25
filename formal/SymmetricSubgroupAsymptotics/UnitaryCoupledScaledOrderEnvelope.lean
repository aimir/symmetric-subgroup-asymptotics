import SymmetricSubgroupAsymptotics.QuadraticExponentialPolynomialTail

/-! An elementary rank/field envelope for a coupled index. The bound
charges the whole component order, rather than using a conjugacy-class
estimate. No group or action is part of this scalar statement. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.UnitaryCoupledScaledOrderEnvelope

private theorem self_le_three_pow_pred (q : ℕ) (hq : 1 ≤ q) :
    q ≤ 3^(q-1) := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
    have he : q+1-1=(q-1)+1 := by omega
    rw [he,pow_succ]
    nlinarith

private theorem rank_coefficient_le (r : ℕ) (hr : 5 ≤ r) :
    3*(r+2)^2+3 ≤ 6*2^(2*r-5) := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
    have hstep : 3*(r+1+2)^2+3 ≤ 4*(3*(r+2)^2+3) := by nlinarith
    have he : 2*(r+1)-5=(2*r-5)+2 := by omega
    calc
      _ ≤ 4*(3*(r+2)^2+3) := hstep
      _ ≤ 4*(6*2^(2*r-5)) := Nat.mul_le_mul_left 4 ih
      _ = 6*2^(2*(r+1)-5) := by rw [he,pow_add]; ring

private theorem coefficient_le (q r : ℕ) (hq : 2 ≤ q) (hr : 4 ≤ r)
    (hhead : r=4 → 3 ≤ q) :
    3*(r+2)^2+3 ≤ 2*(q+1)*q^(2*r-5) := by
  by_cases hr5 : 5 ≤ r
  · exact (rank_coefficient_le r hr5).trans
      (Nat.mul_le_mul (by omega : 6 ≤ 2*(q+1))
        (Nat.pow_le_pow_left hq _))
  · have hr4 : r=4 := by omega
    subst r
    have hq3 := hhead rfl
    exact (by decide : 3*((4:ℕ)+2)^2+3 ≤ 2*(3+1)*3^(2*4-5)).trans
      (Nat.mul_le_mul (by omega : 2*(3+1) ≤ 2*(q+1))
        (Nat.pow_le_pow_left hq3 _))

theorem scaled_order_cube_le (q r : ℕ) (hq : 2 ≤ q) (hr : 4 ≤ r)
    (hhead : r=4 → 3 ≤ q) :
    25*(q^((r+2)^2))^3 ≤ 3^(2*(q^2-1)*q^(2*r-5)) := by
  have hq1 : 1 ≤ q := by omega
  have hpred : q-1+1=q := by omega
  have hsq : q^2-1+1=q^2 := Nat.sub_add_cancel (Nat.one_le_pow _ _ hq1)
  have hfactor : q^2-1=(q-1)*(q+1) := by nlinarith
  have hcoeff := coefficient_le q r hq hr hhead
  have hexp : 3+(q-1)*((r+2)^2*3) ≤ 2*(q^2-1)*q^(2*r-5) := by
    calc
      _ ≤ (q-1)*3+(q-1)*((r+2)^2*3) :=
        Nat.add_le_add_right (Nat.le_mul_of_pos_left 3 (by omega : 0 < q-1)) _
      _ = (q-1)*(3*(r+2)^2+3) := by ring
      _ ≤ (q-1)*(2*(q+1)*q^(2*r-5)) := Nat.mul_le_mul_left _ hcoeff
      _ = 2*(q^2-1)*q^(2*r-5) := by rw [hfactor]; ring
  have hpow : ((3^(q-1))^((r+2)^2))^3 =
      3^((q-1)*((r+2)^2*3)) := by
    rw [←pow_mul,←pow_mul]
  calc
    _ ≤ 27*(q^((r+2)^2))^3 := Nat.mul_le_mul_right _ (by decide : 25 ≤ 27)
    _ ≤ 3^3*((3^(q-1))^((r+2)^2))^3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
        (Nat.pow_le_pow_left (self_le_three_pow_pred q hq1) _) 3)
    _ = 3^(3+(q-1)*((r+2)^2*3)) := by rw [hpow,pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hexp

end SymmetricSubgroupAsymptotics.UnitaryCoupledScaledOrderEnvelope
