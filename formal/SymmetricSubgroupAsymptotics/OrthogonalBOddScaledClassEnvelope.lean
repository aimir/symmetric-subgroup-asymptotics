import SymmetricSubgroupAsymptotics.RankOneSharpOrderCubeNumerics
import Mathlib.Tactic.IntervalCases

/-! The odd-B bilinear order exponent is 2*r^2+3*r+1. A shared
field/rank envelope pays its scaled class equation, apart from the
literal rank-three three-field seed, which uses the punctured index81.
There are no group/class-count assumptions in these integer lemmas. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.OrthogonalBOddScaledClassEnvelope

private def pointIndex (q r : ℕ) : ℕ := (q^(r-1)-1)*q^(r-1)
private def exponent (r : ℕ) : ℕ := 2*r^2+3*r+3

private theorem exponent_double (r : ℕ) (hr : 3 ≤ r) :
    exponent (r+1) ≤ 2*exponent r := by unfold exponent; nlinarith

private theorem index_double (q r : ℕ) (hq : 2 ≤ q) (hr : 3 ≤ r) :
    2*pointIndex q r ≤ pointIndex q (r+1) := by
  have ha : q^(r-1)-1 ≤ q^r-1 := Nat.sub_le_sub_right
    (Nat.pow_le_pow_right (by omega : 0 < q) (by omega : r-1 ≤ r)) 1
  have hb : 2*q^(r-1) ≤ q^r := by
    calc
      _ ≤ q*q^(r-1) := Nat.mul_le_mul_right _ hq
      _ = q^r := by
        rw [←pow_succ']
        exact congrArg (fun n : ℕ => q^n) (by omega)
  change 2*((q^(r-1)-1)*q^(r-1)) ≤ (q^((r+1)-1)-1)*q^((r+1)-1)
  rw [show r+1-1=r by omega]
  calc
    _ = (q^(r-1)-1)*(2*q^(r-1)) := by ring
    _ ≤ (q^r-1)*q^r := Nat.mul_le_mul ha hb

private theorem field_identity (q : ℕ) (hq : 4 ≤ q) :
    pointIndex q 3+q^2=q^4 := by
  have hs : q^2-1+1=q^2 := Nat.sub_add_cancel (Nat.one_le_pow 2 q (by omega))
  change (q^2-1)*q^2+q^2=q^4
  calc
    _ = (q^2-1+1)*q^2 := by ring
    _ = q^2*q^2 := congrArg (fun n : ℕ => n*q^2) hs
    _ = q^4 := by ring

private theorem field_seed (q : ℕ) (hq : 4 ≤ q) :
    25*q^90 ≤ 3^(pointIndex q 3) := by
  induction q,hq using Nat.le_induction with
  | base => decide +kernel
  | succ q hq ih =>
    have hs := RankOneSharpOrderCubeNumerics.polynomial_step (3^32) 90 4 q
      (by decide) hq (by decide +kernel)
    have hstep : pointIndex q 3+32 ≤ pointIndex (q+1) 3 := by
      have h₀ := field_identity q hq
      have h₁ := field_identity (q+1) (by omega)
      have hq2 : 16 ≤ q^2 := (by decide : 16 ≤ (4:ℕ)^2).trans
        (Nat.pow_le_pow_left hq 2)
      nlinarith
    calc
      25*(q+1)^90 ≤ 25*(3^32*q^90) := Nat.mul_le_mul_left 25 hs
      _ = 3^32*(25*q^90) := by ring
      _ ≤ 3^32*3^(pointIndex q 3) := Nat.mul_le_mul_left _ ih
      _ = 3^(32+pointIndex q 3) := (pow_add _ _ _).symm
      _ ≤ 3^(pointIndex (q+1) 3) := Nat.pow_le_pow_right (by decide) (by omega)

private theorem rank_tail (q r₀ : ℕ) (hq : 2 ≤ q) (hr₀ : 3 ≤ r₀)
    (hbase : 25*q^(3*exponent r₀) ≤ 3^(pointIndex q r₀))
    (r : ℕ) (hr : r₀ ≤ r) : 25*q^(3*exponent r) ≤ 3^(pointIndex q r) := by
  induction r,hr using Nat.le_induction with
  | base => exact hbase
  | succ r hr ih =>
    have hd := exponent_double r (by omega)
    have hp : q^(3*exponent (r+1)) ≤ (q^(3*exponent r))^2 := by
      calc
        _ ≤ q^((3*exponent r)*2) := Nat.pow_le_pow_right (by omega) (by omega)
        _ = (q^(3*exponent r))^2 := pow_mul _ _ _
    calc
      25*q^(3*exponent (r+1)) ≤ 25*(q^(3*exponent r))^2 := Nat.mul_le_mul_left 25 hp
      _ ≤ 25^2*(q^(3*exponent r))^2 := Nat.mul_le_mul_right _ (by decide : (25:ℕ) ≤ 25^2)
      _ = (25*q^(3*exponent r))^2 := (mul_pow _ _ _).symm
      _ ≤ (3^(pointIndex q r))^2 := Nat.pow_le_pow_left ih 2
      _ = 3^(2*pointIndex q r) := by
        rw [←pow_mul]
        exact congrArg (fun n : ℕ => 3^n) (Nat.mul_comm _ _)
      _ ≤ 3^(pointIndex q (r+1)) := Nat.pow_le_pow_right (by decide)
        (index_double q r hq (by omega))

private theorem class_equation_power (q r : ℕ) (hq : 3 ≤ q) :
    (q^(2*r^2+3*r+1)/pointIndex q r+1)*q ≤ q^(exponent r) := by
  let a := 2*r^2+3*r+1
  have hdiv : q^a/pointIndex q r ≤ q^a := Nat.div_le_self _ _
  have hadd : q^a+1 ≤ q^(a+1) := by
    have hp : 1 ≤ q^a := Nat.one_le_pow _ _ (by omega)
    have hh := Nat.mul_le_mul_right (q^a) (by omega : 2 ≤ q)
    rw [show q^(a+1)=q*q^a from pow_succ' q a]
    omega
  calc
    _ ≤ (q^a+1)*q := Nat.mul_le_mul_right _ (Nat.add_le_add_right hdiv 1)
    _ ≤ q^(a+1)*q := Nat.mul_le_mul_right _ hadd
    _ = q^(exponent r) := by rw [←pow_succ]; rfl

theorem scaled_class_equation_budget (q r : ℕ) (hq : 3 ≤ q) (hr : 3 ≤ r)
    (hwindow : 4 ≤ q ∨ 4 ≤ r) :
    25*((q^(2*r^2+3*r+1)/((q^(r-1)-1)*q^(r-1))+1)*q)^3 ≤
      3^((q^(r-1)-1)*q^(r-1)) := by
  have hp := Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (class_equation_power q r hq) 3)
  have he : (q^(exponent r))^3=q^(3*exponent r) := by
    rw [←pow_mul]
    exact congrArg (fun n : ℕ => q^n) (Nat.mul_comm _ _)
  rw [he] at hp
  apply hp.trans
  by_cases hq4 : 4 ≤ q
  · exact rank_tail q 3 (by omega) (by decide) (field_seed q hq4) r hr
  · have hq3 : q=3 := by omega
    subst q
    exact rank_tail 3 4 (by decide) (by decide) (by decide +kernel) r
      (hwindow.resolve_left hq4)

theorem eightyOne_le_ternary_multiple (k l : ℕ) (hl : 0 < l)
    (horbit : 72 ≤ (3^k-1)*l) : 81 ≤ 3^k*l := by
  by_cases hk : 4 ≤ k
  · exact ((by decide : 81 ≤ (3:ℕ)^4).trans
      (Nat.pow_le_pow_right (by decide) hk)).trans (Nat.le_mul_of_pos_right _ hl)
  · have hk3 : k ≤ 3 := by omega
    interval_cases k <;> norm_num at horbit <;> omega

theorem rank_three_three_field_budget :
    25*((3^28/81+1)*3)^3 ≤ 3^81 := by decide +kernel

end SymmetricSubgroupAsymptotics.OrthogonalBOddScaledClassEnvelope
