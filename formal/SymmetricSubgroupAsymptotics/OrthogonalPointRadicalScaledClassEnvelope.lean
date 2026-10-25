import SymmetricSubgroupAsymptotics.OrthogonalPointRadicalOrderCubeNumerics
import SymmetricSubgroupAsymptotics.RankOneSharpOrderCubeNumerics

/-! One scaled class-equation envelope for the split/minus orthogonal
point-radical index. Two seeds and field/rank inductions cover every
odd field from rank four and the binary family from rank five. The
binary rank-four head is deliberately outside the shared statement. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.OrthogonalPointRadicalScaledClassEnvelope
open OrthogonalPointRadicalOrderCubeNumerics

private def exponent (r : ℕ) : ℕ := 2*r^2-r+11

private theorem exponent_double (r : ℕ) (hr : 4 ≤ r) :
    exponent (r+1) ≤ 2*exponent r := by
  have ha : r ≤ 2*r^2 := by nlinarith
  have hb : r+1 ≤ 2*(r+1)^2 := by nlinarith
  have hsa := Nat.sub_add_cancel ha
  have hsb := Nat.sub_add_cancel hb
  unfold exponent
  nlinarith

private theorem index_double (q r : ℕ) (hq : 2 ≤ q) (hr : 4 ≤ r) :
    2*minusIndex q r ≤ minusIndex q (r+1) := by
  have ha : q^(r-2)-1 ≤ q^(r-1)-1 :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_right (by omega : 0 < q) (by omega : r-2 ≤ r-1)) 1
  have hb : 2*q^(r-1) ≤ q^r := by
    calc
      _ ≤ q*q^(r-1) := Nat.mul_le_mul_right _ hq
      _ = q^r := by
        rw [←pow_succ']
        exact congrArg (fun n : ℕ => q^n) (by omega)
  change 2*((q^(r-2)-1)*q^(r-1)) ≤ (q^((r+1)-2)-1)*q^((r+1)-1)
  rw [show r+1-2=r-1 by omega,show r+1-1=r by omega]
  calc
    _ = (q^(r-2)-1)*(2*q^(r-1)) := by ring
    _ ≤ (q^(r-1)-1)*q^r := Nat.mul_le_mul ha hb

private theorem index_field_identity (q : ℕ) (hq : 3 ≤ q) :
    minusIndex q 4+q^3=q^5 := by
  have hsub : q^2-1+1=q^2 := by
    have hp := Nat.one_le_pow 2 q (by omega : 1 ≤ q)
    omega
  change (q^2-1)*q^3+q^3=q^5
  calc
    _ = (q^2-1+1)*q^3 := by ring
    _ = q^2*q^3 := congrArg (fun n : ℕ => n*q^3) hsub
    _ = q^5 := by ring

private theorem field_seed (q : ℕ) (hq : 3 ≤ q) :
    25*q^117 ≤ 3^(minusIndex q 4) := by
  induction q,hq using Nat.le_induction with
  | base => decide +kernel
  | succ q hq ih =>
    have hs := RankOneSharpOrderCubeNumerics.polynomial_step (3^32) 117 3 q
      (by decide) hq (by decide +kernel)
    have hstep : minusIndex q 4+32 ≤ minusIndex (q+1) 4 := by
      have h₀ := index_field_identity q hq
      have h₁ := index_field_identity (q+1) (by omega)
      have hq4 : 81 ≤ q^4 := (by decide : 81 ≤ (3:ℕ)^4).trans
        (Nat.pow_le_pow_left hq 4)
      nlinarith
    calc
      25*(q+1)^117 ≤ 25*(3^32*q^117) := Nat.mul_le_mul_left 25 hs
      _ = 3^32*(25*q^117) := by ring
      _ ≤ 3^32*3^(minusIndex q 4) := Nat.mul_le_mul_left _ ih
      _ = 3^(32+minusIndex q 4) := (pow_add _ _ _).symm
      _ ≤ 3^(minusIndex (q+1) 4) := Nat.pow_le_pow_right (by decide) (by omega)

private theorem rank_tail (q r₀ : ℕ) (hq : 2 ≤ q) (hr₀ : 4 ≤ r₀)
    (hbase : 25*q^(3*exponent r₀) ≤ 3^(minusIndex q r₀))
    (r : ℕ) (hr : r₀ ≤ r) : 25*q^(3*exponent r) ≤ 3^(minusIndex q r) := by
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
      _ ≤ (3^(minusIndex q r))^2 := Nat.pow_le_pow_left ih 2
      _ = 3^(2*minusIndex q r) := by
        rw [←pow_mul]
        exact congrArg (fun n : ℕ => 3^n) (Nat.mul_comm _ _)
      _ ≤ 3^(minusIndex q (r+1)) := Nat.pow_le_pow_right (by decide)
        (index_double q r hq (by omega))

private theorem index_power_lower (q r : ℕ) (hq : 2 ≤ q) (hr : 4 ≤ r) :
    q^(2*r-4) ≤ minusIndex q r := by
  have hv : 1 ≤ q^(r-3) := Nat.one_le_pow _ _ (by omega)
  have he : q^(r-2)=q*q^(r-3) := by
    rw [←pow_succ']
    exact congrArg (fun n : ℕ => q^n) (by omega)
  have hm : q^(r-3) ≤ q^(r-2)-1 := by
    have hh := Nat.mul_le_mul_right (q^(r-3)) hq
    rw [he]
    omega
  calc
    q^(2*r-4) = q^(r-3)*q^(r-1) := by
      rw [←pow_add]
      exact congrArg (fun n : ℕ => q^n) (by omega)
    _ ≤ (q^(r-2)-1)*q^(r-1) := Nat.mul_le_mul_right _ hm
    _ = minusIndex q r := rfl

private theorem class_equation_power (q r : ℕ) (hq : 2 ≤ q) (hr : 4 ≤ r) :
    (q^(2*r^2+r)/minusIndex q r+1)*q^6 ≤ q^(exponent r) := by
  let a := (2*r^2+r)-(2*r-4)
  have ht : 2*r-4 ≤ 2*r^2+r :=
    (Nat.sub_le (2*r) 4).trans (by nlinarith : 2*r ≤ 2*r^2+r)
  have hsum : a+(2*r-4)=2*r^2+r := Nat.sub_add_cancel ht
  have hdiv : q^(2*r^2+r)/minusIndex q r ≤ q^a := by
    calc
      _ ≤ q^(2*r^2+r)/q^(2*r-4) :=
        Nat.div_le_div_left (index_power_lower q r hq hr) (pow_pos (by omega) _)
      _ = q^a := by
        have hp : q^(2*r^2+r)=q^a*q^(2*r-4) := by rw [←pow_add,hsum]
        rw [hp,Nat.mul_div_cancel _ (pow_pos (by omega : 0 < q) _)]
  have hadd : q^a+1 ≤ q^(a+1) := by
    have hpos : 1 ≤ q^a := Nat.one_le_pow _ _ (by omega)
    have hh := Nat.mul_le_mul_right (q^a) hq
    rw [pow_succ']
    omega
  have he : (a+1)+6=exponent r := by
    have ht' : 2*r-4+4=2*r := Nat.sub_add_cancel (by omega : 4 ≤ 2*r)
    have hs : 2*r^2-r+r=2*r^2 := Nat.sub_add_cancel (by nlinarith : r ≤ 2*r^2)
    unfold exponent
    omega
  calc
    _ ≤ (q^a+1)*q^6 := Nat.mul_le_mul_right _ (Nat.add_le_add_right hdiv 1)
    _ ≤ q^(a+1)*q^6 := Nat.mul_le_mul_right _ hadd
    _ = q^(exponent r) := by rw [←pow_add,he]

theorem scaled_class_equation_budget (q r : ℕ) (hq : 2 ≤ q) (hr : 4 ≤ r)
    (hwindow : 3 ≤ q ∨ 5 ≤ r) :
    25*((q^(2*r^2+r)/minusIndex q r+1)*q^6)^3 ≤ 3^(minusIndex q r) := by
  have hpower := Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (class_equation_power q r hq hr) 3)
  have hp : (q^(exponent r))^3=q^(3*exponent r) := by
    rw [←pow_mul]
    exact congrArg (fun n : ℕ => q^n) (Nat.mul_comm _ _)
  rw [hp] at hpower
  apply hpower.trans
  by_cases hq3 : 3 ≤ q
  · exact rank_tail q 4 hq (by decide) (field_seed q hq3) r hr
  · have hq2 : q=2 := by omega
    subst q
    exact rank_tail 2 5 (by decide) (by decide) (by decide +kernel) r
      (hwindow.resolve_left hq3)

end SymmetricSubgroupAsymptotics.OrthogonalPointRadicalScaledClassEnvelope
