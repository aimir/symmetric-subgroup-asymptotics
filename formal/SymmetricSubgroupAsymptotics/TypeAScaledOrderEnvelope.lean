import SymmetricSubgroupAsymptotics.QuadraticExponentialPolynomialTail

/-! Exponential rectangles and a rank-two polynomial envelope. These
integer lemmas assert no group recognition or action classification. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.TypeAScaledOrderEnvelope

private theorem cube_le_three_power (q : ℕ) (hq : 1 ≤ q) :
    q^3 ≤ 3^(2*(q-1)) := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
    have he : 2*(q+1-1)=2*(q-1)+2 := by omega
    calc
      (q+1)^3 ≤ (2*q)^3 := Nat.pow_le_pow_left (by omega) 3
      _ = 8*q^3 := by ring
      _ ≤ 9*q^3 := Nat.mul_le_mul_right _ (by decide : 8 ≤ 9)
      _ ≤ 9*3^(2*(q-1)) := Nat.mul_le_mul_left 9 ih
      _ = 3^(2*(q+1-1)) := by rw [he,pow_add]; ring

private theorem coefficient_tail (q c r₀ : ℕ) (hq : 2 ≤ q) (hr₀ : 2 ≤ r₀)
    (hseed : 2*(r₀+2)^2+3 ≤ c*q^(r₀-2)) (r : ℕ) (hr : r₀ ≤ r) :
    2*(r+2)^2+3 ≤ c*q^(r-2) := by
  induction r, hr using Nat.le_induction with
  | base => exact hseed
  | succ r hr ih =>
    have hstep : 2*(r+1+2)^2+3 ≤ 2*(2*(r+2)^2+3) := by nlinarith
    have he : r+1-2=(r-2)+1 := by omega
    calc
      _ ≤ 2*(2*(r+2)^2+3) := hstep
      _ ≤ q*(2*(r+2)^2+3) := Nat.mul_le_mul_right _ hq
      _ ≤ q*(c*q^(r-2)) := Nat.mul_le_mul_left q ih
      _ = c*q^(r+1-2) := by rw [he,pow_succ]; ring

private theorem scaled_of_coefficient (q r c : ℕ) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hquad : c*(q-1) ≤ q^2) (hcoeff : 2*(r+2)^2+3 ≤ c*q^(r-2)) :
    25*(q^((r+2)^2))^3 ≤ 3^(q^r) := by
  have hexp : 3+2*(q-1)*(r+2)^2 ≤ q^r := by
    calc
      _ ≤ (q-1)*3+2*(q-1)*(r+2)^2 :=
        Nat.add_le_add_right (Nat.le_mul_of_pos_left 3 (by omega : 0 < q-1)) _
      _ = (q-1)*(2*(r+2)^2+3) := by ring
      _ ≤ (q-1)*(c*q^(r-2)) := Nat.mul_le_mul_left _ hcoeff
      _ = q^(r-2)*(c*(q-1)) := by ring
      _ ≤ q^(r-2)*q^2 := Nat.mul_le_mul_left _ hquad
      _ = q^r := by rw [←pow_add,show r-2+2=r by omega]
  have hp : (q^((r+2)^2))^3 ≤ 3^(2*(q-1)*(r+2)^2) := by
    calc
      _ = (q^3)^((r+2)^2) := by
        rw [←pow_mul,←pow_mul]
        exact congrArg (fun n : ℕ => q^n) (Nat.mul_comm _ _)
      _ ≤ (3^(2*(q-1)))^((r+2)^2) :=
        Nat.pow_le_pow_left (cube_le_three_power q (by omega)) _
      _ = _ := (pow_mul _ _ _).symm
  calc
    _ ≤ 27*3^(2*(q-1)*(r+2)^2) := Nat.mul_le_mul (by decide : 25 ≤ 27) hp
    _ = 3^(3+2*(q-1)*(r+2)^2) := by rw [pow_add]; norm_num only [Nat.reducePow]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hexp

theorem higher_scaled_order_cube_le (q r : ℕ) (hq : 2 ≤ q)
    (hwindow : 8 ≤ r ∨ (5 ≤ r ∧ 3 ≤ q) ∨ (4 ≤ r ∧ 4 ≤ q) ∨ (r=3 ∧ 5 ≤ q)) :
    25*(q^((r+2)^2))^3 ≤ 3^(q^r) := by
  have hquad : 4*(q-1) ≤ q^2 := by
    have he : q-1+1=q := by omega
    nlinarith
  rcases hwindow with hr | ⟨hr,hq3⟩ | ⟨hr,hq4⟩ | ⟨hr,hq5⟩
  · apply scaled_of_coefficient q r 4 hq (by omega) hquad
    apply coefficient_tail q 4 8 hq (by decide) ?_ r hr
    exact (by decide : 2*((8:ℕ)+2)^2+3 ≤ 4*2^(8-2)).trans
      (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hq _))
  · apply scaled_of_coefficient q r 4 hq (by omega) hquad
    apply coefficient_tail q 4 5 hq (by decide) ?_ r hr
    exact (by decide : 2*((5:ℕ)+2)^2+3 ≤ 4*3^(5-2)).trans
      (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hq3 _))
  · have hquad5 : 5*(q-1) ≤ q^2 := by
      by_cases hq5 : 5 ≤ q
      · exact (Nat.mul_le_mul_left 5 (Nat.sub_le q 1)).trans
          (by simpa only [pow_two] using Nat.mul_le_mul_right q hq5)
      · have he : q=4 := by omega
        subst q
        decide
    apply scaled_of_coefficient q r 5 hq (by omega) hquad5
    apply coefficient_tail q 5 4 hq (by decide) ?_ r hr
    exact (by decide : 2*((4:ℕ)+2)^2+3 ≤ 5*4^(4-2)).trans
      (Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left hq4 _))
  · subst r
    have hh := QuadraticExponentialPolynomialTail.polynomial_tail 25 75 3 5 5
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) q hq5
    have hc : (q^((3+2)^2))^3=q^75 := by
      rw [←pow_mul]
      exact congrArg (fun n : ℕ => q^n) (by decide : (3+2)^2*3=75)
    rw [hc]
    have hi : 5*q^2 ≤ q^3 :=
      (Nat.mul_le_mul_right (q^2) hq5).trans_eq (by ring)
    exact hh.trans (Nat.pow_le_pow_right (by decide) hi)

theorem rank_two_scaled_class_cube_le (q : ℕ) (hq : 5 ≤ q) :
    25*(18*q*(q^2+2*q))^3 ≤ 3^(q^2) := by
  induction q, hq using Nat.le_induction with
  | base => decide +kernel
  | succ q hq ih =>
    have hstep : 18*(q+1)*((q+1)^2+2*(q+1)) ≤ 8*(18*q*(q^2+2*q)) := by
      calc
        _ = 18*(q+1)^2*(q+3) := by ring
        _ ≤ 18*(2*q)^2*(2*(q+2)) := Nat.mul_le_mul
          (Nat.mul_le_mul_left 18 (Nat.pow_le_pow_left (by omega : q+1 ≤ 2*q) 2))
          (by omega)
        _ = _ := by ring
    have hgap : 512 ≤ 3^(2*q+1) :=
      (by decide : 512 ≤ (3:ℕ)^11).trans
        (Nat.pow_le_pow_right (by decide) (by omega))
    calc
      _ ≤ 25*(8*(18*q*(q^2+2*q)))^3 :=
        Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hstep 3)
      _ = 512*(25*(18*q*(q^2+2*q))^3) := by ring
      _ ≤ 512*3^(q^2) := Nat.mul_le_mul_left 512 ih
      _ ≤ 3^(2*q+1)*3^(q^2) := Nat.mul_le_mul_right _ hgap
      _ = 3^((q+1)^2) := by
        rw [←pow_add]
        exact congrArg (fun n : ℕ => 3^n) (by ring)

end SymmetricSubgroupAsymptotics.TypeAScaledOrderEnvelope
