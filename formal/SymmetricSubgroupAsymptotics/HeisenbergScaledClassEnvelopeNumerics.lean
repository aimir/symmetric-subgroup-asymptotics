import SymmetricSubgroupAsymptotics.SmallReeScaledClassEnvelopeNumerics

/-! Scaled order cubes at the literal prime-times-q^4 index. The
q=3 prime factor is retained; one polynomial induction covers q≥4.
The exponent66 is the proved coarse original-model ceiling. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.HeisenbergScaledClassEnvelopeNumerics

private theorem field_le_three_power (q : ℕ) (hq : 4 ≤ q) : q ≤ 3^(q-2) := by
  induction q,hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
    have he : q+1-2=q-2+1 := by omega
    calc
      q+1 ≤ 3*q := by omega
      _ ≤ 3*3^(q-2) := Nat.mul_le_mul_left 3 ih
      _ = 3^(q+1-2) := by rw [he,pow_succ]; ring

private theorem exponent_le (q : ℕ) (hq : 4 ≤ q) :
    198*(q-2)+3 ≤ 2*q^4 := by
  induction q,hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
    have hcube : 64 ≤ q^3 := (by decide : 64 ≤ (4:ℕ)^3).trans
      (Nat.pow_le_pow_left hq 3)
    have hstep : q^4+4*q^3 ≤ (q+1)^4 := by nlinarith
    calc
      198*(q+1-2)+3 = (198*(q-2)+3)+198 := by omega
      _ ≤ 2*q^4+198 := Nat.add_le_add_right ih 198
      _ ≤ 2*(q+1)^4 := by nlinarith

theorem scaled_order_cube (q p : ℕ) (hq : 3 ≤ q) (hp : 2 ≤ p)
    (hthree : q=3 → 3 ≤ p) : 25*(q^66)^3 ≤ 3^(p*q^4) := by
  by_cases hq3 : q=3
  · subst q
    have hp3 := hthree rfl
    exact (by decide +kernel : 25*((3:ℕ)^66)^3 ≤ 3^(3*3^4)).trans
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hp3))
  · have hq4 : 4 ≤ q := by omega
    have hp198 : (q^66)^3=q^198 := by rw [←pow_mul]
    have he : 198*(q-2)+3 ≤ p*q^4 :=
      (exponent_le q hq4).trans (Nat.mul_le_mul_right _ hp)
    calc
      25*(q^66)^3 = 25*q^198 := by rw [hp198]
      _ ≤ 3^3*(3^(q-2))^198 := Nat.mul_le_mul
        (by decide : (25:ℕ) ≤ 3^3)
        (Nat.pow_le_pow_left (field_le_three_power q hq4) 198)
      _ = 3^(198*(q-2)+3) := by
        rw [←pow_mul,←pow_add]
        exact congrArg (fun z : ℕ => 3^z) (by ring)
      _ ≤ 3^(p*q^4) := Nat.pow_le_pow_right (by decide) he

end SymmetricSubgroupAsymptotics.HeisenbergScaledClassEnvelopeNumerics
