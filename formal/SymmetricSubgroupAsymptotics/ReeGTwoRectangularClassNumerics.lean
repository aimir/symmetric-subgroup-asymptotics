import SymmetricSubgroupAsymptotics.RankOneSharpOrderCubeNumerics

/-! Scalar order-cube capacity at the rectangular ReeG2 index 3q.
The group-theoretic index is not a premise of any numerical lemma here;
its actual original-model proof is supplied separately. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.ReeGTwoRectangularClassNumerics

def orderBound (q : ℕ) : ℕ := q^3*(q-1)*(q^3+1)

theorem twice_le_three_pow (n : ℕ) : 2*n ≤ 3^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [pow_succ]
    have hp : 1 ≤ 3^n := Nat.one_le_pow n 3 (by decide)
    nlinarith

theorem order_le_seventh (q : ℕ) (hq : 1 ≤ q) : orderBound q ≤ q^7 := by
  have hsub : q-1+1=q := by omega
  have hq3 : q ≤ q^3+1 := by
    have hh : q ≤ q^3 := Nat.le_self_pow (by decide) q
    omega
  have he : (q-1)*(q^3+1)+(q^3+1)=q^4+q := by
    calc
      _ = (q-1+1)*(q^3+1) := by ring
      _ = _ := by rw [hsub]; ring
  have hs : (q-1)*(q^3+1) ≤ q^4 := by omega
  calc
    orderBound q = q^3*((q-1)*(q^3+1)) := by unfold orderBound; ring
    _ ≤ q^3*q^4 := Nat.mul_le_mul_left _ hs
    _ = q^7 := by ring

theorem field_power_cube_le (q : ℕ) (hq : 27 ≤ q) : q^24 ≤ 5^(3*q-1) := by
  have ht := RankOneSharpOrderCubeNumerics.polynomial_tail 1 24 125 27
    (by decide) (by decide +kernel) (by decide +kernel) q hq
  calc
    q^24 ≤ 125^(q-1) := by simpa only [one_mul] using ht
    _ = (5^3)^(q-1) := rfl
    _ = 5^(3*(q-1)) := (pow_mul _ _ _).symm
    _ ≤ 5^(3*q-1) := Nat.pow_le_pow_right (by decide) (by omega)

end SymmetricSubgroupAsymptotics.ReeGTwoRectangularClassNumerics
