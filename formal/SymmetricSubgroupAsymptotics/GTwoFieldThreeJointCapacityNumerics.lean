import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Pure arithmetic for the same central intersection, endpoint image and
join in the field-three middle source. Divisibility is retained in the
small-index classifier, rather than replaced by a separate maximum. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.GTwoFieldThreeJointCapacityNumerics

private theorem central_cases (c : ℕ) (hc : c≤9) (hdiv : c∣27) :
    c=1 ∨ c=3 ∨ c=9 := by
  interval_cases c <;> norm_num at hdiv <;> norm_num

theorem index_ge_twentySeven (m c w l : ℕ) (hl : 0<l)
    (hc : c≤9) (hw : w=1 ∨ w=3) (hline : w=3 → 8≤3*l)
    (hprod : m*c*w=243*l) : 27≤m := by
  rcases hw with rfl | rfl
  · have hh := Nat.mul_le_mul_left m hc
    nlinarith only [hprod,hh,hl]
  · have hh := Nat.mul_le_mul_left (m*3) hc
    have hL := hline rfl
    have hl3 : 3≤l := by omega
    nlinarith only [hprod,hh,hl3]

theorem central_card_eq_nine_of_index_lt (m c w l : ℕ) (hl : 0<l)
    (hc : c≤9) (hdiv : c∣27) (hw : w=1 ∨ w=3)
    (hline : w=3 → 8≤3*l) (hprod : m*c*w=243*l) (hm : m<54) : c=9 := by
  rcases central_cases c hc hdiv with rfl | rfl | h9
  · rcases hw with rfl | rfl
    · nlinarith only [hprod,hl,hm]
    · have hL := hline rfl
      nlinarith only [hprod,hL,hm]
  · rcases hw with rfl | rfl
    · nlinarith only [hprod,hl,hm]
    · have hL := hline rfl
      nlinarith only [hprod,hL,hm]
  · exact h9

theorem index_ge_fiftyFour_of_double_join (m c w l l' : ℕ) (hl' : 0<l')
    (hc : c≤9) (hw : w=1 ∨ w=3) (he : l=2*l')
    (hline : w=3 → 8≤3*l') (hprod : m*c*w=243*l) : 54≤m := by
  rw [he] at hprod
  rcases hw with rfl | rfl
  · have hh := Nat.mul_le_mul_left m hc
    nlinarith only [hprod,hh,hl']
  · have hh := Nat.mul_le_mul_left (m*3) hc
    have hL := hline rfl
    have hl3 : 3≤l' := by omega
    nlinarith only [hprod,hh,hl3]

end SymmetricSubgroupAsymptotics.GTwoFieldThreeJointCapacityNumerics
