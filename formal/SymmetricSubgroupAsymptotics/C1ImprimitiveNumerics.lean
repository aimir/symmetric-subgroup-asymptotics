import Mathlib.Tactic

/-! Broad numerical branches of the three-twentieths induction.
Here v is the primitive component's ternary composition multiplicity,
e the induced-module bound, t the actual top relative head, and d the
whole relative head. The structural inequality d≤v*e+t is a separate
project theorem; this file proves its numerical consequences and never
assumes the high-action classification itself. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics

/-- All ordinary-top branches with block size at least five. -/
theorem c1_imprimitive_ordinary_large (r s v e t d : ℕ)
    (hr : 5≤r) (hs : 0<s) (hv : 3*v≤r) (he : 3*e≤s)
    (ht : 27*t≤5*s) (hd : d≤v*e+t) : 20*d<3*(r*s) := by
  have hve := Nat.mul_le_mul hv he
  have hrs := Nat.mul_le_mul_right s hr
  nlinarith

/-- The full block-size-four ordinary-top branch. -/
theorem c1_imprimitive_ordinary_four (s v e t d : ℕ)
    (hs : 0<s) (hv : v≤1) (he : 3*e≤s)
    (ht : 27*t≤5*s) (hd : d≤v*e+t) : 20*d<3*(4*s) := by
  have hve := Nat.mul_le_mul_right e hv
  nlinarith

/-- The exceptional top-degree18 numerical seam is eliminated for all
primitive block sizes at least nine. -/
theorem c1_imprimitive_top_eighteen_large (r v e t d : ℕ)
    (hr : 9≤r) (hv : 3*v≤r) (he : e≤7)
    (ht : t≤3) (hd : d≤v*e+t) : 20*d<3*(r*18) := by
  have hve := Nat.mul_le_mul_left v he
  nlinarith

/-- A semiregular ternary top of degree6 removes every block size≥4,
using only the integral primitive composition bound. -/
theorem c1_imprimitive_top_six (r v e t d : ℕ)
    (hr : 4≤r) (hv : 3*v≤r) (he : e≤2)
    (ht : t≤1) (hd : d≤v*e+t) : 20*d<3*(r*6) := by
  have hve := Nat.mul_le_mul_left v he
  by_cases h4 : r=4
  · subst r
    have hv1 : v≤1 := by omega
    nlinarith
  · have hr5 : 5≤r := by omega
    nlinarith

/-- Degree2 tops reduce directly to the strict primitive density input.
The possible primitive degree9 exception remains outside this premise. -/
theorem c1_imprimitive_top_two (r v e t d : ℕ)
    (hv : 10*v≤3*r) (he : e≤1) (ht : t=0) (hd : d≤v*e+t) :
    20*d≤3*(r*2) := by
  have hve := Nat.mul_le_mul_left v he
  nlinarith

/-- Natural A4 tops with block size≥4 are numerically below threshold. -/
theorem c1_imprimitive_top_a4 (r v e t d : ℕ)
    (hr : 4≤r) (hv : 3*v≤r) (he : e≤1)
    (ht : t≤1) (hd : d≤v*e+t) : 20*d<3*(r*4) := by
  have hve := Nat.mul_le_mul_left v he
  nlinarith

/-- The four exceptional degree9 top types are eliminated uniformly
whenever the primitive block size is at least six. -/
theorem c1_imprimitive_top_e9_large (r v e t d : ℕ)
    (hr : 6≤r) (hv : 3*v≤r) (he : e≤3)
    (ht : t≤2) (hd : d≤v*e+t) : 20*d<3*(r*9) := by
  have hve := Nat.mul_le_mul_left v he
  nlinarith

/-- A natural C3 top is harmless in the generic strict primitive-density
range. Block sizes4–6 are left to their concrete small inputs. -/
theorem c1_imprimitive_top_c3_large (r v e t d : ℕ)
    (hr : 7≤r) (hv : 10*v<3*r) (he : e≤1)
    (ht : t≤1) (hd : d≤v*e+t) : 20*d<3*(r*3) := by
  have hve := Nat.mul_le_mul_left v he
  nlinarith

end SymmetricSubgroupAsymptotics
