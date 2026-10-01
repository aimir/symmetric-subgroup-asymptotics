import SymmetricSubgroupAsymptotics.MarkedC4PsiAnalysis

/-!
# The numerical Case-II marked-C4 peel

RDT's excessive-factor theorem supplies `e,z,g` with `e*z+g ≤ w/2` and
`z ≤ w/4`.  Its dependent-factor bounds, after retaining all abelian
physical coordinates and all auxiliary `C₄` coordinates, give the two source
rank inequalities below.  This file proves that their complete epimorphism
exponent fits inside the exact marked quadratic reserve.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

/-- The Case-II epimorphism exponent, including all auxiliary cyclic-four
generators, is paid by the linear part of one marked quadratic reserve. -/
theorem caseII_epimorphism_cost_le
    {e z g w b₃ b₄ r dSource dNormal : ℝ}
    (hz : 0 ≤ z) (hg : 0 ≤ g)
    (hb₃ : 0 ≤ b₃) (hb₄ : 0 ≤ b₄) (hr : 0 ≤ r)
    (hexcess : e * z + g ≤ w / 2) (hzcap : z ≤ w / 4)
    (hSource : dSource ≤ e * b₃ / 4 + b₄ / 2 + r)
    (hNormal : dNormal ≤ b₃ / 4) :
    z * dSource + g * dNormal ≤ w * (b₃ + b₄) / 8 + w * r / 4 := by
  have hzs := mul_le_mul_of_nonneg_left hSource hz
  have hgn := mul_le_mul_of_nonneg_left hNormal hg
  have hb₃q : 0 ≤ b₃ / 4 := div_nonneg hb₃ (by norm_num)
  have hb₄q : 0 ≤ b₄ / 2 := div_nonneg hb₄ (by norm_num)
  have hex := mul_le_mul_of_nonneg_right hexcess hb₃q
  have hzb := mul_le_mul_of_nonneg_right hzcap hb₄q
  have hzr := mul_le_mul_of_nonneg_right hzcap hr
  calc
    z * dSource + g * dNormal ≤
        z * (e * b₃ / 4 + b₄ / 2 + r) + g * (b₃ / 4) := add_le_add hzs hgn
    _ = (e * z + g) * (b₃ / 4) + z * (b₄ / 2) + z * r := by ring
    _ ≤ (w / 2) * (b₃ / 4) + (w / 4) * (b₄ / 2) + (w / 4) * r := by
      linarith
    _ = w * (b₃ + b₄) / 8 + w * r / 4 := by ring

/-- The Case-II exponent fits in `F(b,r)-F(b-w,r)` once the remaining
physical support is `b-w`.  The unused `w²/16` is the induction reserve. -/
theorem caseII_epimorphism_cost_le_markedF_reserve
    {e z g b w b₃ b₄ r dSource dNormal : ℝ}
    (hz : 0 ≤ z) (hg : 0 ≤ g)
    (hb₃ : 0 ≤ b₃) (hb₄ : 0 ≤ b₄) (hr : 0 ≤ r)
    (hwidth : b₃ + b₄ = b - w)
    (hexcess : e * z + g ≤ w / 2) (hzcap : z ≤ w / 4)
    (hSource : dSource ≤ e * b₃ / 4 + b₄ / 2 + r)
    (hNormal : dNormal ≤ b₃ / 4) :
    z * dSource + g * dNormal ≤ markedF b r - markedF (b - w) r := by
  have hcost := caseII_epimorphism_cost_le hz hg hb₃ hb₄ hr
    hexcess hzcap hSource hNormal
  rw [markedF_reserve]
  rw [hwidth] at hcost
  nlinarith [sq_nonneg w]

/-- A peel with an additional nonnegative error `E` is still paid after the
same error is added to the reserve. -/
theorem caseII_epimorphism_cost_add_error_le
    {e z g b w b₃ b₄ r dSource dNormal E : ℝ}
    (hz : 0 ≤ z) (hg : 0 ≤ g)
    (hb₃ : 0 ≤ b₃) (hb₄ : 0 ≤ b₄) (hr : 0 ≤ r)
    (hwidth : b₃ + b₄ = b - w)
    (hexcess : e * z + g ≤ w / 2) (hzcap : z ≤ w / 4)
    (hSource : dSource ≤ e * b₃ / 4 + b₄ / 2 + r)
    (hNormal : dNormal ≤ b₃ / 4) :
    z * dSource + g * dNormal + E ≤
      markedF b r - markedF (b - w) r + E := by
  linarith [caseII_epimorphism_cost_le_markedF_reserve hz hg
    hb₃ hb₄ hr hwidth hexcess hzcap hSource hNormal]

end MarkedC4
end SymmetricSubgroupAsymptotics

end
