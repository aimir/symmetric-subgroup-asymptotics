import SymmetricSubgroupAsymptotics.CFSGQuadraticHyperbolicShear

/-! A full hyperbolic point radical clears the entire tail of a vector
whose opposite coordinate is one, at every quadratic norm. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.QuadraticHyperbolicRadicalClearing

open CFSGQuadraticHyperbolicShear
variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

theorem transform_clear_tail (Q : QuadraticForm K W) (x : K × (W × K))
    (hb : x.2.2 = 1) :
    transform Q (-x.2.1) x = (norm Q x, (0, 1)) := by
  have hw : (transform Q (-x.2.1) x).2.1 = 0 := by
    simp only [transform, hb, one_smul, add_neg_cancel]
  have hn := transform_preserves Q (-x.2.1) x
  have ha : (transform Q (-x.2.1) x).1 = norm Q x := by
    change (transform Q (-x.2.1) x).1 * x.2.2 +
      Q (transform Q (-x.2.1) x).2.1 = norm Q x at hn
    rw [hw, QuadraticMap.map_zero, add_zero, hb, mul_one] at hn
    exact hn
  apply Prod.ext
  · exact ha
  · apply Prod.ext
    · exact hw
    · exact hb

end SymmetricSubgroupAsymptotics.QuadraticHyperbolicRadicalClearing
