import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.NoncommRing

/-! Explicit integral commutator formulas for a square-zero root matrix.
These are target-side identities, not an injectivity assertion for a Serre
quotient and not a uniform adjoint bound on the source model. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSquareZeroAdjoint
variable {B : Type*} [Ring B]

theorem lie_lie (e x : B) (he : e * e = 0) :
    ⁅e, ⁅e, x⁆⁆ = -(e * x * e + e * x * e) := by
  have h : ⁅e, ⁅e, x⁆⁆ = (e * e) * x - (e * x * e + e * x * e) + x * (e * e) := by
    simp only [Ring.lie_def]
    noncomm_ring
  rw [h, he, zero_mul, mul_zero, zero_sub, add_zero]

theorem lie_lie_lie (e x : B) (he : e * e = 0) : ⁅e, ⁅e, ⁅e, x⁆⁆⁆ = 0 := by
  have hl : e * (e * x * e) = 0 := by
    calc
      e * (e * x * e) = (e * e) * x * e := by noncomm_ring
      _ = 0 := by rw [he, zero_mul, zero_mul]
  have hr : e * x * e * e = 0 := by
    calc
      e * x * e * e = e * x * (e * e) := by noncomm_ring
      _ = 0 := by rw [he, mul_zero]
  rw [lie_lie e x he]
  simp only [Ring.lie_def, mul_neg, neg_mul, mul_add, add_mul, hl, hr,
    add_zero, neg_zero, sub_self]

end SymmetricSubgroupAsymptotics.CFSGSquareZeroAdjoint
