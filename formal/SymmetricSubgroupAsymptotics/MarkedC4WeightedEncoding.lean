import SymmetricSubgroupAsymptotics.MarkedC4GenerationExtension

/-!
# Weighted finite encodings for the marked `C4` moment

The unmarked Roney-Dougal--Tracey reductions encode each source object by a
bounded-word object, with a uniform bound on every encoding fibre.  Marks are
transported along the same encoding.  This file records the elementary joint
summation step: the fibre multiplicity and the mark-extension cost are charged
together before summing over encoded objects.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

/-- A finite encoding with fibres of size at most `M` transports a pointwise
weight bound with factor `C` to the corresponding bound on total weights. -/
theorem sum_le_uniformFiber_mul_sum
    {A B : Type*} [Fintype A] [Fintype B]
    (code : A → B) (sourceWeight : A → ℝ) (targetWeight : B → ℝ)
    (M : ℕ) (C : ℝ)
    (hpoint : ∀ a, sourceWeight a ≤ C * targetWeight (code a))
    (hC : 0 ≤ C) (htarget : ∀ b, 0 ≤ targetWeight b)
    (hfibre : ∀ b, Fintype.card {a : A // code a = b} ≤ M) :
    (∑ a, sourceWeight a) ≤ (M : ℝ) * C * ∑ b, targetWeight b := by
  calc
    (∑ a, sourceWeight a) =
        ∑ b, ∑ a : {a : A // code a = b}, sourceWeight a.1 := by
      exact (Fintype.sum_fiberwise code sourceWeight).symm
    _ ≤ ∑ b, ∑ _a : {a : A // code a = b}, C * targetWeight b := by
      apply Finset.sum_le_sum
      intro b hb
      apply Finset.sum_le_sum
      intro a ha
      simpa [a.2] using hpoint a.1
    _ = ∑ b, (Fintype.card {a : A // code a = b} : ℝ) *
          (C * targetWeight b) := by
      apply Finset.sum_congr rfl
      intro b hb
      simp [nsmul_eq_mul]
    _ ≤ ∑ b, (M : ℝ) * (C * targetWeight b) := by
      apply Finset.sum_le_sum
      intro b hb
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hfibre b
      · exact mul_nonneg hC (htarget b)
    _ = (M : ℝ) * C * ∑ b, targetWeight b := by
      rw [Finset.mul_sum]
      congr 1
      funext b
      ring

/-- The same transport when the pointwise cost is a power of two. -/
theorem sum_le_uniformFiber_mul_twoPow_mul_sum
    {A B : Type*} [Fintype A] [Fintype B]
    (code : A → B) (sourceWeight : A → ℝ) (targetWeight : B → ℝ)
    (M e : ℕ)
    (hpoint : ∀ a, sourceWeight a ≤ (2 : ℝ) ^ e * targetWeight (code a))
    (htarget : ∀ b, 0 ≤ targetWeight b)
    (hfibre : ∀ b, Fintype.card {a : A // code a = b} ≤ M) :
    (∑ a, sourceWeight a) ≤
      (M : ℝ) * (2 : ℝ) ^ e * ∑ b, targetWeight b := by
  exact sum_le_uniformFiber_mul_sum code sourceWeight targetWeight M
    ((2 : ℝ) ^ e) hpoint (by positivity) htarget hfibre

end MarkedC4
end SymmetricSubgroupAsymptotics
