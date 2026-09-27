import SymmetricSubgroupAsymptotics.BinaryMenuExponentAsymptotics

/-!
# A uniform numerical binary-menu exponent

The eventually valid quadratic estimate is extended over the finite initial
segment by summing the nonnegative excesses there. The resulting constant
depends only on the numerical exponent, including its value at zero.
No actual group menu or weighted counting estimate is asserted here.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

/-- A single nonnegative numerical constant handles all powers of two,
including the finite initial segment and k=0. -/
theorem binaryMenuExponent_uniform_le_one128 :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ k : ℕ,
      binaryMenuExponent k ≤ ((2 : ℝ)^k)^2/128 + H := by
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp
    binaryMenuExponent_eventually_le_one128
  let H : ℝ := ∑ j ∈ Finset.range K,
    max 0 (binaryMenuExponent j - ((2 : ℝ)^j)^2/128)
  have hH : 0 ≤ H := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  refine ⟨H,hH,?_⟩
  intro k
  by_cases hk : K ≤ k
  · exact (hK k hk).trans (le_add_of_nonneg_right hH)
  · have hterm : max 0 (binaryMenuExponent k - ((2 : ℝ)^k)^2/128) ≤ H :=
      Finset.single_le_sum
        (f := fun j : ℕ => max 0 (binaryMenuExponent j - ((2 : ℝ)^j)^2/128))
        (fun _ _ => le_max_left _ _)
        (Finset.mem_range.mpr (Nat.lt_of_not_ge hk))
    have hexcess : binaryMenuExponent k - ((2 : ℝ)^k)^2/128 ≤ H :=
      (le_max_right _ _).trans hterm
    linarith

end SymmetricSubgroupAsymptotics

end
