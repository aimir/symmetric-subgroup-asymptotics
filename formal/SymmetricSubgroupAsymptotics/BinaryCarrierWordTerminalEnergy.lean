import SymmetricSubgroupAsymptotics.BinaryCarrierWordEnergy
import SymmetricSubgroupAsymptotics.BinaryCarrierWordTerminal
import SymmetricSubgroupAsymptotics.BinaryCarrierTerminalCoefficient

/-! The numerical reserve for one terminal attachment to a complete
certified carrier word. The remaining finite terminal factor, polynomial
loss and original normal-weight mass are explicit, before any asymptotic
profile summation or owner-acceptance argument.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierWord

open BinaryMarkedTerminalAttachment

attribute [local instance] Fintype.ofFinite

/-- Sum the full terminal rectangle against the actual carrier-history
bound. The 72^ell loss is retained explicitly, including the empty word. -/
theorem terminal_history_sum_le_reserve
    (w : List Factor) (v : AxisWeights w) (hv : WeightsNonnegative w v)
    (T : ℝ) (cert : CertifiedHistoryRows w T) (r c : ℕ) (hc : 2*c ≤ r) :
    (∑ j ∈ Finset.range (r+1), ∑ ell ∈ Finset.range (c+1),
      coefficient r c j ell * normalHistorySum w v ((j : ℝ)-ell) 0 ell) ≤
      ((eulerProduct⁻¹)^3 * ((r+1 : ℕ) : ℝ) *
        (∑ ell ∈ Finset.range (c+1), (72 : ℝ)^ell)) *
          (axisWeightProduct w v *
            (2 : ℝ)^(((r : ℝ)+4*T)^2/4 - (25/82)*r*T - (29/164)*T^2)) := by
  have hterm (j ell : ℕ) (hj : j ≤ r) (hell : ell ≤ c) :
      coefficient r c j ell * normalHistorySum w v ((j : ℝ)-ell) 0 ell ≤
        (eulerProduct⁻¹)^3 * (72 : ℝ)^ell *
          (axisWeightProduct w v *
            (2 : ℝ)^(((r : ℝ)+4*T)^2/4 - (25/82)*r*T - (29/164)*T^2)) := by
    have hjR : 0 ≤ (j : ℝ) ∧ (j : ℝ) ≤ r :=
      ⟨Nat.cast_nonneg _, Nat.cast_le.mpr hj⟩
    have hellR : 0 ≤ (ell : ℝ) ∧ (ell : ℝ) ≤ (r : ℝ)/2 := by
      have he : 2*ell ≤ r := (Nat.mul_le_mul_left 2 hell).trans hc
      have heR : (2 : ℝ)*ell ≤ r := by exact_mod_cast he
      exact ⟨Nat.cast_nonneg _, by linarith⟩
    calc
      _ ≤ ((eulerProduct⁻¹)^3 * (72 : ℝ)^ell *
          (2 : ℝ)^((ell : ℝ)*((r : ℝ)/2-ell)+((j : ℝ)-ell)*((r : ℝ)-j))) *
            normalHistorySum w v ((j : ℝ)-ell) 0 ell :=
        mul_le_mul_of_nonneg_right (coefficient_le_energy_base r c j ell hell hc)
          (normalHistorySum_nonneg w v hv _ _ _)
      _ = ((eulerProduct⁻¹)^3 * (72 : ℝ)^ell) *
          ((2 : ℝ)^((ell : ℝ)*((r : ℝ)/2-ell)+((j : ℝ)-ell)*((r : ℝ)-j)) *
            normalHistorySum w v ((j : ℝ)-ell) 0 ell) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (normalHistorySum_le_reserve w v hv T cert r j ell hjR hellR)
        (by positivity [euler_positive])
  calc
    _ ≤ ∑ j ∈ Finset.range (r+1), ∑ ell ∈ Finset.range (c+1),
        (eulerProduct⁻¹)^3 * (72 : ℝ)^ell *
          (axisWeightProduct w v *
            (2 : ℝ)^(((r : ℝ)+4*T)^2/4 - (25/82)*r*T - (29/164)*T^2)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro ell hell
      exact hterm j ell (by simpa using hj) (by simpa using hell)
    _ = _ := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      ring

/-- A derived complete weighted sum over actual terminal fibres, with the
quadratic deficit displayed. All row certificates and physical weight
identifications remain visible; this is not a catalogue-completeness claim. -/
theorem terminal_weighted_subfamilies_le_reserve
    {ι : Type} [Fintype ι] (a : ℕ) (s : ι → Bool)
    (w : List Factor) (b : ℕ) (hb : OrderBound w b)
    (v : AxisWeights w) (hv : WeightsNonnegative w v)
    (P : ∀ H : Family w, Subgroup (CriticalProductGroup a s × H.1) → Prop)
    (T : ℝ) (cert : CertifiedHistoryRows w T) :
    (∑ H : Family w, weight w v H *
      (Nat.card {K : TerminalActualSubgroups a s H.1 // P H K.1} : ℝ)) ≤
      (((binaryStructuredOrderConstant b *
        (b*w.length+2)^(binaryStructuredOrderConstant b) : ℕ) : ℝ)^w.length) *
        (((eulerProduct⁻¹)^3 * ((criticalProductRank a s+1 : ℕ) : ℝ) *
          (∑ ell ∈ Finset.range (Fintype.card ι+1), (72 : ℝ)^ell)) *
            (axisWeightProduct w v *
              (2 : ℝ)^(((criticalProductRank a s : ℝ)+4*T)^2/4 -
                (25/82)*(criticalProductRank a s)*T - (29/164)*T^2))) := by
  let D : ℝ := (((binaryStructuredOrderConstant b *
    (b*w.length+2)^(binaryStructuredOrderConstant b) : ℕ) : ℝ)^w.length)
  have hD : 0 ≤ D := pow_nonneg (Nat.cast_nonneg _) _
  calc
    _ ≤ ∑ j ∈ Finset.range (criticalProductRank a s+1),
        ∑ ell ∈ Finset.range (Fintype.card ι+1),
          coefficient (criticalProductRank a s) (Fintype.card ι) j ell *
            (D * normalHistorySum w v ((j : ℝ)-ell) 0 ell) :=
      terminal_weighted_subfamilies_le_history a s w b hb v hv P
    _ = D * (∑ j ∈ Finset.range (criticalProductRank a s+1),
        ∑ ell ∈ Finset.range (Fintype.card ι+1),
          coefficient (criticalProductRank a s) (Fintype.card ι) j ell *
            normalHistorySum w v ((j : ℝ)-ell) 0 ell) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ell _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (terminal_history_sum_le_reserve w v hv T cert (criticalProductRank a s)
        (Fintype.card ι) (terminalCritical_two_card_le_rank a s)) hD

end SymmetricSubgroupAsymptotics.BinaryCarrierWord
