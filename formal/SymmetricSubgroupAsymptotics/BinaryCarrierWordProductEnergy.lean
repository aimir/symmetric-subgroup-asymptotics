import SymmetricSubgroupAsymptotics.BinaryCarrierTerminalFamily
import SymmetricSubgroupAsymptotics.BinaryCarrierUnitWeights
import SymmetricSubgroupAsymptotics.BinaryCarrierWordTerminalEnergy

/-! A reusable count of actual critical-plus-carrier product subgroups.
The input certifies every original normal history, and the order bound
discharges its multiplicity. Physical scales may vary between positions.
There is one terminal attachment, with the original survival test retained.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierWord

attribute [local instance] Fintype.ofFinite

/-- The full fixed-word bound, with explicit order, terminal and normal
multiplicity losses. The length counts original occurrences, whereas T
is their total physical scale. -/
def terminalProductReserve {ι : Type} [Fintype ι] (a : ℕ) (s : ι → Bool)
    (b length : ℕ) (T : ℝ) : ℝ :=
  (((binaryStructuredOrderConstant b *
    (b*length+2)^(binaryStructuredOrderConstant b) : ℕ) : ℝ)^length) *
    (((eulerProduct⁻¹)^3 * ((criticalProductRank a s+1 : ℕ) : ℝ) *
      (∑ ell ∈ Finset.range (Fintype.card ι+1), (72 : ℝ)^ell)) *
        ((2 : ℝ)^((2^b)*length) *
          (2 : ℝ)^(((criticalProductRank a s : ℝ)+4*T)^2/4 -
            (25/82)*(criticalProductRank a s)*T - (29/164)*T^2)))

/-- An unconditional internal normal count is used, rather than a count
of numerical labels. Each original tail is attached to the terminal once. -/
theorem terminal_subfamilies_le_reserve_of_orderBound
    {ι : Type} [Fintype ι] (a : ℕ) (s : ι → Bool)
    (w : List Factor) (b : ℕ) (hb : OrderBound w b)
    (T : ℝ) (cert : CertifiedHistoryRows w T)
    (P : ∀ H : Family w, Subgroup (CriticalProductGroup a s × H.1) → Prop) :
    (∑ H : Family w,
      (Nat.card {K : TerminalActualSubgroups a s H.1 // P H K.1} : ℝ)) ≤
        terminalProductReserve a s b w.length T := by
  have h := terminal_weighted_subfamilies_le_reserve a s w b hb
    (unitAxisWeights w) (unitAxisWeights_nonnegative w) P T cert
  simp only [weight_unitAxisWeights, one_mul] at h
  apply h.trans
  unfold terminalProductReserve
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
  apply mul_le_mul_of_nonneg_left _ (by positivity [euler_positive])
  exact mul_le_mul_of_nonneg_right
    (axisWeightProduct_unitAxisWeights_le_of_orderBound w b hb)
    (Real.rpow_nonneg (by norm_num) _)

/-- Count literal original product subgroups, preserving P through the
exact tail equivalence. Only individual specified projections are full. -/
theorem terminal_product_subgroups_le_reserve_of_orderBound
    {ι : Type} [Fintype ι] (a : ℕ) (s : ι → Bool)
    (w : List Factor) (b : ℕ) (hb : OrderBound w b)
    (T : ℝ) (cert : CertifiedHistoryRows w T)
    (P : Subgroup (CriticalProductGroup a s × Product w) → Prop) :
    (Nat.card (TerminalProductFamily a s w P) : ℝ) ≤
      terminalProductReserve a s b w.length T := by
  rw [terminalProductFamily_card_real]
  exact terminal_subfamilies_le_reserve_of_orderBound a s w b hb T cert
    (fun H J => P (J.map (SubdirectTailImage.inclusion H.1)))

end SymmetricSubgroupAsymptotics.BinaryCarrierWord
