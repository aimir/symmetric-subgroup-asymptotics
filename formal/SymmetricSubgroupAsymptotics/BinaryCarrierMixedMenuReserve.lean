import SymmetricSubgroupAsymptotics.BinaryCarrierMixedMenuWord
import SymmetricSubgroupAsymptotics.BinaryCarrierWordProductEnergy

/-! Reserves for actual words mixing the literal J with the five masters.
The word itself supplies its physical scale and actual factor-order bound.
Weighted statements retain all original axis weights; the unweighted product
count uses the proved normal multiplicity bound and attaches terminals once. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierMixedMenuWord

open BinaryCarrierWord

theorem normalHistorySum_le_reserve (kinds : List Kind)
    (v : AxisWeights (word kinds)) (hv : WeightsNonnegative (word kinds) v)
    (R j ell : ℝ) (hj : 0 ≤ j ∧ j ≤ R) (hell : 0 ≤ ell ∧ ell ≤ R / 2) :
    (2 : ℝ) ^ (ell * (R / 2 - ell) + (j - ell) * (R - j)) *
        normalHistorySum (word kinds) v (j - ell) 0 ell ≤
      axisWeightProduct (word kinds) v *
        (2 : ℝ) ^ ((R + 4 * totalScale kinds) ^ 2 / 4 -
          (25 / 82) * R * totalScale kinds - (29 / 164) * (totalScale kinds) ^ 2) :=
  BinaryCarrierWord.normalHistorySum_le_reserve (word kinds) v hv (totalScale kinds)
    (certifiedHistoryRows kinds) R j ell hj hell

/-- Original normal multiplicities and arbitrary subgroup weights remain
visible; no count of labels or assumed total-weight estimate appears. -/
theorem markedSum_le_reserve (kinds : List Kind)
    (v : AxisWeights (word kinds)) (hv : WeightsNonnegative (word kinds) v)
    (P : Subgroup (Product (word kinds)) → Prop)
    (R j ell : ℝ) (hj : 0 ≤ j ∧ j ≤ R) (hell : 0 ≤ ell ∧ ell ≤ R / 2) :
    (2 : ℝ) ^ (ell * (R / 2 - ell) + (j - ell) * (R - j)) *
        markedSum (word kinds) v P (j - ell) 0 ell ≤
      (((binaryStructuredOrderConstant 12 *
        (12 * kinds.length + 2) ^ (binaryStructuredOrderConstant 12) : ℕ) : ℝ) ^
          kinds.length) * axisWeightProduct (word kinds) v *
        (2 : ℝ) ^ ((R + 4 * totalScale kinds) ^ 2 / 4 -
          (25 / 82) * R * totalScale kinds - (29 / 164) * (totalScale kinds) ^ 2) := by
  simpa only [word_length] using
    BinaryCarrierWord.markedSum_le_reserve_of_orderBound (word kinds) 12
      (orderBound kinds) v hv P (totalScale kinds) (certifiedHistoryRows kinds)
      R j ell hj hell

/-- Count actual subgroups of the original critical-plus-carrier product.
The literal subgroup predicate P survives the exact tail reconstruction;
no fullness of the entire critical product or physical normalizer bound is
introduced. There is one terminal attachment for each actual carrier tail. -/
theorem terminal_product_subgroups_le_reserve
    {ι : Type} [Fintype ι] (a : ℕ) (s : ι → Bool)
    (kinds : List Kind)
    (P : Subgroup (CriticalProductGroup a s × Product (word kinds)) → Prop) :
    (Nat.card (TerminalProductFamily a s (word kinds) P) : ℝ) ≤
      terminalProductReserve a s 12 kinds.length (totalScale kinds) := by
  simpa only [word_length] using
    BinaryCarrierWord.terminal_product_subgroups_le_reserve_of_orderBound
      a s (word kinds) 12 (orderBound kinds) (totalScale kinds)
        (certifiedHistoryRows kinds) P

end SymmetricSubgroupAsymptotics.BinaryCarrierMixedMenuWord
