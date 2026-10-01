import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveNumerics
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelToolkit
import SymmetricSubgroupAsymptotics.Non2PreE7SmallFactorModel

/-!
# Numerical totals for the reusable small-family models

The normal-comparator and factor-comparator constructions have the same
coefficient support on the literal normal menu.  Away from the bottom axis
the main coefficient is one and the tail coefficient is zero.  At the bottom
axis the normal model has only its fixed tail, while the factor model has its
fixed mixed coefficients.

This file proves those facts once.  A concrete family therefore only has to
bound the finite number of literal normal axes and its fixed bottom constants;
it never has to unfold the quotient construction used by the axis certificate.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

private abbrev NormalAxis {w : ℕ} (i : PreE7NonPairActionClass w) :=
  {N : Subgroup (preE7NonPairAction w i) // N.Normal}

namespace PreE7NormalComparatorModel

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (M : PreE7NormalComparatorModel w i)

theorem axis_mainCoefficient (N : NormalAxis i) :
    (M.axis N).mainCoefficient = if N.1 = ⊥ then 0 else 1 := by
  by_cases h : N.1 = ⊥ <;>
    simp [axis, h, PreE7SmallAxisCertificate.mainCoefficient]

theorem axis_tailCoefficient (N : NormalAxis i) :
    (M.axis N).tailCoefficient = if N.1 = ⊥ then M.tailConstant else 0 := by
  by_cases h : N.1 = ⊥ <;>
    simp [axis, h, PreE7SmallAxisCertificate.tailCoefficient]

theorem main_total_le_card (family : PreE7NoPairNoC3EarlierOwnerFamily) (b : ℕ) :
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
        ((M.toData.certificate family).C b) ≤ Nat.card (NormalAxis i) := by
  unfold fusionAxisEnvelopeTotal
  calc
    (∑ N : NormalAxis i, (M.toData.certificate family).C b N) ≤
        ∑ _N : NormalAxis i, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro N _
      change (M.axis N).mainCoefficient ≤ 1
      rw [M.axis_mainCoefficient N]
      split <;> norm_num
    _ = Nat.card (NormalAxis i) := by simp

theorem tail_total_eq (family : PreE7NoPairNoC3EarlierOwnerFamily) (b : ℕ) :
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
        ((M.toData.certificate family).tailCoefficient b) = M.tailConstant := by
  unfold fusionAxisEnvelopeTotal
  let B : NormalAxis i := ⟨⊥, inferInstance⟩
  calc
    (∑ N : NormalAxis i, (M.toData.certificate family).tailCoefficient b N) =
        ∑ N : NormalAxis i, if N = B then M.tailConstant else 0 := by
      apply Finset.sum_congr rfl
      intro N _
      change (M.axis N).tailCoefficient = _
      rw [M.axis_tailCoefficient N]
      congr 1
      exact propext ⟨fun hn => Subtype.ext hn, fun hn => by rw [hn]⟩
    _ = M.tailConstant := by simp [B]

/-- Package a normal-comparator model once its finite menu size and its one
bottom tail constant fit the common menu-mass scale. -/
def numericalData (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hmain : ∀ b,
      (Nat.card (NormalAxis i) : ℝ) ≤
        (2 : ℝ) ^ (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2))
    (htail : ∀ b,
      M.tailConstant ≤
        (2 : ℝ) ^ (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)) :
    PreE7SmallAdditiveNumericalData family w i where
  data := M.toData
  main_total_bound := fun b => (M.main_total_le_card family b).trans (hmain b)
  tail_total_bound := fun b => by rw [M.tail_total_eq family b]; exact htail b

end PreE7NormalComparatorModel

namespace PreE7FactorComparatorModel

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (M : PreE7FactorComparatorModel w i)

theorem axis_mainCoefficient (N : NormalAxis i) :
    (M.axis N).mainCoefficient = if N.1 = ⊥ then M.mainConstant else 1 := by
  by_cases h : N.1 = ⊥ <;>
    simp [axis, h, PreE7SmallAxisCertificate.mainCoefficient]

theorem axis_tailCoefficient (N : NormalAxis i) :
    (M.axis N).tailCoefficient = if N.1 = ⊥ then M.tailConstant else 0 := by
  by_cases h : N.1 = ⊥ <;>
    simp [axis, h, PreE7SmallAxisCertificate.tailCoefficient]

theorem main_total_le_card_add (family : PreE7NoPairNoC3EarlierOwnerFamily) (b : ℕ) :
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
        ((M.toData.certificate family).C b) ≤
      Nat.card (NormalAxis i) + M.mainConstant := by
  unfold fusionAxisEnvelopeTotal
  let B : NormalAxis i := ⟨⊥, inferInstance⟩
  calc
    (∑ N : NormalAxis i, (M.toData.certificate family).C b N) ≤
        ∑ N : NormalAxis i, ((1 : ℝ) + if N = B then M.mainConstant else 0) := by
      apply Finset.sum_le_sum
      intro N _
      change (M.axis N).mainCoefficient ≤ _
      rw [M.axis_mainCoefficient N]
      by_cases h : N = B
      · rw [h]
        rw [if_pos (show B.1 = ⊥ by rfl), if_pos rfl]
        linarith [M.mainConstant_nonneg]
      · have hbot : N.1 ≠ ⊥ := by
          intro hn
          apply h
          apply Subtype.ext
          exact hn
        simp [h, hbot]
    _ = Nat.card (NormalAxis i) + M.mainConstant := by
      simp [Finset.sum_add_distrib, B]

theorem tail_total_eq (family : PreE7NoPairNoC3EarlierOwnerFamily) (b : ℕ) :
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
        ((M.toData.certificate family).tailCoefficient b) = M.tailConstant := by
  unfold fusionAxisEnvelopeTotal
  let B : NormalAxis i := ⟨⊥, inferInstance⟩
  calc
    (∑ N : NormalAxis i, (M.toData.certificate family).tailCoefficient b N) =
        ∑ N : NormalAxis i, if N = B then M.tailConstant else 0 := by
      apply Finset.sum_congr rfl
      intro N _
      change (M.axis N).tailCoefficient = _
      rw [M.axis_tailCoefficient N]
      congr 1
      exact propext ⟨fun hn => Subtype.ext hn, fun hn => by rw [hn]⟩
    _ = M.tailConstant := by simp [B]

/-- Package a factor-comparator model once its finite menu and its two bottom
constants fit the common menu-mass scale. -/
def numericalData (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hmain : ∀ b,
      (Nat.card (NormalAxis i) : ℝ) + M.mainConstant ≤
        (2 : ℝ) ^ (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2))
    (htail : ∀ b,
      M.tailConstant ≤
        (2 : ℝ) ^ (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)) :
    PreE7SmallAdditiveNumericalData family w i where
  data := M.toData
  main_total_bound := fun b => (M.main_total_le_card_add family b).trans (hmain b)
  tail_total_bound := fun b => by rw [M.tail_total_eq family b]; exact htail b

end PreE7FactorComparatorModel

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
