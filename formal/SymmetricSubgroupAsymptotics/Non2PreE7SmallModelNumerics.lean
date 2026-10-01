import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveNumerics
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelToolkit
import SymmetricSubgroupAsymptotics.Non2PreE7SmallFactorModel
import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailSource

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

/-! ## Uniform finite bounds -/

/-- Literal normal subgroups inject into subsets of the underlying group. -/
theorem normalAxis_card_le_two_pow_card (G : Type*) [Group G] [Finite G] :
    Nat.card {N : Subgroup G // N.Normal} ≤ 2 ^ Nat.card G := by
  letI : Fintype G := Fintype.ofFinite G
  let f : {N : Subgroup G // N.Normal} → Set G := fun N => N.1
  have hf : Function.Injective f := by
    intro N K h
    apply Subtype.ext
    exact SetLike.coe_injective h
  calc
    Nat.card {N : Subgroup G // N.Normal} ≤ Nat.card (Set G) :=
      Nat.card_le_card_of_injective f hf
    _ = 2 ^ Nat.card G := by
      rw [Nat.card_eq_fintype_card, Fintype.card_set, Nat.card_eq_fintype_card]

/-- An automorphism is determined by a generating set of size at most the
base-two logarithm of the group order. -/
theorem mulEquiv_card_le_card_pow_log (G : Type*) [Group G] [Finite G] :
    Nat.card (G ≃* G) ≤ Nat.card G ^ Nat.log 2 (Nat.card G) := by
  obtain ⟨S, hS, hpow⟩ := exists_generating_finset_two_pow_le G
  have hsize : S.card ≤ Nat.log 2 (Nat.card G) :=
    Nat.le_log_of_pow_le (by norm_num) hpow
  letI : Finite (G →* G) := Finite.of_injective
    (fun f : G →* G => (f : G → G)) DFunLike.coe_injective
  have hautHom : Nat.card (G ≃* G) ≤ Nat.card (G →* G) := by
    exact Nat.card_le_card_of_injective (fun e : G ≃* G => e.toMonoidHom)
      (fun _ _ h => MulEquiv.ext (fun g => DFunLike.congr_fun h g))
  exact hautHom.trans ((monoidHom_card_le_pow_of_closure S hS).trans
    (Nat.pow_le_pow_right Nat.card_pos hsize))

theorem mulEquiv_card_cast_le_card_pow_log (G : Type*) [Group G] [Finite G] :
    (Nat.card (G ≃* G) : ℝ) ≤
      (Nat.card G : ℝ) ^ Nat.log 2 (Nat.card G) := by
  exact_mod_cast mulEquiv_card_le_card_pow_log G

/-- The completely elementary fallback: forget the homomorphism structure
and regard an automorphism as a function on the underlying finite group. -/
theorem mulEquiv_card_le_card_pow_card (G : Type*) [Group G] [Finite G] :
    Nat.card (G ≃* G) ≤ Nat.card G ^ Nat.card G := by
  letI : Fintype G := Fintype.ofFinite G
  calc
    Nat.card (G ≃* G) ≤ Nat.card (G → G) :=
      Nat.card_le_card_of_injective (fun e : G ≃* G => (e : G → G))
        (fun _ _ h => MulEquiv.ext (fun g => congrFun h g))
    _ = Nat.card G ^ Nat.card G := by
      rw [Nat.card_fun]

/-- At widths at least four, the common coefficient envelope dominates
`2^(16w)`, uniformly in the complement degree. -/
theorem two_rpow_sixteen_width_le_menuMass {w : ℕ} (hw : 4 ≤ w) (b : ℕ) :
    (2 : ℝ) ^ (16 * (w : ℝ)) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have harg : (3 : ℝ) < ((w + b + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 3 < w + b + 2 by omega)
  have hlog : (1 : ℝ) ≤ Real.log ((w + b + 2 : ℕ) : ℝ) := by
    exact ((Real.lt_log_iff_exp_lt (by positivity)).2
      (Real.exp_one_lt_three.trans harg)).le
  have hw0 : (0 : ℝ) ≤ w := by positivity
  nlinarith [sq_nonneg (Real.log ((w + b + 2 : ℕ) : ℝ) - 1)]

/-- The sharper width-four lower envelope obtained from `log 6 > 3/2`. -/
theorem two_rpow_thirtySix_width_le_menuMass {w : ℕ} (hw : 4 ≤ w) (b : ℕ) :
    (2 : ℝ) ^ (36 * (w : ℝ)) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hhalfSq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    norm_num
  have hhalf : Real.exp (1 / 2 : ℝ) < 2 := by
    nlinarith [Real.exp_pos (1 / 2 : ℝ), Real.exp_one_lt_three]
  have hthreeHalf : Real.exp (3 / 2 : ℝ) < 6 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.exp_add]
    convert mul_lt_mul_of_pos' Real.exp_one_lt_three hhalf
      (Real.exp_pos _) (by norm_num) using 1 <;> norm_num
  have harg : (6 : ℝ) ≤ ((w + b + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 6 ≤ w + b + 2 by omega)
  have hlog : (3 / 2 : ℝ) ≤ Real.log ((w + b + 2 : ℕ) : ℝ) := by
    exact ((Real.lt_log_iff_exp_lt (by positivity)).2
      (hthreeHalf.trans_le harg)).le
  have hw0 : (0 : ℝ) ≤ w := by positivity
  nlinarith [sq_nonneg (Real.log ((w + b + 2 : ℕ) : ℝ) - 3 / 2)]

/-- At widths at least eight, the same envelope dominates `2^(64w)`. -/
theorem two_rpow_sixtyFour_width_le_menuMass {w : ℕ} (hw : 8 ≤ w) (b : ℕ) :
    (2 : ℝ) ^ (64 * (w : ℝ)) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hexpTwo : Real.exp (2 : ℝ) < 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos 1, Real.exp_one_lt_three]
  have harg : (9 : ℝ) < ((w + b + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 9 < w + b + 2 by omega)
  have hlog : (2 : ℝ) ≤ Real.log ((w + b + 2 : ℕ) : ℝ) := by
    exact ((Real.lt_log_iff_exp_lt (by positivity)).2 (hexpTwo.trans harg)).le
  have hw0 : (0 : ℝ) ≤ w := by positivity
  nlinarith [sq_nonneg (Real.log ((w + b + 2 : ℕ) : ℝ) - 2)]

namespace PreE7NormalComparatorModel

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (M : PreE7NormalComparatorModel w i)

theorem normalAxis_card_le_modelPow :
    Nat.card (NormalAxis i) ≤ 2 ^ Nat.card M.G := by
  calc
    Nat.card (NormalAxis i) ≤
        2 ^ Nat.card (preE7NonPairAction w i) :=
      normalAxis_card_le_two_pow_card _
    _ = 2 ^ Nat.card M.G := by
      rw [Nat.card_congr M.equiv.toEquiv]

theorem normalAxis_card_cast_le_modelRpow :
    (Nat.card (NormalAxis i) : ℝ) ≤ (2 : ℝ) ^ (Nat.card M.G : ℝ) := by
  calc
    (Nat.card (NormalAxis i) : ℝ) ≤ ((2 ^ Nat.card M.G : ℕ) : ℝ) := by
      exact_mod_cast M.normalAxis_card_le_modelPow
    _ = (2 : ℝ) ^ (Nat.card M.G : ℝ) := by
      rw [Real.rpow_natCast]
      norm_num

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

theorem normalAxis_card_le_modelPow :
    Nat.card (NormalAxis i) ≤ 2 ^ Nat.card M.G := by
  calc
    Nat.card (NormalAxis i) ≤
        2 ^ Nat.card (preE7NonPairAction w i) :=
      normalAxis_card_le_two_pow_card _
    _ = 2 ^ Nat.card M.G := by
      rw [Nat.card_congr M.equiv.toEquiv]

theorem normalAxis_card_cast_le_modelRpow :
    (Nat.card (NormalAxis i) : ℝ) ≤ (2 : ℝ) ^ (Nat.card M.G : ℝ) := by
  calc
    (Nat.card (NormalAxis i) : ℝ) ≤ ((2 ^ Nat.card M.G : ℕ) : ℝ) := by
      exact_mod_cast M.normalAxis_card_le_modelPow
    _ = (2 : ℝ) ^ (Nat.card M.G : ℝ) := by
      rw [Real.rpow_natCast]
      norm_num

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
