import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveDegreeTwoExhaustion
import SymmetricSubgroupAsymptotics.TraceyBinaryFiveSixteenths

/-!
# Degree-four affine components whose order divides twelve

This is the exact numerical `A4` half of the local degree-four capacity
table.  The proof uses the literal component-order divisor, rather than an
abstract identification of the component.  Every block count is accepted
except `2,3,4,6,8,12,16,24`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem refinedWeightedFactorBudget_twelve (rate : ℕ → ℝ) :
    refinedWeightedFactorBudget rate 12 =
      rate 2 + fixedTargetCompositionGamma * rate 3 := by
  rw [show 12 = 2 ^ 2 * 3 ^ 1 by norm_num,
    refinedWeightedFactorBudget_mul rate (by norm_num) (by norm_num),
    refinedWeightedFactorBudget_prime_pow rate Nat.prime_two,
    refinedWeightedFactorBudget_prime_pow rate (by norm_num : Nat.Prime 3)]
  unfold fixedTargetCompositionGamma
  norm_num [Real.logb_self_eq_one]

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace ComponentSource

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
  (hTraceyLog : TraceyAffineInducedModuleInput)
  (hTraceyRefined : TraceyRefinedInducedModuleInput)
  (hTraceyPerm : TraceyPermutationGeneratorInput)
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

private abbrev blocks := Nat.card block.Points

private theorem blocks_ne_zero : blocks block ≠ 0 :=
  (Nat.card_pos (α := block.Points)).ne'

private theorem valuation_ge_of_pow_dvd
    {q d : ℕ} (hq : q.Prime) (hpow : q ^ d ∣ blocks block) :
    d ≤ (blocks block).factorization q := by
  exact (hq.pow_dvd_iff_le_factorization (blocks_ne_zero block)).mp hpow

private theorem width_even (hr : Nat.card block.Fibre = 4) : Even w := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  rw [width_eq block, hr]
  exact ⟨2 * Nat.card block.Points, by ring⟩

private theorem budget_twelve_largePrime
    (q e : ℕ) (hq5 : 5 ≤ q) (he : 1 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate (blocks block) q e) 12 ≤
      (49 / 160 : ℝ) * blocks block := by
  rw [refinedWeightedFactorBudget_twelve]
  have h2 := traceyPrimaryRate_nonmatching_le (blocks block) q e 2 5
    (by omega) (by
      calc 5 ≤ q := hq5
        _ = q ^ 1 := by simp
        _ ≤ q ^ e := Nat.pow_le_pow_right (by omega) he) (by norm_num)
  have h3 := traceyPrimaryRate_nonmatching_le (blocks block) q e 3 5
    (by omega) (by
      calc 5 ≤ q := hq5
        _ = q ^ 1 := by simp
        _ ≤ q ^ e := Nat.pow_le_pow_right (by omega) he) (by norm_num)
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hr3 := ActualWreathCompressionTower.traceyPrimaryRate_nonneg
    (blocks block) q e 3
  have h2' : ActualWreathCompressionTower.traceyPrimaryRate
      (blocks block) q e 2 ≤ (blocks block : ℝ) / 5 := by
    simpa only [blocks] using h2
  have h3' : ActualWreathCompressionTower.traceyPrimaryRate
      (blocks block) q e 3 ≤ (blocks block : ℝ) / 5 := by
    simpa only [blocks] using h3
  calc
    _ ≤ (blocks block : ℝ) / 5 +
        (17 / 32 : ℝ) * ((blocks block : ℝ) / 5) := by gcongr
    _ = (49 / 160 : ℝ) * blocks block := by ring

noncomputable def of_degreeFour_twelve_largePrime
    (hr : Nat.card block.Fibre = 4)
    (hcomponent : Nat.card block.Component ∣ 12)
    (q e : ℕ) (hq : q.Prime) (hq5 : 5 ≤ q)
    (he : 1 ≤ e) (hdiv : q ^ e ∣ blocks block)
    (hmax : ¬ q ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P q e 12 hq he hdiv hmax (by norm_num) hcomponent
  apply smallAffine_even_budget_margin 4 (blocks block) w
      (by simpa only [hr] using width_eq block) (width_even block hr)
      (49 / 160) _
  · unfold preE7CharacterRho
    norm_num
  · exact budget_twelve_largePrime block q e hq5 he

private theorem budget_twelve_ternaryTwo
    (e : ℕ) (he : 2 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate (blocks block) 3 e) 12 ≤
      (383 / 1152 : ℝ) * blocks block := by
  rw [refinedWeightedFactorBudget_twelve]
  have hpow : 9 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num : 0 < 3) he
  have h2 := traceyPrimaryRate_nonmatching_le (blocks block) 3 e 2 9
    (by norm_num) hpow (by norm_num)
  have h3 := traceyPrimaryRate_three_matching_of_two_le (blocks block) e he
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hr3 := ActualWreathCompressionTower.traceyPrimaryRate_nonneg
    (blocks block) 3 e 3
  have h2' : ActualWreathCompressionTower.traceyPrimaryRate
      (blocks block) 3 e 2 ≤ (blocks block : ℝ) / 9 := by
    simpa only [blocks] using h2
  calc
    _ ≤ (blocks block : ℝ) / 9 +
        (17 / 32 : ℝ) * ((blocks block : ℝ) * (5 / 12)) := by gcongr
    _ = (383 / 1152 : ℝ) * blocks block := by ring

noncomputable def of_degreeFour_twelve_ternaryTwo
    (hr : Nat.card block.Fibre = 4)
    (hcomponent : Nat.card block.Component ∣ 12)
    (e : ℕ) (he : 2 ≤ e) (hdiv : 3 ^ e ∣ blocks block)
    (hmax : ¬ 3 ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P 3 e 12 (by norm_num) (by omega) hdiv hmax (by norm_num) hcomponent
  apply smallAffine_even_budget_margin 4 (blocks block) w
      (by simpa only [hr] using width_eq block) (width_even block hr)
      (383 / 1152) _
  · unfold preE7CharacterRho
    norm_num
  · exact budget_twelve_ternaryTwo block e he

private def degreeFourMixedRate (s e₂ e₃ p : ℕ) : ℝ :=
  min (ActualWreathCompressionTower.traceyPrimaryRate s 2 e₂ p)
    (ActualWreathCompressionTower.traceyPrimaryRate s 3 e₃ p)

private theorem budget_twelve_mixed_sixteenThree
    (e₂ e₃ : ℕ) (he₂ : 4 ≤ e₂) (he₃ : 1 ≤ e₃) :
    refinedWeightedFactorBudget
        (degreeFourMixedRate (blocks block) e₂ e₃) 12 ≤
      (563 / 1536 : ℝ) * blocks block := by
  rw [refinedWeightedFactorBudget_twelve]
  have h2 : degreeFourMixedRate (blocks block) e₂ e₃ 2 ≤
      (blocks block : ℝ) / 3 :=
    (min_le_right _ _).trans
      (traceyPrimaryRate_nonmatching_le (blocks block) 3 e₃ 2 3
        (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 3) he₃)
        (by norm_num))
  have h3 : degreeFourMixedRate (blocks block) e₂ e₃ 3 ≤
      (blocks block : ℝ) / 16 :=
    (min_le_left _ _).trans
      (traceyPrimaryRate_nonmatching_le (blocks block) 2 e₂ 3 16
        (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 2) he₂)
        (by norm_num))
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hr3 : 0 ≤ degreeFourMixedRate (blocks block) e₂ e₃ 3 := le_min
    (ActualWreathCompressionTower.traceyPrimaryRate_nonneg _ _ _ _)
    (ActualWreathCompressionTower.traceyPrimaryRate_nonneg _ _ _ _)
  calc
    _ ≤ (blocks block : ℝ) / 3 +
        (17 / 32 : ℝ) * ((blocks block : ℝ) / 16) := by gcongr
    _ = (563 / 1536 : ℝ) * blocks block := by ring

noncomputable def of_degreeFour_twelve_mixed_sixteenThree
    (hr : Nat.card block.Fibre = 4)
    (hcomponent : Nat.card block.Component ∣ 12)
    (e₂ e₃ : ℕ) (he₂ : 4 ≤ e₂) (he₃ : 1 ≤ e₃)
    (hdiv₂ : 2 ^ e₂ ∣ blocks block) (hmax₂ : ¬ 2 ^ (e₂ + 1) ∣ blocks block)
    (hdiv₃ : 3 ^ e₃ ∣ blocks block) (hmax₃ : ¬ 3 ^ (e₃ + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_twoTraceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P 2 e₂ 3 e₃ 12 Nat.prime_two (by omega) hdiv₂ hmax₂
      (by norm_num) he₃ hdiv₃ hmax₃ (by norm_num) hcomponent
  apply smallAffine_even_budget_margin 4 (blocks block) w
      (by simpa only [hr] using width_eq block) (width_even block hr)
      (563 / 1536) _
  · unfold preE7CharacterRho
    norm_num
  · simpa only [degreeFourMixedRate] using
      budget_twelve_mixed_sixteenThree block e₂ e₃ he₂ he₃

private theorem primePowerRate_two_five
    (e : ℕ) (he : 5 ≤ e) :
    ActualWreathCompressionTower.traceyPrimePowerRate 2 e 2 ≤
      (5 / 16 : ℝ) * (2 ^ e : ℕ) := by
  unfold ActualWreathCompressionTower.traceyPrimePowerRate
  rw [if_pos rfl]
  simp only [Nat.reduceSubDiff, Nat.mul_one]
  have hmiddle : (16 : ℝ) * (e.choose (e / 2) : ℝ) ≤
      5 * (2 : ℝ) ^ e := by
    exact_mod_cast binary_middle_le_five_sixteenths e he
  have hp : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  norm_num [Nat.cast_pow] at hmiddle ⊢
  field_simp
  nlinarith

private theorem budget_twelve_binaryPrimePowerFive
    (e : ℕ) (he : 5 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimePowerRate 2 e) 12 ≤
      (337 / 1024 : ℝ) * (2 ^ e : ℕ) := by
  rw [refinedWeightedFactorBudget_twelve]
  have h2 := primePowerRate_two_five e he
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hs32 : (32 : ℝ) ≤ (2 ^ e : ℕ) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) he
  have h3 : ActualWreathCompressionTower.traceyPrimePowerRate 2 e 3 = 1 := by
    simp [ActualWreathCompressionTower.traceyPrimePowerRate]
  rw [h3]
  simp only [mul_one]
  calc
    _ ≤ (5 / 16 : ℝ) * (2 ^ e : ℕ) + 17 / 32 :=
      add_le_add h2 hgamma
    _ ≤ (337 / 1024 : ℝ) * (2 ^ e : ℕ) := by nlinarith

noncomputable def of_degreeFour_twelve_binaryPrimePowerFive
    (hr : Nat.card block.Fibre = 4)
    (hcomponent : Nat.card block.Component ∣ 12)
    (e : ℕ) (he : 5 ≤ e) (hs : blocks block = 2 ^ e) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimePower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P 2 e 12 Nat.prime_two (by omega) hs (by norm_num) hcomponent
  apply smallAffine_even_budget_margin 4 (blocks block) w
      (by simpa only [hr] using width_eq block) (width_even block hr)
      (337 / 1024) _
  · unfold preE7CharacterRho
    norm_num
  · rw [hs]
    exact budget_twelve_binaryPrimePowerFive e he

/-- Degree-four/order-twelve exhaustion: every block count is accepted
except `2,3,4,6,8,12,16,24`. -/
noncomputable def degreeFourTwelveExhaustion
    (hr : Nat.card block.Fibre = 4)
    (hcomponent : Nat.card block.Component ∣ 12) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P ⊕
      PLift (blocks block = 2 ∨ blocks block = 3 ∨ blocks block = 4 ∨
        blocks block = 6 ∨ blocks block = 8 ∨ blocks block = 12 ∨
        blocks block = 16 ∨ blocks block = 24) := by
  by_cases hlarge : ∃ q : ℕ, q.Prime ∧ q ∣ blocks block ∧ 5 ≤ q
  · let q := Classical.choose hlarge
    have hqdata := Classical.choose_spec hlarge
    let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      hqdata.1 hqdata.2.1
    exact .inl (of_degreeFour_twelve_largePrime hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm block P hr hcomponent q E.e hqdata.1
        hqdata.2.2 E.one_le E.pow_dvd E.pow_succ_not_dvd)
  by_cases h9 : 3 ^ 2 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      (by norm_num : Nat.Prime 3) (dvd_trans (by norm_num : 3 ∣ 3 ^ 2) h9)
    have he : 2 ≤ E.e := by
      simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
        (valuation_ge_of_pow_dvd block (by norm_num : Nat.Prime 3) h9)
    exact .inl (of_degreeFour_twelve_ternaryTwo hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm block P hr hcomponent E.e he E.pow_dvd
        E.pow_succ_not_dvd)
  by_cases h3 : 3 ∣ blocks block
  · by_cases h16 : 2 ^ 4 ∣ blocks block
    · let E₂ := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
        Nat.prime_two (dvd_trans (by norm_num : 2 ∣ 2 ^ 4) h16)
      let E₃ := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
        (by norm_num : Nat.Prime 3) h3
      have he₂ : 4 ≤ E₂.e := by
        simpa only [E₂, ExactPrimaryDivisor.ofPrimeDvd] using
          (valuation_ge_of_pow_dvd block Nat.prime_two h16)
      exact .inl (of_degreeFour_twelve_mixed_sixteenThree hTraceyHalf
        hTraceyLog hTraceyRefined hTraceyPerm block P hr hcomponent
          E₂.e E₃.e he₂ E₃.one_le E₂.pow_dvd E₂.pow_succ_not_dvd
            E₃.pow_dvd E₃.pow_succ_not_dvd)
    · have hdvd : blocks block ∣ 2 ^ 3 * 3 ^ 1 :=
        dvd_binary_ternary_bounded (blocks_ne_zero block) hlarge h16 h9
      have hs2 : 2 ≤ blocks block := block.degrees_ge_two.2
      have hs24 : blocks block ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases hs : blocks block
      all_goals norm_num at hdvd
      all_goals norm_num at h3
      all_goals exact .inr ⟨by simp⟩
  · by_cases h32 : 2 ^ 5 ∣ blocks block
    · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
        Nat.prime_two (dvd_trans (by norm_num : 2 ∣ 2 ^ 5) h32)
      have he : 5 ≤ E.e := by
        simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
          (valuation_ge_of_pow_dvd block Nat.prime_two h32)
      have hdvd : blocks block ∣ 2 ^ E.e := by
        simpa only [pow_zero, mul_one] using
          (dvd_binary_ternary_bounded (a := E.e) (b := 0)
            (blocks_ne_zero block) hlarge E.pow_succ_not_dvd
              (by simpa only [Nat.zero_add, pow_one] using h3))
      have hs : blocks block = 2 ^ E.e := Nat.dvd_antisymm hdvd E.pow_dvd
      exact .inl (of_degreeFour_twelve_binaryPrimePowerFive hTraceyHalf
        hTraceyLog hTraceyRefined hTraceyPerm block P hr hcomponent E.e he hs)
    · have hdvd : blocks block ∣ 2 ^ 4 := by
        simpa only [pow_zero, mul_one] using
          (dvd_binary_ternary_bounded (a := 4) (b := 0)
            (blocks_ne_zero block) hlarge h32
              (by simpa only [Nat.zero_add, pow_one] using h3))
      have hs2 : 2 ≤ blocks block := block.degrees_ge_two.2
      have hs16 : blocks block ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases hs : blocks block
      all_goals norm_num at hdvd
      all_goals exact .inr ⟨by simp⟩

end ComponentSource
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
