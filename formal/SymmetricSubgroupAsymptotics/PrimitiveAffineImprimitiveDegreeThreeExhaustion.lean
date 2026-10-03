import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallExhaustion

/-!
# Exact degree-three affine component exhaustion

For a primitive affine component on three points the literal component order
divides six.  Tracey's retained primary capacities therefore close every
actual block count except `2,3,4,6,8,12,18`.  This is the exact numerical
list in the manuscript's regular-`C3`/natural-`S3` capacity theorem, proved
here without classifying the component as either abstract group.

The count nine uses the integral capacity of the actual chief tower.  Mixed
binary/ternary counts use both literal primary divisors simultaneously.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Margin conversion retaining the exact lower bound on the block count.
The only possible parity loss is one point, hence `1/(8*c)` pays it when
`c <= s`. -/
theorem smallAffine_budget_margin_of_lower
    (r s w c : ℕ) (hc : 1 ≤ c) (hcs : c ≤ s) (hw : w = r * s)
    (k eta : ℝ)
    (hnum :
      Non2UnipotentPrefixFiniteMenu.preE7CharacterRho * (r : ℝ) + k +
          1 / (8 * (c : ℝ)) ≤ ((r : ℝ) - 1) / 8)
    (heta : eta ≤ k * s) :
    Non2UnipotentPrefixFiniteMenu.preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - s) / 8 - eta := by
  have heven : (w : ℝ) ≤ evenWidth w + 1 := by
    exact_mod_cast width_le_evenWidth_add_one w
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hsR : (c : ℝ) ≤ s := by exact_mod_cast hcs
  have hpay : (1 : ℝ) / 8 ≤ (s : ℝ) / (8 * (c : ℝ)) := by
    calc
      (1 : ℝ) / 8 = (c : ℝ) / (8 * (c : ℝ)) := by field_simp
      _ ≤ (s : ℝ) / (8 * (c : ℝ)) := by
        exact div_le_div_of_nonneg_right hsR (by positivity)
  have hwR : (w : ℝ) = r * s := by exact_mod_cast hw
  rw [hwR] at heven ⊢
  have hspos : (0 : ℝ) < s := lt_of_lt_of_le hcR hsR
  have hscaled := mul_le_mul_of_nonneg_right hnum (le_of_lt hspos)
  ring_nf at heven heta hpay hscaled ⊢
  nlinarith

/-- With no prime at least five and bounded binary and ternary valuations,
the block count divides `2^a * 3^b`. -/
theorem dvd_binary_ternary_bounded
    {s a b : ℕ} (hs : s ≠ 0)
    (hlarge : ¬ ∃ q : ℕ, q.Prime ∧ q ∣ s ∧ 5 ≤ q)
    (h2 : ¬ 2 ^ (a + 1) ∣ s) (h3 : ¬ 3 ^ (b + 1) ∣ s) :
    s ∣ 2 ^ a * 3 ^ b := by
  rw [← Nat.factorization_le_iff_dvd hs (by positivity)]
  intro p
  by_cases hp : p.Prime
  · by_cases hps : p ∣ s
    · have hp5 : p < 5 := by
        by_contra h
        exact hlarge ⟨p, hp, hps, by omega⟩
      have hp23 : p = 2 ∨ p = 3 := by
        have hp2 := hp.two_le
        have hpne4 : p ≠ 4 := by
          intro hp4
          subst p
          norm_num at hp
        omega
      rcases hp23 with rfl | rfl
      · have hvnot : ¬ a + 1 ≤ s.factorization 2 := by
          intro hv
          exact h2 ((Nat.prime_two.pow_dvd_iff_le_factorization hs).mpr hv)
        have hv : s.factorization 2 ≤ a := by omega
        rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num))
          (pow_ne_zero _ (by norm_num)), Nat.factorization_pow,
          Nat.factorization_pow]
        change s.factorization 2 ≤
          a * (Nat.factorization 2) 2 + b * (Nat.factorization 3) 2
        rw [Nat.Prime.factorization_self Nat.prime_two,
          Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]
        simp
        exact hv
      · have hvnot : ¬ b + 1 ≤ s.factorization 3 := by
          intro hv
          exact h3 (((by norm_num : Nat.Prime 3).pow_dvd_iff_le_factorization hs).mpr hv)
        have hv : s.factorization 3 ≤ b := by omega
        rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num))
          (pow_ne_zero _ (by norm_num)), Nat.factorization_pow,
          Nat.factorization_pow]
        change s.factorization 3 ≤
          a * (Nat.factorization 2) 3 + b * (Nat.factorization 3) 3
        rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2),
          Nat.Prime.factorization_self (by norm_num : Nat.Prime 3)]
        simp
        exact hv
    · rw [Nat.factorization_eq_zero_of_not_dvd hps]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

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

private theorem budget_six_largePrime
    (q e : ℕ) (hq : q.Prime) (hq5 : 5 ≤ q) (he : 1 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate (blocks block) q e) 6 ≤
      (33 / 160 : ℝ) * blocks block := by
  rw [refinedWeightedFactorBudget_six]
  have h2 := traceyPrimaryRate_nonmatching_le (blocks block) q e 2 5
    (by omega) (by
      calc 5 ≤ q := hq5
        _ = q ^ 1 := by simp
        _ ≤ q ^ e := Nat.pow_le_pow_right hq.one_le he) (by norm_num)
  have h3 := traceyPrimaryRate_nonmatching_le (blocks block) q e 3 5
    (by omega) (by
      calc 5 ≤ q := hq5
        _ = q ^ 1 := by simp
        _ ≤ q ^ e := Nat.pow_le_pow_right hq.one_le he) (by norm_num)
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hr3 := ActualWreathCompressionTower.traceyPrimaryRate_nonneg
    (blocks block) q e 3
  have h2' : ActualWreathCompressionTower.traceyPrimaryRate
      (blocks block) q e 2 ≤ (blocks block : ℝ) / 5 := by
    norm_num at h2 ⊢
    exact h2
  have h3' : ActualWreathCompressionTower.traceyPrimaryRate
      (blocks block) q e 3 ≤ (blocks block : ℝ) / 5 := by
    norm_num at h3 ⊢
    exact h3
  calc
    _ ≤ (1 / 2 : ℝ) * ((blocks block : ℝ) / 5) +
        (17 / 32 : ℝ) * ((blocks block : ℝ) / 5) := by gcongr
    _ = (33 / 160 : ℝ) * blocks block := by ring

noncomputable def of_degreeThree_largePrime
    (hr : Nat.card block.Fibre = 3)
    (q e : ℕ) (hq : q.Prime) (hq5 : 5 ≤ q)
    (he : 1 ≤ e) (hdiv : q ^ e ∣ blocks block)
    (hmax : ¬ q ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P q e 6 hq he hdiv hmax (by norm_num)
      (component_card_dvd_6 block P hr)
  apply smallAffine_budget_margin_of_lower 3 (blocks block) w 5
      (by norm_num) (by
        exact le_trans hq5 (Nat.le_of_dvd (Nat.card_pos (α := block.Points))
          (dvd_trans (dvd_pow_self q (by omega)) hdiv)))
      (by simpa only [hr] using width_eq block) (33 / 160) _
  · unfold preE7CharacterRho
    norm_num
  · exact budget_six_largePrime block q e hq hq5 he

private theorem budget_six_binary_four
    (e : ℕ) (he : 4 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate (blocks block) 2 e) 6 ≤
      (371 / 1536 : ℝ) * blocks block := by
  rw [refinedWeightedFactorBudget_six]
  have h2 := traceyPrimaryRate_two_matching_of_four_le (blocks block) e he
  have hpow : 16 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num : 0 < 2) he
  have h3 := traceyPrimaryRate_nonmatching_le (blocks block) 2 e 3 16
    (by norm_num) hpow (by norm_num)
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hr3 := ActualWreathCompressionTower.traceyPrimaryRate_nonneg
    (blocks block) 2 e 3
  have h3' : ActualWreathCompressionTower.traceyPrimaryRate
      (blocks block) 2 e 3 ≤ (blocks block : ℝ) / 16 := by
    norm_num at h3 ⊢
    exact h3
  calc
    _ ≤ (1 / 2 : ℝ) * ((blocks block : ℝ) * (5 / 12)) +
        (17 / 32 : ℝ) * ((blocks block : ℝ) / 16) := by gcongr
    _ = (371 / 1536 : ℝ) * blocks block := by ring

noncomputable def of_degreeThree_binaryFour
    (hr : Nat.card block.Fibre = 3)
    (e : ℕ) (he : 4 ≤ e) (hdiv : 2 ^ e ∣ blocks block)
    (hmax : ¬ 2 ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P 2 e 6 Nat.prime_two (by omega) hdiv hmax (by norm_num)
      (component_card_dvd_6 block P hr)
  apply smallAffine_even_budget_margin 3 (blocks block) w
      (by simpa only [hr] using width_eq block)
      (by
        rw [width_eq block, hr]
        exact Even.mul_left (even_iff_two_dvd.mpr
          (dvd_trans (by exact dvd_pow_self 2 (by omega)) hdiv)) 3)
      (371 / 1536) _
  · unfold preE7CharacterRho
    norm_num
  · exact budget_six_binary_four block e he

private theorem budget_six_ternary_three
    (e : ℕ) (he : 3 ≤ e) :
    refinedWeightedFactorBudget
        (ActualWreathCompressionTower.traceyPrimaryRate (blocks block) 3 e) 6 ≤
      (169 / 864 : ℝ) * blocks block := by
  rw [refinedWeightedFactorBudget_six]
  have hpow : 27 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num : 0 < 3) he
  have h2 := traceyPrimaryRate_nonmatching_le (blocks block) 3 e 2 27
    (by norm_num) hpow (by norm_num)
  have h3' : ActualWreathCompressionTower.traceyPrimaryRate
      (blocks block) 3 e 3 ≤ (blocks block : ℝ) / 3 := by
    apply traceyPrimaryRate_matching_le
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · have hden : (18 : ℝ) ≤ 6 * e := by
        exact_mod_cast (Nat.mul_le_mul_left 6 he)
      have hfrac : (2 : ℝ) / (6 * e) ≤ 2 / 18 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
      norm_num at hfrac ⊢
      exact hfrac
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hr3 := ActualWreathCompressionTower.traceyPrimaryRate_nonneg
    (blocks block) 3 e 3
  have h2' : ActualWreathCompressionTower.traceyPrimaryRate
      (blocks block) 3 e 2 ≤ (blocks block : ℝ) / 27 := by
    norm_num at h2 ⊢
    exact h2
  calc
    _ ≤ (1 / 2 : ℝ) * ((blocks block : ℝ) / 27) +
        (17 / 32 : ℝ) * ((blocks block : ℝ) / 3) := by gcongr
    _ = (169 / 864 : ℝ) * blocks block := by ring

noncomputable def of_degreeThree_ternaryThree
    (hr : Nat.card block.Fibre = 3)
    (e : ℕ) (he : 3 ≤ e) (hdiv : 3 ^ e ∣ blocks block)
    (hmax : ¬ 3 ^ (e + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_traceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P 3 e 6 (by norm_num) (by omega) hdiv hmax (by norm_num)
      (component_card_dvd_6 block P hr)
  apply smallAffine_budget_margin_of_lower 3 (blocks block) w 27
      (by norm_num) (Nat.le_of_dvd (Nat.card_pos (α := block.Points))
        (dvd_trans (Nat.pow_dvd_pow 3 he) hdiv))
      (by simpa only [hr] using width_eq block) (169 / 864) _
  · unfold preE7CharacterRho
    norm_num
  · exact budget_six_ternary_three block e he

private def mixedRate (s e₂ e₃ p : ℕ) : ℝ :=
  min (ActualWreathCompressionTower.traceyPrimaryRate s 2 e₂ p)
    (ActualWreathCompressionTower.traceyPrimaryRate s 3 e₃ p)

private theorem budget_six_mixed_fourNine
    (e₂ e₃ : ℕ) (he₂ : 2 ≤ e₂) (he₃ : 2 ≤ e₃) :
    refinedWeightedFactorBudget (mixedRate (blocks block) e₂ e₃) 6 ≤
      (217 / 1152 : ℝ) * blocks block := by
  rw [refinedWeightedFactorBudget_six]
  have h2 : mixedRate (blocks block) e₂ e₃ 2 ≤ (blocks block : ℝ) / 9 := by
    exact (min_le_right _ _).trans
      (traceyPrimaryRate_nonmatching_le (blocks block) 3 e₃ 2 9
        (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 3) he₃)
        (by norm_num))
  have h3 : mixedRate (blocks block) e₂ e₃ 3 ≤ (blocks block : ℝ) / 4 := by
    exact (min_le_left _ _).trans
      (traceyPrimaryRate_nonmatching_le (blocks block) 2 e₂ 3 4
        (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 2) he₂)
        (by norm_num))
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hr3 : 0 ≤ mixedRate (blocks block) e₂ e₃ 3 := le_min
    (ActualWreathCompressionTower.traceyPrimaryRate_nonneg _ _ _ _)
    (ActualWreathCompressionTower.traceyPrimaryRate_nonneg _ _ _ _)
  calc
    _ ≤ (1 / 2 : ℝ) * ((blocks block : ℝ) / 9) +
        (17 / 32 : ℝ) * ((blocks block : ℝ) / 4) := by gcongr
    _ = (217 / 1152 : ℝ) * blocks block := by ring

noncomputable def of_degreeThree_mixedFourNine
    (hr : Nat.card block.Fibre = 3)
    (e₂ e₃ : ℕ) (he₂ : 2 ≤ e₂) (he₃ : 2 ≤ e₃)
    (hdiv₂ : 2 ^ e₂ ∣ blocks block) (hmax₂ : ¬ 2 ^ (e₂ + 1) ∣ blocks block)
    (hdiv₃ : 3 ^ e₃ ∣ blocks block) (hmax₃ : ¬ 3 ^ (e₃ + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_twoTraceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P 2 e₂ 3 e₃ 6 Nat.prime_two (by omega) hdiv₂ hmax₂
      (by norm_num) (by omega) hdiv₃ hmax₃ (by norm_num)
      (component_card_dvd_6 block P hr)
  apply smallAffine_budget_margin_of_lower 3 (blocks block) w 36
      (by norm_num) (Nat.le_of_dvd (Nat.card_pos (α := block.Points)) (by
        simpa [pow_two] using (Nat.Coprime.pow 2 2
          (by norm_num : Nat.Coprime 2 3)).mul_dvd_of_dvd_of_dvd
          (dvd_trans (Nat.pow_dvd_pow 2 he₂) hdiv₂)
          (dvd_trans (Nat.pow_dvd_pow 3 he₃) hdiv₃)))
      (by simpa only [hr] using width_eq block) (217 / 1152) _
  · unfold preE7CharacterRho
    norm_num
  · simpa only [mixedRate] using budget_six_mixed_fourNine block e₂ e₃ he₂ he₃

private theorem budget_six_mixed_eightThree
    (e₂ e₃ : ℕ) (he₂ : 3 ≤ e₂) (he₃ : 1 ≤ e₃) :
    refinedWeightedFactorBudget (mixedRate (blocks block) e₂ e₃) 6 ≤
      (179 / 768 : ℝ) * blocks block := by
  rw [refinedWeightedFactorBudget_six]
  have h2 : mixedRate (blocks block) e₂ e₃ 2 ≤ (blocks block : ℝ) / 3 := by
    exact (min_le_right _ _).trans
      (traceyPrimaryRate_nonmatching_le (blocks block) 3 e₃ 2 3
        (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 3) he₃)
        (by norm_num))
  have h3 : mixedRate (blocks block) e₂ e₃ 3 ≤ (blocks block : ℝ) / 8 := by
    exact (min_le_left _ _).trans
      (traceyPrimaryRate_nonmatching_le (blocks block) 2 e₂ 3 8
        (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 2) he₂)
        (by norm_num))
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  have hr3 : 0 ≤ mixedRate (blocks block) e₂ e₃ 3 := le_min
    (ActualWreathCompressionTower.traceyPrimaryRate_nonneg _ _ _ _)
    (ActualWreathCompressionTower.traceyPrimaryRate_nonneg _ _ _ _)
  calc
    _ ≤ (1 / 2 : ℝ) * ((blocks block : ℝ) / 3) +
        (17 / 32 : ℝ) * ((blocks block : ℝ) / 8) := by gcongr
    _ = (179 / 768 : ℝ) * blocks block := by ring

noncomputable def of_degreeThree_mixedEightThree
    (hr : Nat.card block.Fibre = 3)
    (e₂ e₃ : ℕ) (he₂ : 3 ≤ e₂) (he₃ : 1 ≤ e₃)
    (hdiv₂ : 2 ^ e₂ ∣ blocks block) (hmax₂ : ¬ 2 ^ (e₂ + 1) ∣ blocks block)
    (hdiv₃ : 3 ^ e₃ ∣ blocks block) (hmax₃ : ¬ 3 ^ (e₃ + 1) ∣ blocks block) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_twoTraceyPrimary hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    block P 2 e₂ 3 e₃ 6 Nat.prime_two (by omega) hdiv₂ hmax₂
      (by norm_num) he₃ hdiv₃ hmax₃ (by norm_num)
      (component_card_dvd_6 block P hr)
  apply smallAffine_even_budget_margin 3 (blocks block) w
      (by simpa only [hr] using width_eq block)
      (by
        rw [width_eq block, hr]
        exact Even.mul_left (even_iff_two_dvd.mpr
          (dvd_trans (by exact dvd_pow_self 2 (by omega)) hdiv₂)) 3)
      (179 / 768) _
  · unfold preE7CharacterRho
    norm_num
  · simpa only [mixedRate] using budget_six_mixed_eightThree block e₂ e₃ he₂ he₃

noncomputable def of_degreeThree_nineBlocks
    (hr : Nat.card block.Fibre = 3) (hs : blocks block = 9) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  apply of_integralTraceyPrimePower hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm block P 3 2 6 (by norm_num) (by norm_num) hs (by norm_num)
      (component_card_dvd_6 block P hr)
  have hw : w = 27 := by simpa only [hr, hs] using width_eq block
  have hbudget : integralRefinedWeightedFactorBudget
      (ActualWreathCompressionTower.traceyPrimePowerRate 3 2) 6 =
        (1 / 2 : ℝ) + 3 * fixedTargetCompositionGamma := by
    rw [show 6 = 2 ^ 1 * 3 ^ 1 by norm_num,
      integralRefinedWeightedFactorBudget_mul_of_coprime _ (by decide),
      integralRefinedWeightedFactorBudget_prime_pow _ Nat.prime_two,
      integralRefinedWeightedFactorBudget_prime_pow _
        (by norm_num : Nat.Prime 3)]
    simp [ActualWreathCompressionTower.traceyPrimePowerRate,
      fixedTargetCompositionGamma, Nat.choose]
    ring
  rw [hbudget]
  have hs' : Nat.card block.Points = 9 := by simpa only [blocks] using hs
  rw [hs']
  norm_num [hw, preE7CharacterRho, evenWidth, halfDegree]
  have hlog := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo.le
  unfold fixedTargetCompositionGamma at hlog
  unfold fixedTargetCompositionGamma
  norm_num at hlog ⊢
  linarith

/-- Degree three: every block count is accepted except
`2,3,4,6,8,12,18`. -/
noncomputable def degreeThreeExhaustion
    (hr : Nat.card block.Fibre = 3) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P ⊕
      PLift (blocks block = 2 ∨ blocks block = 3 ∨ blocks block = 4 ∨
        blocks block = 6 ∨ blocks block = 8 ∨ blocks block = 12 ∨
        blocks block = 18) := by
  by_cases hlarge : ∃ q : ℕ, q.Prime ∧ q ∣ blocks block ∧ 5 ≤ q
  · let q := Classical.choose hlarge
    have hqdata := Classical.choose_spec hlarge
    let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      hqdata.1 hqdata.2.1
    exact .inl (of_degreeThree_largePrime hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm block P hr q E.e hqdata.1 hqdata.2.2
        E.one_le E.pow_dvd E.pow_succ_not_dvd)
  by_cases h16 : 2 ^ 4 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      Nat.prime_two (dvd_trans (by norm_num : 2 ∣ 2 ^ 4) h16)
    have he : 4 ≤ E.e := by
      simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
        (valuation_ge_of_pow_dvd block Nat.prime_two h16)
    exact .inl (of_degreeThree_binaryFour hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm block P hr E.e he E.pow_dvd
        E.pow_succ_not_dvd)
  by_cases h27 : 3 ^ 3 ∣ blocks block
  · let E := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
      (by norm_num : Nat.Prime 3) (dvd_trans (by norm_num : 3 ∣ 3 ^ 3) h27)
    have he : 3 ≤ E.e := by
      simpa only [E, ExactPrimaryDivisor.ofPrimeDvd] using
        (valuation_ge_of_pow_dvd block (by norm_num : Nat.Prime 3) h27)
    exact .inl (of_degreeThree_ternaryThree hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm block P hr E.e he E.pow_dvd
        E.pow_succ_not_dvd)
  by_cases h49 : 2 ^ 2 ∣ blocks block ∧ 3 ^ 2 ∣ blocks block
  · let E₂ := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
        Nat.prime_two (dvd_trans (by norm_num : 2 ∣ 2 ^ 2) h49.1)
    let E₃ := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
        (by norm_num : Nat.Prime 3)
          (dvd_trans (by norm_num : 3 ∣ 3 ^ 2) h49.2)
    have he₂ : 2 ≤ E₂.e := by
      simpa only [E₂, ExactPrimaryDivisor.ofPrimeDvd] using
        (valuation_ge_of_pow_dvd block Nat.prime_two h49.1)
    have he₃ : 2 ≤ E₃.e := by
      simpa only [E₃, ExactPrimaryDivisor.ofPrimeDvd] using
        (valuation_ge_of_pow_dvd block (by norm_num : Nat.Prime 3) h49.2)
    exact .inl (of_degreeThree_mixedFourNine hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm block P hr E₂.e E₃.e he₂ he₃
        E₂.pow_dvd E₂.pow_succ_not_dvd E₃.pow_dvd E₃.pow_succ_not_dvd)
  by_cases h83 : 2 ^ 3 ∣ blocks block ∧ 3 ∣ blocks block
  · let E₂ := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
        Nat.prime_two (dvd_trans (by norm_num : 2 ∣ 2 ^ 3) h83.1)
    let E₃ := ExactPrimaryDivisor.ofPrimeDvd (blocks_ne_zero block)
        (by norm_num : Nat.Prime 3) h83.2
    have he₂ : 3 ≤ E₂.e := by
      simpa only [E₂, ExactPrimaryDivisor.ofPrimeDvd] using
        (valuation_ge_of_pow_dvd block Nat.prime_two h83.1)
    exact .inl (of_degreeThree_mixedEightThree hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm block P hr E₂.e E₃.e he₂ E₃.one_le
        E₂.pow_dvd E₂.pow_succ_not_dvd E₃.pow_dvd E₃.pow_succ_not_dvd)
  have hdvd : blocks block ∣ 72 := by
    simpa using dvd_binary_ternary_bounded (blocks_ne_zero block) hlarge h16 h27
  have hs2 : 2 ≤ blocks block := block.degrees_ge_two.2
  have hs72 : blocks block ≤ 72 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases hs : blocks block
  all_goals norm_num at hdvd
  all_goals norm_num at h49
  all_goals norm_num at h83
  all_goals first
    | exact .inl (of_degreeThree_nineBlocks hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm block P hr hs)
    | exact .inr ⟨by simp⟩

end ComponentSource
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
