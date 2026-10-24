import SymmetricSubgroupAsymptotics.OriginalAffineSharpDyadicBands
import SymmetricSubgroupAsymptotics.OriginalAffineQuotientPrimeMultiplicity

/-! Small scalar seeds for original affine actions. These use the literal
complement quotient, not subgroup catalogues: all one-dimensional local
degrees at least11, the two-dimensional interval25..32, and the actual
ternary cubic translation profile. The actual smaller-top ceiling remains
explicit; no fitted group-bound premise is exposed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalAffineSharpSmallSeeds
open OriginalAffineBlockCharacteristicHead

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

private def coefficient : ℝ := (translationDimension J block P : ℝ)+
  ArithmeticFunction.cardFactors (Nat.card (block.Component ⧸ P.V))

private theorem coefficient_le : coefficient J block P ≤
    (translationDimension J block P : ℝ)*(1+Real.logb 2 (Nat.card block.Fibre : ℝ)) := by
  have ho := ActualWreathUniformLocalOrderCost.cardFactors_le_logb
    (Nat.card (block.Component ⧸ P.V)) (Nat.card_pos (α := block.Component ⧸ P.V)).ne'
  have hd := OriginalAffineTameUniformCost.quotient_log_le_dimension_mul_degree_log J block P
  dsimp only [coefficient]
  nlinarith only [ho,hd]

private theorem genRank_le_of_bounds (C₀ s₀ R₀ : ℝ)
    (hC : coefficient J block P ≤ C₀)
    (hs : Real.logb 2 (Nat.card block.Fibre : ℝ) ≤ s₀)
    (hR : R₀ ≤ (Nat.card block.Fibre : ℝ)) (hR₀ : 0 ≤ R₀)
    (hbudget : (C₀+2)^2*(9*s₀+64) ≤ 36*R₀^2) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let r := Nat.card block.Fibre
  let t := Nat.card block.Points
  let s := Real.logb 2 (r : ℝ)
  let C := coefficient J block P
  have hr0 : r ≠ 0 := (Nat.card_pos (α := block.Fibre)).ne'
  have ht : 2 ≤ t := block.degrees_ge_two.2
  have ht0 : t ≠ 0 := by omega
  have hs0 : 0 ≤ s := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast (show 1 ≤ r from Nat.pos_of_ne_zero hr0))
  have hC0 : 0 ≤ C := by dsimp only [C,coefficient]; positivity
  have hC₀ : 0 ≤ C₀ := hC0.trans hC
  have hmargin : (C+2)^2*(9*s+64) ≤ 36*(r : ℝ)^2 := by
    have hsq := (sq_le_sq₀ (show 0 ≤ C+2 by linarith only [hC0])
      (show 0 ≤ C₀+2 by linarith only [hC₀])).mpr
        (by simpa only [add_comm] using add_le_add_right hC 2)
    calc
      (C+2)^2*(9*s+64) ≤ (C₀+2)^2*(9*s+64) :=
        mul_le_mul_of_nonneg_right hsq (by linarith only [hs0])
      _ ≤ (C₀+2)^2*(9*s₀+64) :=
        mul_le_mul_of_nonneg_left (by linarith only [hs]) (sq_nonneg _)
      _ ≤ 36*R₀^2 := hbudget
      _ ≤ 36*(r : ℝ)^2 := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ hR₀ (by positivity)).mpr hR) (by norm_num)
  have hh := OriginalAffineSharpMultiplicityCost.genRank_le_half_cost J block P i
  have hl := OriginalAffineSharpMultiplicityCost.genRank_le_log_cost J block P i
  simp only [Fintype.card_eq_nat_card] at hh hl
  change (MarkedC4.genRank J : ℝ) ≤ C*(t : ℝ)/2+MarkedC4.genRank block.Top at hh
  change (MarkedC4.genRank J : ℝ) ≤ Real.sqrt (5/3)*C*(t : ℝ)/
    Real.sqrt (Real.logb 2 (t : ℝ))+MarkedC4.genRank block.Top at hl
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤
      (traceyPermutationGeneratorCeiling t : ℝ) := by exact_mod_cast htop
  change (MarkedC4.genRank block.Top : ℝ) ≤
    (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) at htopR
  have hreal := AffineSharpMultiplicityCeilingMargin.aggregate_le C s (r : ℝ)
    (MarkedC4.genRank J : ℝ) t hC0 hs0 (by positivity) (by positivity) ht hmargin
      (hh.trans (add_le_add le_rfl htopR)) (hl.trans (add_le_add le_rfl htopR))
  have hdegree : n = r*t := by simpa only [Nat.card_fin] using block.degree_product.symm
  have hdegreeR : (n : ℝ) = (r : ℝ)*(t : ℝ) := by exact_mod_cast hdegree
  have hlogn : Real.logb 2 (n : ℝ) = s+Real.logb 2 (t : ℝ) := by
    rw [hdegreeR,Real.logb_mul (by exact_mod_cast hr0) (by exact_mod_cast ht0)]
  have htarget : (MarkedC4.genRank J : ℝ) ≤ (n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ)) := by
    rw [hlogn,hdegreeR]
    exact hreal
  have hfinal := htarget.trans (Nat.le_ceil ((n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ))))
  change (MarkedC4.genRank J : ℝ) ≤ (traceyPermutationGeneratorCeiling n : ℝ) at hfinal
  exact_mod_cast hfinal

theorem genRank_le_of_dimension_one (hd : translationDimension J block P ≤ 1)
    (hr : 11 ≤ Nat.card block.Fibre) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  by_cases hlarge : 16 ≤ Nat.card block.Fibre
  · exact OriginalAffineSharpDyadicBands.genRank_le_of_dimension_one J block P hd hlarge i htop
  have hsmall : Nat.card block.Fibre ≤ 16 := by omega
  have hs0 : 0 ≤ Real.logb 2 (Nat.card block.Fibre : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ Nat.card block.Fibre by omega))
  have hdR : (translationDimension J block P : ℝ) ≤ 1 := by exact_mod_cast hd
  have hc := (coefficient_le J block P).trans
    (mul_le_mul_of_nonneg_right hdR (show 0 ≤ 1+Real.logb 2 (Nat.card block.Fibre : ℝ)
      by linarith only [hs0]))
  simp only [one_mul] at hc
  by_cases h12 : 12 ≤ Nat.card block.Fibre
  · have hs := IntegerLogSquareRootCeilingCertificate.log_upper (Nat.card block.Fibre) 1 4
      (by omega) (by decide) (by simpa only [pow_one] using hsmall)
    have hs' : Real.logb 2 (Nat.card block.Fibre : ℝ) ≤ 4 := by
      simpa only [Nat.cast_ofNat,Nat.cast_one,div_one] using hs
    exact genRank_le_of_bounds J block P 5 4 12 (by linarith only [hc,hs']) hs'
      (by exact_mod_cast h12) (by norm_num) (by norm_num) i htop
  · have he : Nat.card block.Fibre = 11 := by omega
    have hs := IntegerLogSquareRootCeilingCertificate.log_upper 11 2 7 (by decide)
      (by decide) (by decide)
    have hs' : Real.logb 2 (Nat.card block.Fibre : ℝ) ≤ 7/2 := by simpa only [he] using hs
    exact genRank_le_of_bounds J block P (9/2) (7/2) 11
      (by linarith only [hc,hs']) hs' (by exact_mod_cast hr)
      (by norm_num) (by norm_num) i htop

theorem genRank_le_of_dimension_two_interval (hd : translationDimension J block P ≤ 2)
    (hr : 25 ≤ Nat.card block.Fibre) (hr' : Nat.card block.Fibre ≤ 32) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  have hs := IntegerLogSquareRootCeilingCertificate.log_upper (Nat.card block.Fibre) 1 5
    (by omega) (by decide) (by simpa only [pow_one] using hr')
  have hs' : Real.logb 2 (Nat.card block.Fibre : ℝ) ≤ 5 := by
    simpa only [Nat.cast_ofNat,Nat.cast_one,div_one] using hs
  have hs0 : 0 ≤ Real.logb 2 (Nat.card block.Fibre : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ Nat.card block.Fibre by omega))
  have hdR : (translationDimension J block P : ℝ) ≤ 2 := by exact_mod_cast hd
  have hc := (coefficient_le J block P).trans
    (mul_le_mul_of_nonneg_right hdR (show 0 ≤ 1+Real.logb 2 (Nat.card block.Fibre : ℝ)
      by linarith only [hs0]))
  exact genRank_le_of_bounds J block P 12 5 25 (by linarith only [hc,hs']) hs'
    (by exact_mod_cast hr) (by norm_num) (by norm_num) i htop

theorem genRank_le_of_ternary_cubic (hp : P.p = 3)
    (hd : translationDimension J block P = 3) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  have hr : Nat.card block.Fibre = 27 := by
    have hh := fibre_card_eq_prime_pow_dimension J block P
    rw [hp,hd] at hh
    exact hh
  have hq := OriginalAffineQuotientPrimeMultiplicity.quotient_cardFactors_le_nine_of_ternary_cubic
    J block P hp hd
  have hc : coefficient J block P ≤ 12 := by
    have hqR : (ArithmeticFunction.cardFactors (Nat.card (block.Component ⧸ P.V)) : ℝ) ≤ 9 := by
      exact_mod_cast hq
    dsimp only [coefficient]
    rw [hd]
    norm_num only [Nat.cast_ofNat]
    linarith only [hqR]
  have hs := IntegerLogSquareRootCeilingCertificate.log_upper 27 1 5
    (by decide) (by decide) (by decide)
  have hs' : Real.logb 2 (Nat.card block.Fibre : ℝ) ≤ 5 := by
    simpa only [hr,div_one,Nat.cast_ofNat,Nat.cast_one] using hs
  exact genRank_le_of_bounds J block P 12 5 25 hc hs'
    (by rw [hr]; norm_num) (by norm_num) (by norm_num) i htop

end SymmetricSubgroupAsymptotics.OriginalAffineSharpSmallSeeds
