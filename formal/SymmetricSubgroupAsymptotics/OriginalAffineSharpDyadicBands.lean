import SymmetricSubgroupAsymptotics.OriginalAffineSharpMultiplicityCost
import SymmetricSubgroupAsymptotics.OriginalAffineTameUniformCost
import SymmetricSubgroupAsymptotics.AffineSharpMultiplicityCeilingMargin
import SymmetricSubgroupAsymptotics.OddAffineSharpDyadicMarginNumerics
import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate

/-! Three actual affine dimension bands, for arbitrary original top.
Every numerical margin is derived from the literal translation dimension
and the order of the SAME complement quotient. The only generator bound
assumed is the actual top's genuinely smaller coarse ceiling. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalAffineSharpDyadicBands
open OriginalAffineBlockCharacteristicHead

private theorem one_band (k : ℕ) (hk : 4 ≤ k) :
    (1*k+2*1+2)^2*(9*k+73) ≤ 36*4^k := by
  have he : 1*k+2*1+2 = k+4 := by omega
  rw [he]
  exact OddAffineSharpDyadicMarginNumerics.dimension_one k hk

private theorem two_band (k : ℕ) (hk : 5 ≤ k) :
    (2*k+2*2+2)^2*(9*k+73) ≤ 36*4^k := by
  have he : 2*k+2*2+2 = 2*k+6 := by omega
  rw [he]
  exact OddAffineSharpDyadicMarginNumerics.dimension_two k hk

private theorem four_band (k : ℕ) (hk : 6 ≤ k) :
    (4*k+2*4+2)^2*(9*k+73) ≤ 36*4^k := by
  have he : 4*k+2*4+2 = 4*k+10 := by omega
  rw [he]
  exact OddAffineSharpDyadicMarginNumerics.dimension_four k hk

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

private theorem coefficient_le :
    (translationDimension J block P : ℝ)+
      (ArithmeticFunction.cardFactors (Nat.card (block.Component ⧸ P.V)) : ℝ) ≤
        (translationDimension J block P : ℝ)*
          (1+Real.logb 2 (Nat.card block.Fibre : ℝ)) := by
  have ho := ActualWreathUniformLocalOrderCost.cardFactors_le_logb
    (Nat.card (block.Component ⧸ P.V)) (Nat.card_pos (α := block.Component ⧸ P.V)).ne'
  have hd := OriginalAffineTameUniformCost.quotient_log_le_dimension_mul_degree_log J block P
  nlinarith only [ho,hd]

private theorem genRank_le_of_band (D k₀ : ℕ)
    (hnum : ∀ k : ℕ, k₀ ≤ k → (D*k+2*D+2)^2*(9*k+73) ≤ 36*4^k)
    (hd : translationDimension J block P ≤ D)
    (hr : 2^k₀ ≤ Nat.card block.Fibre) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let r := Nat.card block.Fibre
  let t := Nat.card block.Points
  let s := Real.logb 2 (r : ℝ)
  let k := Nat.log 2 r
  let C : ℝ := (translationDimension J block P : ℝ)+
    ArithmeticFunction.cardFactors (Nat.card (block.Component ⧸ P.V))
  let B : ℝ := (D : ℝ)*((k : ℝ)+2)+2
  have hr0 : r ≠ 0 := (Nat.card_pos (α := block.Fibre)).ne'
  have ht : 2 ≤ t := block.degrees_ge_two.2
  have ht0 : t ≠ 0 := by omega
  have hs : 0 ≤ s := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast (show 1 ≤ r from Nat.pos_of_ne_zero hr0))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hk : k₀ ≤ k := Nat.le_log_of_pow_le (by decide : 1 < 2) hr
  have hR : (2 : ℝ)^k ≤ (r : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hr0
  have hsK : s ≤ (k : ℝ)+1 := by
    have hpow : r ≤ 2^(k+1) := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) r).le
    have hh := IntegerLogSquareRootCeilingCertificate.log_upper r 1 (k+1)
      (by omega) (by decide) (by simpa only [pow_one] using hpow)
    simpa only [s,Nat.cast_add,Nat.cast_one,div_one] using hh
  have hCB : C+2 ≤ B := by
    have hdR : (translationDimension J block P : ℝ) ≤ D := by exact_mod_cast hd
    have hfirst := coefficient_le J block P
    change C ≤ (translationDimension J block P : ℝ)*(1+s) at hfirst
    have hdim := mul_le_mul_of_nonneg_right hdR (show 0 ≤ 1+s by linarith only [hs])
    have hwindow := mul_le_mul_of_nonneg_left hsK (show (0 : ℝ) ≤ D by positivity)
    dsimp only [B]
    nlinarith only [hfirst,hdim,hwindow]
  have hn : (D*k+2*D+2)^2*(9*k+73) ≤ 36*4^k := hnum k hk
  have hnR : B^2*(9*((k : ℝ)+1)+64) ≤ 36*(4 : ℝ)^k := by
    have hh : ((D : ℝ)*(k : ℝ)+2*(D : ℝ)+2)^2*(9*(k : ℝ)+73) ≤ 36*(4 : ℝ)^k := by
      exact_mod_cast hn
    dsimp only [B]
    convert hh using 1 <;> ring
  have hRpow : (4 : ℝ)^k ≤ (r : ℝ)^2 := by
    calc
      (4 : ℝ)^k = ((2 : ℝ)^k)^2 := by
        rw [show (4 : ℝ) = 2^2 by norm_num,←pow_mul,←pow_mul]
        congr 1
        omega
      _ ≤ (r : ℝ)^2 := (sq_le_sq₀ (by positivity) (by positivity)).mpr hR
  have hmargin : (C+2)^2*(9*s+64) ≤ 36*(r : ℝ)^2 := by
    have hsq := (sq_le_sq₀ (show 0 ≤ C+2 by linarith only [hC]) hB).mpr hCB
    calc
      (C+2)^2*(9*s+64) ≤ B^2*(9*s+64) :=
        mul_le_mul_of_nonneg_right hsq (by linarith only [hs])
      _ ≤ B^2*(9*((k : ℝ)+1)+64) :=
        mul_le_mul_of_nonneg_left (by linarith only [hsK]) (sq_nonneg B)
      _ ≤ 36*(4 : ℝ)^k := hnR
      _ ≤ 36*(r : ℝ)^2 := mul_le_mul_of_nonneg_left hRpow (by norm_num)
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
    (MarkedC4.genRank J : ℝ) t hC hs (by positivity) (by positivity) ht hmargin
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
    (hr : 16 ≤ Nat.card block.Fibre) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  exact genRank_le_of_band J block P 1 4 one_band hd hr i htop

theorem genRank_le_of_dimension_two (hd : translationDimension J block P ≤ 2)
    (hr : 32 ≤ Nat.card block.Fibre) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  exact genRank_le_of_band J block P 2 5 two_band hd hr i htop

theorem genRank_le_of_dimension_four (hd : translationDimension J block P ≤ 4)
    (hr : 64 ≤ Nat.card block.Fibre) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤ traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  exact genRank_le_of_band J block P 4 6 four_band hd hr i htop

end SymmetricSubgroupAsymptotics.OriginalAffineSharpDyadicBands
