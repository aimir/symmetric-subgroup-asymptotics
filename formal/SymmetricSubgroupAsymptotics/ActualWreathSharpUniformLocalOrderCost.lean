import SymmetricSubgroupAsymptotics.ActualWreathUniformLocalOrderCost
import SymmetricSubgroupAsymptotics.ElementaryChargeSharpRealLogarithmic

/-! Uniform ordinary costs retaining both the sharper induced coefficient
and the ACTUAL local prime multiplicity. The same chief trace and its
internal simple-factor ranks are charged, with rate at least one paying
those ranks. No simple two-generation or ordinary +1 bound is used. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.ActualWreathSharpUniformLocalOrderCost
open ActualWreathChiefWeightedPrimeBudget ActualWreathCharacteristicChiefProfile

private theorem weightedOrder_const (c : ℝ) (M : ℕ) :
    weightedOrder (fun _ => c) M = (ArithmeticFunction.cardFactors M : ℝ)*c := by
  simp only [weightedOrder,ArithmeticFunction.cardFactors_eq_sum_factorization,
    Finsupp.sum,Nat.cast_sum,Finset.sum_mul]

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]
    (S : ActualWreathCompressionState Q I) (i : I) (hI : 2 ≤ Fintype.card I)

include i hI

private theorem uniform_rate (rate : ℝ) (hrate : 1 ≤ rate)
    (hcap : ∀ c : ElementaryCharge (Fintype.card I),
      (c.capacity : ℝ) ≤ (c.dimension : ℝ)*rate) :
    (MarkedC4.genRank S.A : ℝ) ≤
      (ArithmeticFunction.cardFactors (Nat.card S.D) : ℝ)*rate+MarkedC4.genRank Q := by
  obtain ⟨c,hc,hcost,hsource⟩ := exists_weightedOrder_bound S i hI
    (fun _ => rate) (fun _ => hrate) hcap
  rw [weightedOrder_const] at hcost
  have hsourceR : (MarkedC4.genRank S.A : ℝ) ≤ (c : ℝ)+MarkedC4.genRank Q := by
    exact_mod_cast hsource
  exact hsourceR.trans (add_le_add hcost le_rfl)

theorem genRank_le_half_local_cardFactors :
    (MarkedC4.genRank S.A : ℝ) ≤
      (ArithmeticFunction.cardFactors (Nat.card S.D) : ℝ)*(Fintype.card I : ℝ)/2+
        MarkedC4.genRank Q := by
  have ht : (2 : ℝ) ≤ Fintype.card I := by exact_mod_cast hI
  have hh := uniform_rate S i hI ((Fintype.card I : ℝ)/2) (by linarith only [ht])
    (fun c => by simpa only [mul_div_assoc] using c.half)
  simpa only [mul_div_assoc] using hh

theorem genRank_le_log_local_cardFactors :
    (MarkedC4.genRank S.A : ℝ) ≤
      Real.sqrt (5/3)*(ArithmeticFunction.cardFactors (Nat.card S.D) : ℝ)*
        (Fintype.card I : ℝ)/Real.sqrt (Real.logb 2 (Fintype.card I : ℝ))+
          MarkedC4.genRank Q := by
  let t : ℝ := Fintype.card I
  have ht : 2 ≤ t := by dsimp only [t]; exact_mod_cast hI
  have hL : 0 < Real.logb 2 t := Real.logb_pos (by norm_num) (by linarith only [ht])
  have hs : 0 < Real.sqrt (Real.logb 2 t) := Real.sqrt_pos.mpr hL
  have hsle : Real.sqrt (Real.logb 2 t) ≤ t :=
    (Real.sqrt_le_iff).mpr ⟨by linarith only [ht],LargeOrbitGeneratorNumerics.logb_le_square ht⟩
  have hunit : (1 : ℝ) ≤ t/Real.sqrt (Real.logb 2 t) :=
    (le_div_iff₀ hs).mpr (by simpa only [one_mul] using hsle)
  have hsharp : (1 : ℝ) ≤ Real.sqrt (5/3) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5/3),
      Real.sqrt_nonneg (5/3 : ℝ)]
  have hrate : (1 : ℝ) ≤ Real.sqrt (5/3)*t/Real.sqrt (Real.logb 2 t) := by
    have hh := mul_le_mul hsharp hunit (by norm_num : (0 : ℝ) ≤ 1)
      (Real.sqrt_nonneg (5/3 : ℝ))
    simpa only [one_mul,mul_div_assoc] using hh
  have hh := uniform_rate S i hI
    (Real.sqrt (5/3)*t/Real.sqrt (Real.logb 2 t)) hrate
    (fun c => by
      convert ElementaryChargeSharpRealLogarithmic.logarithmic_real c hI using 1 <;>
        dsimp only [t] <;> ring)
  convert hh using 1 <;> dsimp only [t] <;> ring

theorem genRank_le_log_local_log :
    (MarkedC4.genRank S.A : ℝ) ≤
      Real.sqrt (5/3)*Real.logb 2 (Nat.card S.D : ℝ)*
        (Fintype.card I : ℝ)/Real.sqrt (Real.logb 2 (Fintype.card I : ℝ))+
          MarkedC4.genRank Q := by
  have hh := genRank_le_log_local_cardFactors S i hI
  have horder := ActualWreathUniformLocalOrderCost.cardFactors_le_logb
    (Nat.card S.D) (Nat.card_pos (α := S.D)).ne'
  have hm := mul_le_mul_of_nonneg_right horder
    (show (0 : ℝ) ≤ Real.sqrt (5/3)*(Fintype.card I : ℝ)/
      Real.sqrt (Real.logb 2 (Fintype.card I : ℝ)) by positivity)
  have hcompare : Real.sqrt (5/3)*(ArithmeticFunction.cardFactors (Nat.card S.D) : ℝ)*
      (Fintype.card I : ℝ)/Real.sqrt (Real.logb 2 (Fintype.card I : ℝ)) ≤
      Real.sqrt (5/3)*Real.logb 2 (Nat.card S.D : ℝ)*
        (Fintype.card I : ℝ)/Real.sqrt (Real.logb 2 (Fintype.card I : ℝ)) := by
    convert hm using 1 <;> ring
  exact hh.trans (add_le_add hcompare le_rfl)

end SymmetricSubgroupAsymptotics.ActualWreathSharpUniformLocalOrderCost
