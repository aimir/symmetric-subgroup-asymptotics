import SymmetricSubgroupAsymptotics.ActualWreathChiefWeightedPrimeBudget
import SymmetricSubgroupAsymptotics.MarkedC4AbelianSectionSize
import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorNumerics

/-! Uniform ordinary-generator costs on the SAME actual correlated
chief trace, charged to its genuine local group order. Elementary layers
use the proved half/real-log capacities; nonabelian internal-factor ranks
use the checked ordinary prime-multiplicity bound, never an assumed +1
or simple two-generation theorem. No permutation input is used. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.ActualWreathUniformLocalOrderCost
open ActualWreathChiefWeightedPrimeBudget ActualWreathCharacteristicChiefProfile

theorem cardFactors_le_logb (N : ℕ) (hN : N ≠ 0) :
    (ArithmeticFunction.cardFactors N : ℝ) ≤ Real.logb 2 (N : ℝ) := by
  have hnat : 2^ArithmeticFunction.cardFactors N ≤ N := by
    simpa only [ArithmeticFunction.cardFactors_apply,MarkedC4.AbelianSectionSize.omega] using
      MarkedC4.AbelianSectionSize.two_pow_omega_le hN
  have hreal : (2 : ℝ)^ArithmeticFunction.cardFactors N ≤ (N : ℝ) := by exact_mod_cast hnat
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (2 : ℝ)^ArithmeticFunction.cardFactors N) hreal
  simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] using hh

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
    (MarkedC4.genRank S.A : ℝ) ≤ Real.logb 2 (Nat.card S.D : ℝ)*rate+MarkedC4.genRank Q := by
  obtain ⟨c,hc,hcost,hsource⟩ := exists_weightedOrder_bound S i hI
    (fun _ => rate) (fun _ => hrate) hcap
  rw [weightedOrder_const] at hcost
  have hsourceR : (MarkedC4.genRank S.A : ℝ) ≤ (c : ℝ)+MarkedC4.genRank Q := by
    exact_mod_cast hsource
  have horder := mul_le_mul_of_nonneg_right
    (cardFactors_le_logb (Nat.card S.D) (Nat.card_pos (α := S.D)).ne')
    (show 0 ≤ rate by linarith only [hrate])
  exact hsourceR.trans ((add_le_add hcost le_rfl).trans (add_le_add horder le_rfl))

theorem genRank_le_half_local_log :
    (MarkedC4.genRank S.A : ℝ) ≤
      Real.logb 2 (Nat.card S.D : ℝ)*(Fintype.card I : ℝ)/2+MarkedC4.genRank Q := by
  have ht : (2 : ℝ) ≤ Fintype.card I := by exact_mod_cast hI
  have hh := uniform_rate S i hI ((Fintype.card I : ℝ)/2) (by linarith only [ht])
    (fun c => by simpa only [mul_div_assoc] using c.half)
  simpa only [mul_div_assoc] using hh

theorem genRank_le_log_local_log :
    (MarkedC4.genRank S.A : ℝ) ≤
      2*Real.logb 2 (Nat.card S.D : ℝ)*(Fintype.card I : ℝ)/
        Real.sqrt (Real.logb 2 (Fintype.card I : ℝ))+MarkedC4.genRank Q := by
  let t : ℝ := Fintype.card I
  have ht : 2 ≤ t := by dsimp only [t]; exact_mod_cast hI
  have hL : 0 < Real.logb 2 t := Real.logb_pos (by norm_num) (by linarith only [ht])
  have hs : 0 < Real.sqrt (Real.logb 2 t) := Real.sqrt_pos.mpr hL
  have hsle : Real.sqrt (Real.logb 2 t) ≤ t :=
    (Real.sqrt_le_iff).mpr ⟨by linarith only [ht],LargeOrbitGeneratorNumerics.logb_le_square ht⟩
  have hunit : (1 : ℝ) ≤ t/Real.sqrt (Real.logb 2 t) :=
    (le_div_iff₀ hs).mpr (by simpa only [one_mul] using hsle)
  have hrate : (1 : ℝ) ≤ 2*t/Real.sqrt (Real.logb 2 t) := by
    have hh : 1 ≤ 2*(t/Real.sqrt (Real.logb 2 t)) := by linarith only [hunit]
    convert hh using 1 <;> ring
  have hh := uniform_rate S i hI (2*t/Real.sqrt (Real.logb 2 t)) hrate
    (fun c => by convert c.logarithmic using 1 <;> dsimp only [t] <;> ring)
  convert hh using 1 <;> dsimp only [t] <;> ring

end SymmetricSubgroupAsymptotics.ActualWreathUniformLocalOrderCost
