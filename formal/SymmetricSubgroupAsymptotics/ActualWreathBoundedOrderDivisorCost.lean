import SymmetricSubgroupAsymptotics.ActualWreathSixOrderDivisorCost
import SymmetricSubgroupAsymptotics.PrimeMultiplicityTwoRateBound

/-! An exact integer cut for any primary divisor, on a fixed actual
ordinary chief trace. Literal local-order divisibility is the only local
arithmetic input. The cut is the floor of the genuine weighted cost;
no rounding of its individual characteristic terms is introduced. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ActualWreathBoundedOrderDivisorCost
open ActualWreathChiefWeightedPrimeBudget ActualWreathChooseDivisorCapacity

private theorem factorization_le_total (N q : ℕ) :
    N.factorization q ≤ ArithmeticFunction.cardFactors N := by
  by_cases hz : N.factorization q = 0
  · rw [hz]
    exact Nat.zero_le _
  · have hh := Finset.single_le_sum
      (fun j (_ : j ∈ N.factorization.support) => Nat.zero_le (N.factorization j))
      (Finsupp.mem_support_iff.mpr hz)
    simpa only [ArithmeticFunction.cardFactors_eq_sum_factorization,Finsupp.sum] using hh

def numerator (t N q a : ℕ) : ℕ :=
  t*(N.factorization q*(a*(q-1)).choose ((a*(q-1))/2)*q^a+
    (ArithmeticFunction.cardFactors N-N.factorization q)*2^(a*(q-1)))

def denominator (q a : ℕ) : ℕ := 2^(a*(q-1))*q^a

def integerCut (t N q a : ℕ) : ℕ := numerator t N q a / denominator q a

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]
    {i : I} {S : ActualWreathCompressionState Q I} {c : ℕ}

theorem cost_le_integerCut (hc : ActualWreathOrdinaryChiefRecurrence.ChiefCost i S c)
    (hI : 2 ≤ Fintype.card I) (N : ℕ) (hN : N ≠ 0) (horder : Nat.card S.D ∣ N)
    (q a : ℕ) (hq : q.Prime) (hdiv : q^a ∣ Fintype.card I) :
    c ≤ integerCut (Fintype.card I) N q a := by
  let t := Fintype.card I
  let W := divisorWeight t q a
  have hcost := ActualWreathChiefChooseDivisorWeights.cost_le_divisorWeight hc hI q a hq hdiv
  have hlocal := weightedOrder_mono_of_dvd W
    (fun p => (show (0 : ℝ) ≤ 1 by norm_num).trans (one_le_divisorWeight t q a p))
    (Nat.card_pos (α := S.D)).ne' hN horder
  have hw (p : ℕ) : W p ≤ divisorRate t q a p :=
    divisorWeight_le_divisorRate t q a p (by omega) hq hdiv
  have hprimary : W q ≤ (t : ℝ)*primaryRate q a := by
    simpa only [divisorRate,if_pos rfl] using hw q
  have hother (p : ℕ) (hp : p ≠ q) : W p ≤ (t : ℝ)/(q : ℝ)^a := by
    simpa only [divisorRate,if_neg hp] using hw p
  have htwo := PrimeMultiplicityTwoRateBound.weightedOrder_le_two_rates W N q
    ((t : ℝ)*primaryRate q a) ((t : ℝ)/(q : ℝ)^a) hprimary hother
  have hraw : (c : ℝ) ≤ (numerator t N q a : ℝ)/(denominator q a : ℝ) := by
    apply ((hcost.trans hlocal).trans htwo).trans
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have htwoR : (0 : ℝ) < (2 : ℝ)^(a*(q-1)) := by positivity
    have heq : (N.factorization q : ℝ)*((t : ℝ)*primaryRate q a)+
        ((ArithmeticFunction.cardFactors N : ℝ)-(N.factorization q : ℝ))*
          ((t : ℝ)/(q : ℝ)^a) =
        (numerator t N q a : ℝ)/(denominator q a : ℝ) := by
      simp only [numerator,denominator,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,
        Nat.cast_sub (factorization_le_total N q),primaryRate]
      field_simp [hqR.ne',htwoR.ne']
      <;> ring
    exact heq.le
  have hden : 0 < denominator q a := mul_pos (pow_pos (by decide) _) (pow_pos hq.pos _)
  have hh := (le_div_iff₀ (by exact_mod_cast hden : (0 : ℝ) < denominator q a)).mp hraw
  apply (Nat.le_div_iff_mul_le hden).mpr
  exact_mod_cast hh

end SymmetricSubgroupAsymptotics.ActualWreathBoundedOrderDivisorCost
