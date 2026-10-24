import SymmetricSubgroupAsymptotics.ActualWreathSixOrderJointLogCost
import SymmetricSubgroupAsymptotics.PrimeMultiplicityTwoRateBound

/-! A shared SAME-chief bound from a literal local-order divisorN,
its total prime multiplicityC and its largest prime multiplicitym.
The data are arithmetic order bounds, not desired generator estimates.
Every ordinary simple-factor rank remains charged by actual weights>=1. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathBoundedMultiplicityJointCost
open ActualWreathChiefWeightedPrimeBudget ActualWreathChooseDivisorCapacity
open ActualWreathOrdinaryChiefRecurrence

private theorem primary_rate_le_three_eighths (q a : ℕ) (hq : q.Prime)
    (ha : 1 ≤ a) (hM : 8 ≤ q^a) : primaryRate q a ≤ 3/8 := by
  have hn : 3 ≤ a*(q-1) := by
    by_cases hq2 : q = 2
    · have ha3 : 3 ≤ a := by
        by_contra hh
        have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show a ≤ 2 by omega)
        norm_num at hp
        rw [hq2] at hM
        omega
      simpa only [hq2,Nat.reduceSub,mul_one] using ha3
    · by_cases hq3 : q = 3
      · have ha2 : 2 ≤ a := by
          by_contra hh
          have hp := Nat.pow_le_pow_right (by decide : 0 < 3) (show a ≤ 1 by omega)
          norm_num at hp
          rw [hq3] at hM
          omega
        rw [hq3]
        omega
      · have hq4 : 4 ≤ q := by have hh := hq.two_le; omega
        have hh := Nat.mul_le_mul ha (show 3 ≤ q-1 by omega)
        simpa only [one_mul] using hh
  have hh := CentralBinomialNormalizedAntitone.normalized_antitone hn
  norm_num at hh
  exact hh

private theorem two_rates_mono (x y C m P R : ℝ)
    (hx : x ≤ m) (hy : y ≤ C) (hR : 0 ≤ R) (hRP : R ≤ P) :
    x*P+(y-x)*R ≤ m*P+(C-m)*R := by
  have h₁ := mul_le_mul_of_nonneg_right hx (sub_nonneg.mpr hRP)
  have h₂ := mul_le_mul_of_nonneg_right hy hR
  nlinarith only [h₁,h₂]

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]
    (S : ActualWreathCompressionState Q I)

theorem exists_cost (i : I) (hI : 2 ≤ Fintype.card I)
    (N C m : ℕ) (hN : N ≠ 0) (horder : Nat.card S.D ∣ N)
    (hC : ArithmeticFunction.cardFactors N ≤ C) (hm : ∀ p : ℕ, N.factorization p ≤ m)
    (hmC : m ≤ C) (q a : ℕ) (hq : q.Prime) (ha : 1 ≤ a)
    (hdiv : q^a ∣ Fintype.card I)
    (hmax : ∀ p ∈ (Fintype.card I).primeFactors,
      p^(Fintype.card I).factorization p ≤ q^a) :
    ∃ c : ℕ, ChiefCost i S c ∧ MarkedC4.genRank S.A ≤ c+MarkedC4.genRank Q ∧
      (c : ℝ) ≤ ((2*(m : ℝ)+3*(C : ℝ))/5)*(Fintype.card I : ℝ)/
        Real.sqrt (Real.logb 2 (Fintype.card I : ℝ)) ∧
      (8 ≤ q^a → (c : ℝ) ≤ ((2*(m : ℝ)+(C : ℝ))/8)*(Fintype.card I : ℝ)) := by
  let t := Fintype.card I
  let M := q^a
  let V : ℝ := (t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))
  let W : ℕ → ℝ := ActualWreathUnitDivisorWeightBudget.weight t q a
  have ht : 2 ≤ t := hI
  have ht0 : 0 < t := by omega
  have htR : (0 : ℝ) ≤ t := by positivity
  have hM1 : 1 ≤ M := Nat.one_le_pow _ _ hq.pos
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M from pow_pos hq.pos a)
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hmCR : (m : ℝ) ≤ C := by exact_mod_cast hmC
  have hCm : 0 ≤ (C : ℝ)-(m : ℝ) := sub_nonneg.mpr hmCR
  have hmq : (N.factorization q : ℝ) ≤ m := by exact_mod_cast hm q
  have hC' : (ArithmeticFunction.cardFactors N : ℝ) ≤ C := by exact_mod_cast hC
  have hw1 (p : ℕ) : 1 ≤ W p :=
    ActualWreathUnitDivisorWeightBudget.one_le_weight t ht q a p
  have hwU (p : ℕ) : W p ≤ V := min_le_left _ _
  have hwD (p : ℕ) : W p ≤ divisorRate t q a p :=
    (min_le_right _ _).trans (divisorWeight_le_divisorRate t q a p ht0 hq hdiv)
  have hwOther (p : ℕ) (hp : p ≠ q) : W p ≤ (t : ℝ)/(M : ℝ) := by
    simpa only [divisorRate,if_neg hp,M,Nat.cast_pow] using hwD p
  have hwPrimary : W q ≤ (t : ℝ)*primaryRate q a := by
    simpa only [divisorRate,if_pos rfl] using hwD q
  have hrec : (t : ℝ)/(M : ℝ) ≤ (3/5)*V := by
    simpa only [V,mul_div_assoc] using
      LargestPrimePowerQuadraticEntropy.reciprocal_rate_le_three_fifths t M ht hM1 hmax
  obtain ⟨c,hc⟩ := ActualWreathOrdinaryChiefRecurrence.exists_chiefCost i S
  have hcost := ActualWreathUnitDivisorWeightBudget.cost_le_weightedOrder hc hI q a hq hdiv
  have hlocal := weightedOrder_mono_of_dvd W
    (fun p => (show (0 : ℝ) ≤ 1 by norm_num).trans (hw1 p))
    (Nat.card_pos (α := S.D)).ne' hN horder
  have htotal : (c : ℝ) ≤ weightedOrder W N := hcost.trans hlocal
  have htwo (P R : ℝ) (hP : W q ≤ P) (hR : ∀ p, p ≠ q → W p ≤ R)
      (hR0 : 0 ≤ R) (hRP : R ≤ P) :
      (c : ℝ) ≤ (m : ℝ)*P+((C : ℝ)-(m : ℝ))*R := by
    have hh := PrimeMultiplicityTwoRateBound.weightedOrder_le_two_rates W N q P R hP hR
    exact (htotal.trans hh).trans
      (two_rates_mono _ _ _ _ _ _ hmq hC' hR0 hRP)
  have hlogCost : (c : ℝ) ≤ ((2*(m : ℝ)+3*(C : ℝ))/5)*V := by
    have hRP : (t : ℝ)/(M : ℝ) ≤ V := hrec.trans (by nlinarith only [hV])
    have hh := htwo V ((t : ℝ)/(M : ℝ)) (hwU q) hwOther (by positivity) hRP
    have hr := mul_le_mul_of_nonneg_left hrec hCm
    calc
      (c : ℝ) ≤ (m : ℝ)*V+((C : ℝ)-(m : ℝ))*((t : ℝ)/(M : ℝ)) := hh
      _ ≤ (m : ℝ)*V+((C : ℝ)-(m : ℝ))*((3/5)*V) := add_le_add le_rfl hr
      _ = ((2*(m : ℝ)+3*(C : ℝ))/5)*V := by ring
  refine ⟨c,hc,genRank_le_cost_add_top hc,?_,?_⟩
  · convert hlogCost using 1 <;> dsimp only [V,t] <;> ring
  · intro hM8
    have hM8R : (8 : ℝ) ≤ M := by exact_mod_cast hM8
    have hrec8 : (t : ℝ)/(M : ℝ) ≤ (t : ℝ)/8 := by
      apply (div_le_iff₀ hMpos).mpr
      have hh := mul_le_mul_of_nonneg_left hM8R htR
      nlinarith only [hh]
    have hr := primary_rate_le_three_eighths q a hq ha hM8
    have hP : W q ≤ (3/8)*(t : ℝ) := by
      have hh := hwPrimary.trans (mul_le_mul_of_nonneg_left hr htR)
      convert hh using 1 <;> ring
    have hRP : (t : ℝ)/(M : ℝ) ≤ (3/8)*(t : ℝ) :=
      hrec8.trans (by nlinarith only [htR])
    have hh := htwo ((3/8)*(t : ℝ)) ((t : ℝ)/(M : ℝ)) hP hwOther (by positivity) hRP
    have he := mul_le_mul_of_nonneg_left hrec8 hCm
    calc
      (c : ℝ) ≤ (m : ℝ)*((3/8)*(t : ℝ))+
          ((C : ℝ)-(m : ℝ))*((t : ℝ)/(M : ℝ)) := hh
      _ ≤ (m : ℝ)*((3/8)*(t : ℝ))+((C : ℝ)-(m : ℝ))*((t : ℝ)/8) :=
        add_le_add le_rfl he
      _ = ((2*(m : ℝ)+(C : ℝ))/8)*(Fintype.card I : ℝ) := by dsimp only [t]; ring

end SymmetricSubgroupAsymptotics.ActualWreathBoundedMultiplicityJointCost
