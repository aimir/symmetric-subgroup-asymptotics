import SymmetricSubgroupAsymptotics.ActualWreathChiefPrimeMultiplicityBudget
import Mathlib.Data.Finsupp.Order

/-! A real weighted prime-multiplicity budget on the SAME actual chief
trace. Weights bound the actual per-characteristic elementary capacities;
their lower bound one also pays genuine nonabelian internal-factor ranks.
The generic capacity hypothesis is not an ordinary-generator or aggregate
assumption. Concrete divisor/induced-bound weights are installed separately. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ActualWreathChiefWeightedPrimeBudget
open PermutationalWreathProduct ActualWreathCharacteristicChiefProfile
open ActualWreathChiefPrimeMultiplicityBudget

/-- Every prime exponent is counted with its own nonnegative real rate. -/
def weightedOrder (weight : ℕ → ℝ) (M : ℕ) : ℝ :=
  M.factorization.sum (fun p a => (a : ℝ)*weight p)

theorem weightedOrder_nonneg (weight : ℕ → ℝ) (hw : ∀ p, 0 ≤ weight p) (M : ℕ) :
    0 ≤ weightedOrder weight M := by
  unfold weightedOrder
  exact Finsupp.sum_nonneg (fun p _ => mul_nonneg (by positivity) (hw p))

theorem weightedOrder_mul (weight : ℕ → ℝ) {M N : ℕ}
    (hM : M ≠ 0) (hN : N ≠ 0) :
    weightedOrder weight (M*N) = weightedOrder weight M + weightedOrder weight N := by
  unfold weightedOrder
  rw [Nat.factorization_mul hM hN,Finsupp.sum_add_index']
  · intro p
    simp
  · intro p a b
    push_cast
    ring

theorem weightedOrder_prime_pow (weight : ℕ → ℝ) {p a : ℕ} (hp : p.Prime) :
    weightedOrder weight (p^a) = (a : ℝ)*weight p := by
  unfold weightedOrder
  rw [hp.factorization_pow]
  exact Finsupp.sum_single_index (by simp)

theorem weightedOrder_mono_of_dvd (weight : ℕ → ℝ) (hw : ∀ p, 0 ≤ weight p)
    {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (hd : M ∣ N) :
    weightedOrder weight M ≤ weightedOrder weight N := by
  unfold weightedOrder
  apply Finsupp.sum_le_sum_index ((Nat.factorization_le_iff_dvd hM hN).mpr hd)
  · intro p _ a b hab
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (hw p)
  · intro p _
    simp

theorem cardFactors_le_weightedOrder (weight : ℕ → ℝ) (hw : ∀ p, 1 ≤ weight p)
    (M : ℕ) : (ArithmeticFunction.cardFactors M : ℝ) ≤ weightedOrder weight M := by
  have heq : (ArithmeticFunction.cardFactors M : ℝ) =
      M.factorization.sum (fun _ a => (a : ℝ)) := by
    rw [ArithmeticFunction.cardFactors_eq_sum_factorization]
    simp only [Finsupp.sum,Nat.cast_sum]
  rw [heq]
  unfold weightedOrder
  rw [Finsupp.sum,Finsupp.sum]
  apply Finset.sum_le_sum
  intro p _
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (hw p) (show (0 : ℝ) ≤ M.factorization p by positivity)

theorem genRank_le_weightedOrder (weight : ℕ → ℝ) (hw : ∀ p, 1 ≤ weight p)
    (G : Type*) [Group G] [Finite G] :
    (MarkedC4.genRank G : ℝ) ≤ weightedOrder weight (Nat.card G) := by
  have h := FiniteGroupPrimeMultiplicityGenerators.genRank_le_cardFactors G
  exact (show (MarkedC4.genRank G : ℝ) ≤ ArithmeticFunction.cardFactors (Nat.card G) by
    exact_mod_cast h).trans (cardFactors_le_weightedOrder weight hw _)

section Chief
variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]

theorem cost_le_weightedOrder {i : I} {S : ActualWreathCompressionState Q I} {n : ℕ}
    (h : ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n)
    (hI : 2 ≤ Fintype.card I) (weight : ℕ → ℝ) (hw : ∀ p, 1 ≤ weight p)
    (hcap : ∀ c : ElementaryCharge (Fintype.card I),
      (c.capacity : ℝ) ≤ (c.dimension : ℝ)*weight c.p) :
    (n : ℝ) ≤ weightedOrder weight (Nat.card S.D) := by
  have hw0 : ∀ p, 0 ≤ weight p := fun p => le_trans (by norm_num) (hw p)
  induction h with
  | terminal S hD =>
      simpa only [Nat.cast_zero] using weightedOrder_nonneg weight hw0 (Nat.card S.D)
  | vanishing S D' phi hphi hmin hz n next ih =>
      exact ih.trans (weightedOrder_mono_of_dvd weight hw0
        (Nat.card_pos (α := D')).ne' (Nat.card_pos (α := S.D)).ne'
        (Subgroup.card_dvd_of_surjective phi hphi))
  | elementary S D' phi hphi hmin C n next ih =>
      have hc := hcap (actualCharge S phi C i hI)
      change (ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i : ℝ) ≤
        (Module.finrank (ZMod C.p) C.V : ℝ)*weight C.p at hc
      have heq : (Module.finrank (ZMod C.p) C.V : ℝ)*weight C.p =
          weightedOrder weight (Nat.card phi.ker) := by
        rw [ActualWreathChiefHalfOrderBudget.elementary_kernel_card phi C,
          weightedOrder_prime_pow weight C.p_prime]
      have hc' := hc.trans_eq heq
      change (n : ℝ) ≤ weightedOrder weight (Nat.card D') at ih
      have hh := add_le_add hc' ih
      rw [←weightedOrder_mul weight (Nat.card_pos (α := phi.ker)).ne'
        (Nat.card_pos (α := D')).ne',
        ActualWreathChiefHalfOrderBudget.card_kernel_mul_card_of_surjective phi hphi] at hh
      simpa only [Nat.cast_add] using hh
  | nonabelian S D' phi hphi hmin hnc hne C j n next ih =>
      have hc := factor_genRank_le_local_cardFactors S.rho phi S.rho_injective C j
      have hcR : (MarkedC4.genRank (C.factor j) : ℝ) ≤
          ArithmeticFunction.cardFactors (Nat.card phi.ker) := by exact_mod_cast hc
      have hc' := hcR.trans (cardFactors_le_weightedOrder weight hw (Nat.card phi.ker))
      change (n : ℝ) ≤ weightedOrder weight (Nat.card D') at ih
      have hh := add_le_add hc' ih
      rw [←weightedOrder_mul weight (Nat.card_pos (α := phi.ker)).ne'
        (Nat.card_pos (α := D')).ne',
        ActualWreathChiefHalfOrderBudget.card_kernel_mul_card_of_surjective phi hphi] at hh
      simpa only [Nat.cast_add] using hh

theorem exists_weightedOrder_bound (S : ActualWreathCompressionState Q I)
    (i : I) (hI : 2 ≤ Fintype.card I) (weight : ℕ → ℝ) (hw : ∀ p, 1 ≤ weight p)
    (hcap : ∀ c : ElementaryCharge (Fintype.card I),
      (c.capacity : ℝ) ≤ (c.dimension : ℝ)*weight c.p) :
    ∃ n : ℕ, ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n ∧
      (n : ℝ) ≤ weightedOrder weight (Nat.card S.D) ∧
      MarkedC4.genRank S.A ≤ n + MarkedC4.genRank Q := by
  obtain ⟨n,hn⟩ := ActualWreathOrdinaryChiefRecurrence.exists_chiefCost i S
  exact ⟨n,hn,cost_le_weightedOrder hn hI weight hw hcap,
    ActualWreathOrdinaryChiefRecurrence.genRank_le_cost_add_top hn⟩
end Chief
end SymmetricSubgroupAsymptotics.ActualWreathChiefWeightedPrimeBudget
