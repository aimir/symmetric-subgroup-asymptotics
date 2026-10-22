import SymmetricSubgroupAsymptotics.ActualWreathSemisimpleCoefficient
import SymmetricSubgroupAsymptotics.CFSGSimpleAutomorphismOrderBound

/-! The SAME actual affine tower coefficient from the actual simple
 automorphism-square bound. No simple generating tuple is asserted;
 coefficient three, original chart and all tower budgets are unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics
private theorem one_le_simple_logb
    (G : Type) [Group G] [Finite G] (hsimple : IsSimpleGroup G) :
    (1 : ℝ) ≤ Real.logb 2 (Nat.card G) := by
  letI : IsSimpleGroup G := hsimple
  rw [Real.le_logb_iff_rpow_le (by norm_num)
    (by exact_mod_cast (Nat.card_pos (α := G)))]
  norm_num
  exact_mod_cast Finite.one_lt_card (α := G)

/-- The actual automorphism-square bound gives the same linear constant. -/
theorem semisimplePolynomialConstant_le_orderLog_of_autSquare
    (hAut : FiniteSimpleAutomorphismSquareBound)
    {G : Type} [Group G] {E : Subgroup G}
    (C : SemisimpleNormalChart E) :
    FixedTargetCompositionEnvelope.semisimplePolynomialConstant C ≤
      (2 : ℝ) ^
        (3 * ∑ i : C.ι, Real.logb 2 (Nat.card (C.factor i))) := by
  have hfactor : ∀ i : C.ι,
      1 + (Nat.card (C.factor i ≃* C.factor i) : ℝ) /
          Real.logb 2 (Nat.card (C.factor i)) ≤
        (2 : ℝ) ^
          (3 * Real.logb 2 (Nat.card (C.factor i))) := by
    intro i
    let a : ℝ := Real.logb 2 (Nat.card (C.factor i))
    have ha1 : 1 ≤ a := one_le_simple_logb (C.factor i) (C.simple i)
    have ha0 : 0 ≤ a := zero_le_one.trans ha1
    have hautNat := hAut (C.factor i)
      (C.simple i) (C.centerless i)
    have haut : (Nat.card (C.factor i ≃* C.factor i) : ℝ) ≤
        (Nat.card (C.factor i) : ℝ) ^ (2 : ℕ) := by exact_mod_cast hautNat
    have hcardpos : (0 : ℝ) < Nat.card (C.factor i) := by
      exact_mod_cast Nat.card_pos (α := C.factor i)
    have hcard : (Nat.card (C.factor i) : ℝ) = (2 : ℝ) ^ a := by
      dsimp [a]
      exact (Real.rpow_logb (by norm_num) (by norm_num) hcardpos).symm
    have hautExp : (Nat.card (C.factor i ≃* C.factor i) : ℝ) ≤
        (2 : ℝ) ^ (2 * a) := by
      calc
        _ ≤ (Nat.card (C.factor i) : ℝ) ^ (2 : ℕ) := haut
        _ = ((2 : ℝ) ^ a) ^ (2 : ℝ) := by rw [← hcard, Real.rpow_two]
        _ = (2 : ℝ) ^ (a * 2) := by
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        _ = (2 : ℝ) ^ (2 * a) := by ring_nf
    have hdiv : (Nat.card (C.factor i ≃* C.factor i) : ℝ) / a ≤
        (2 : ℝ) ^ (2 * a) :=
      (div_le_self (by positivity) ha1).trans hautExp
    calc
      1 + (Nat.card (C.factor i ≃* C.factor i) : ℝ) /
          Real.logb 2 (Nat.card (C.factor i)) ≤
          1 + (2 : ℝ) ^ (2 * a) := by simpa [a] using add_le_add_left hdiv 1
      _ ≤ 2 * (2 : ℝ) ^ (2 * a) := by
        have : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * a) := by
          exact Real.one_le_rpow (by norm_num) (mul_nonneg (by norm_num) ha0)
        linarith
      _ = (2 : ℝ) ^ (1 + 2 * a) := by
        calc
          _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (2 * a) := by norm_num
          _ = _ := by rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (2 : ℝ) ^ (3 * a) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith
      _ = _ := rfl
  unfold FixedTargetCompositionEnvelope.semisimplePolynomialConstant
  calc
    (∏ i : C.ι, (1 +
        (Nat.card (C.factor i ≃* C.factor i) : ℝ) /
          Real.logb 2 (Nat.card (C.factor i)))) ≤
      ∏ i : C.ι, (2 : ℝ) ^
        (3 * Real.logb 2 (Nat.card (C.factor i))) :=
      Finset.prod_le_prod
        (fun i _ => add_nonneg zero_le_one (div_nonneg (by positivity)
          (C.logb_card_pos i).le))
        (fun i _ => hfactor i)
    _ = (2 : ℝ) ^ (∑ i : C.ι,
        3 * Real.logb 2 (Nat.card (C.factor i))) := by
      exact (Real.rpow_sum_of_pos (by norm_num) _ Finset.univ).symm
    _ = (2 : ℝ) ^
        (3 * ∑ i : C.ι, Real.logb 2 (Nat.card (C.factor i))) := by
      rw [Finset.mul_sum]

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]
namespace ActualWreathCompressionTower
private theorem natPow_eq_two_rpow_logb (p n : ℕ) (hp : 0 < p) :
    (p : ℝ) ^ n = (2 : ℝ) ^ (Real.logb 2 p * n) := by
  calc
    (p : ℝ) ^ n = (p : ℝ) ^ (n : ℝ) := (Real.rpow_natCast _ _).symm
    _ = ((2 : ℝ) ^ (Real.logb 2 p)) ^ (n : ℝ) := by
      rw [Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast hp)]
    _ = (2 : ℝ) ^ (Real.logb 2 p * n) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- Linear semisimple variant of the tower constant bound. -/
theorem coefficientConstant_le_two_rpow_linearCost_of_autSquare
    (hAut : FiniteSimpleAutomorphismSquareBound) :
    {S : ActualWreathCompressionState Q I} →
      (T : ActualWreathCompressionTower S) →
      T.coefficientConstant ≤ (2 : ℝ) ^
        (T.elementaryCoefficientLogCost +
          T.semisimpleLinearCoefficientLogCost)
  | _, .terminal _ _ => by
      simp [coefficientConstant, elementaryCoefficientLogCost,
        semisimpleLinearCoefficientLogCost]
  | S, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log capacity_refined
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      have ih := coefficientConstant_le_two_rpow_linearCost_of_autSquare hAut next
      rw [coefficientConstant, elementaryCoefficientLogCost,
        semisimpleLinearCoefficientLogCost,
        natPow_eq_two_rpow_logb C.p _ C.p_prime.pos]
      calc
        _ ≤ (2 : ℝ) ^ (Real.logb 2 C.p *
              traceyAffineCoefficientExponent
                (Module.finrank (ZMod C.p) C.V) (Fintype.card I)
                (traceyInducedGeneratorCeiling
                  (Module.finrank (ZMod C.p) C.V) (Fintype.card I))
                S.generatorCount S.sourceDegree C.p) *
            (2 : ℝ) ^ (next.elementaryCoefficientLogCost +
              next.semisimpleLinearCoefficientLogCost) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = _ := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1
          ring
  | S, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      let E :=
        PermutationalWreathProduct.Compression.kernelSemisimpleChartOfFullComponent
          S.rho phi S.rho_injective S.fullComponent C
      have hpoly := semisimplePolynomialConstant_le_orderLog_of_autSquare hAut E
      have hsum := kernelSemisimple_factorLogSum_le phi hphi C
      have hpoly' :
          FixedTargetCompositionEnvelope.semisimplePolynomialConstant E ≤
            (2 : ℝ) ^ (3 * (Fintype.card I : ℝ) *
              ∑ i : C.ι, Real.logb 2 (Nat.card (C.factor i))) :=
        hpoly.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
          simpa [mul_assoc] using
            mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 3)))
      have ih := coefficientConstant_le_two_rpow_linearCost_of_autSquare hAut next
      rw [coefficientConstant, elementaryCoefficientLogCost,
        semisimpleLinearCoefficientLogCost]
      calc
        _ ≤ (2 : ℝ) ^ (3 * (Fintype.card I : ℝ) *
              ∑ i : C.ι, Real.logb 2 (Nat.card (C.factor i))) *
            (2 : ℝ) ^ (next.elementaryCoefficientLogCost +
              next.semisimpleLinearCoefficientLogCost) :=
          mul_le_mul hpoly' ih (coefficientConstant_nonneg next) (by positivity)
        _ = _ := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1
          ring

/-- Final coefficient estimate used by the affine menu.  Only the elementary
Tracey term is subquadratic; the semisimple constant and its source
polynomial are linear in the number of blocks. -/
theorem envelope_coefficient_le_two_rpow_linearSemisimpleBudget_of_autSquare
    (hAut : FiniteSimpleAutomorphismSquareBound)
    {S : ActualWreathCompressionState Q I}
    (T : ActualWreathCompressionTower S) (hs : 2 ≤ Fintype.card I)
    (b : ℕ) :
    T.envelope.coefficient b ≤
      (2 : ℝ) ^
        (4 * (Fintype.card I : ℝ) ^ 2 /
              Real.sqrt (Real.logb 2 (Fintype.card I)) *
                T.elementaryLogBudget ^ 2 +
          (4 * Fintype.card I * S.sourceDegree /
                Real.sqrt (Real.logb 2 (Fintype.card I)) +
              Fintype.card I * (S.generatorCount + 2) + S.sourceDegree) *
            T.elementaryLogBudget +
          3 * Fintype.card I * T.semisimpleLogBudget +
          2 * Fintype.card I * T.semisimpleLogBudget *
            Real.logb 2 (b + 1)) := by
  have henv := T.envelope_coefficient_le b
  have hconst := T.coefficientConstant_le_two_rpow_linearCost_of_autSquare hAut
  have helem := T.elementaryCoefficientLogCost_le hs
  have hsemi := T.semisimpleLinearCoefficientLogCost_eq
  have hdegree := T.coefficientPolynomialDegree_le_semisimpleLogBudget
  have hlog0 : 0 ≤ Real.logb 2 (b + 1) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ b + 1 by omega))
  have hpow : (1 + (b : ℝ)) ^ T.coefficientPolynomialDegree =
      (2 : ℝ) ^ (Real.logb 2 (b + 1) * T.coefficientPolynomialDegree) := by
    simpa [Nat.cast_add, add_comm] using
      natPow_eq_two_rpow_logb (b + 1) T.coefficientPolynomialDegree (by omega)
  calc
    T.envelope.coefficient b ≤
        T.coefficientConstant *
          (1 + (b : ℝ)) ^ T.coefficientPolynomialDegree := henv
    _ ≤ (2 : ℝ) ^
          (T.elementaryCoefficientLogCost +
            T.semisimpleLinearCoefficientLogCost) *
        (1 + (b : ℝ)) ^ T.coefficientPolynomialDegree :=
      mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = (2 : ℝ) ^
        (T.elementaryCoefficientLogCost +
            T.semisimpleLinearCoefficientLogCost +
          Real.logb 2 (b + 1) * T.coefficientPolynomialDegree) := by
      rw [hpow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hdegree' := mul_le_mul_of_nonneg_left hdegree hlog0
      rw [hsemi]
      nlinarith

end ActualWreathCompressionTower
end SymmetricSubgroupAsymptotics
