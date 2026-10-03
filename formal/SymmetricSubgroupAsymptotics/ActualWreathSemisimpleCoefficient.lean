import SymmetricSubgroupAsymptotics.ActualWreathElementaryCoefficient
import SymmetricSubgroupAsymptotics.ActualWreathCompressionTrace
import SymmetricSubgroupAsymptotics.SemisimpleOuterFactorPublished
import SymmetricSubgroupAsymptotics.FixedTargetCompositionEnvelope

/-!
# Uniform semisimple coefficient of an actual affine wreath tower

The simple factors in a quotient tower are sections of the local component,
so they need not themselves occur as literal permutation subgroups.  We use
the published primitive-generator corollary on each factor's regular action.
Scott provenance then charges every retained diagonal factor to a distinct
block/local-factor coordinate.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- A simple group's automorphism group is paid solely from its order.  This
is the published faithful-simple generator theorem applied to the regular
action, followed by the standard generating-tuple count. -/
theorem simpleAut_card_le_card_pow_log2
    (hgen : FaithfulSimplePermutationGeneratorBound)
    (G : Type) [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (hcenter : IsCenterless G) :
    Nat.card (G ≃* G) ≤ Nat.card G ^ Nat.log2 (Nat.card G) := by
  letI : Fintype G := Fintype.ofFinite G
  let e : G ≃ Fin (Fintype.card G) := Fintype.equivFin G
  let rho : G →* Equiv.Perm (Fin (Fintype.card G)) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G G)
  have hrho : Function.Injective rho :=
    e.permCongrHom.injective.comp MulAction.toPerm_injective
  obtain ⟨S, hS, hScard⟩ := hgen (Fintype.card G) G hsimple hcenter
    rho hrho
  letI : Finite (G →* G) := Finite.of_injective
    (fun f : G →* G => (f : G → G)) DFunLike.coe_injective
  calc
    Nat.card (G ≃* G) ≤ Nat.card (G →* G) :=
      Nat.card_le_card_of_injective (fun a => a.toMonoidHom)
        (fun _ _ h => MulEquiv.ext (fun x => DFunLike.congr_fun h x))
    _ ≤ Nat.card G ^ S.card := monoidHom_card_le_pow_of_closure S hS
    _ ≤ Nat.card G ^ Nat.log2 (Nat.card G) := by
      simpa only [Nat.card_eq_fintype_card] using
        Nat.pow_le_pow_right (Nat.card_pos (α := G)) hScard

private theorem one_le_simple_logb
    (G : Type) [Group G] [Finite G] (hsimple : IsSimpleGroup G) :
    (1 : ℝ) ≤ Real.logb 2 (Nat.card G) := by
  letI : IsSimpleGroup G := hsimple
  rw [Real.le_logb_iff_rpow_le (by norm_num)
    (by exact_mod_cast (Nat.card_pos (α := G)))]
  norm_num
  exact_mod_cast Finite.one_lt_card (α := G)

/-- The fixed semisimple polynomial constant costs at most twice the square
of the total base-two logarithmic order of its simple factors. -/
theorem semisimplePolynomialConstant_le_orderLogSquare
    (hgen : FaithfulSimplePermutationGeneratorBound)
    {G : Type} [Group G] {E : Subgroup G}
    (C : SemisimpleNormalChart E) :
    FixedTargetCompositionEnvelope.semisimplePolynomialConstant C ≤
      (2 : ℝ) ^
        (2 * (∑ i : C.ι,
          Real.logb 2 (Nat.card (C.factor i))) ^ 2) := by
  have hfactor : ∀ i : C.ι,
      1 + (Nat.card (C.factor i ≃* C.factor i) : ℝ) /
          Real.logb 2 (Nat.card (C.factor i)) ≤
        (2 : ℝ) ^
          (2 * (Real.logb 2 (Nat.card (C.factor i))) ^ 2) := by
    intro i
    let a : ℝ := Real.logb 2 (Nat.card (C.factor i))
    have ha1 : 1 ≤ a := one_le_simple_logb (C.factor i) (C.simple i)
    have ha0 : 0 ≤ a := zero_le_one.trans ha1
    have hautNat := simpleAut_card_le_card_pow_log2 hgen (C.factor i)
      (C.simple i) (C.centerless i)
    have haut : (Nat.card (C.factor i ≃* C.factor i) : ℝ) ≤
        (Nat.card (C.factor i) : ℝ) ^ Nat.log2 (Nat.card (C.factor i)) := by
      exact_mod_cast hautNat
    have hlog2 : (Nat.log2 (Nat.card (C.factor i)) : ℝ) ≤ a :=
      Real.log2_le_logb (Nat.card (C.factor i))
    have hcardpos : (0 : ℝ) < Nat.card (C.factor i) := by
      exact_mod_cast Nat.card_pos (α := C.factor i)
    have hcard : (Nat.card (C.factor i) : ℝ) = (2 : ℝ) ^ a := by
      dsimp [a]
      exact (Real.rpow_logb (by norm_num) (by norm_num) hcardpos).symm
    have hautExp : (Nat.card (C.factor i ≃* C.factor i) : ℝ) ≤
        (2 : ℝ) ^ (a ^ 2) := by
      calc
        _ ≤ (Nat.card (C.factor i) : ℝ) ^ Nat.log2 (Nat.card (C.factor i)) := haut
        _ = ((2 : ℝ) ^ a) ^ (Nat.log2 (Nat.card (C.factor i)) : ℕ) := by rw [← hcard]
        _ = ((2 : ℝ) ^ a) ^ (Nat.log2 (Nat.card (C.factor i)) : ℝ) := by
          rw [Real.rpow_natCast]
        _ = (2 : ℝ) ^ (a * (Nat.log2 (Nat.card (C.factor i)) : ℝ)) := by
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        _ ≤ (2 : ℝ) ^ (a ^ 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
            convert mul_le_mul_of_nonneg_left hlog2 ha0 using 1 <;> ring)
    have hdiv : (Nat.card (C.factor i ≃* C.factor i) : ℝ) / a ≤
        (2 : ℝ) ^ (a ^ 2) := by
      exact (div_le_self (by positivity) ha1).trans hautExp
    calc
      1 + (Nat.card (C.factor i ≃* C.factor i) : ℝ) /
          Real.logb 2 (Nat.card (C.factor i)) ≤
          1 + (2 : ℝ) ^ (a ^ 2) := by simpa [a] using add_le_add_left hdiv 1
      _ ≤ 2 * (2 : ℝ) ^ (a ^ 2) := by
        have : (1 : ℝ) ≤ (2 : ℝ) ^ (a ^ 2) := by
          simpa using Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (sq_nonneg a)
        linarith
      _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (a ^ 2) := by norm_num
      _ = (2 : ℝ) ^ (1 + a ^ 2) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (2 : ℝ) ^ (2 * a ^ 2) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith
      _ = (2 : ℝ) ^
          (2 * (Real.logb 2 (Nat.card (C.factor i))) ^ 2) := rfl
  unfold FixedTargetCompositionEnvelope.semisimplePolynomialConstant
  calc
    (∏ i : C.ι, (1 +
        (Nat.card (C.factor i ≃* C.factor i) : ℝ) /
          Real.logb 2 (Nat.card (C.factor i)))) ≤
      ∏ i : C.ι, (2 : ℝ) ^
        (2 * (Real.logb 2 (Nat.card (C.factor i))) ^ 2) :=
      Finset.prod_le_prod
        (fun i _ => add_nonneg zero_le_one (div_nonneg (by positivity)
          (C.logb_card_pos i).le))
        (fun i _ => hfactor i)
    _ = (2 : ℝ) ^ (∑ i : C.ι,
        2 * (Real.logb 2 (Nat.card (C.factor i))) ^ 2) := by
      exact (Real.rpow_sum_of_pos (by norm_num) _ Finset.univ).symm
    _ ≤ (2 : ℝ) ^
        (2 * (∑ i : C.ι,
          Real.logb 2 (Nat.card (C.factor i))) ^ 2) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hnonneg : ∀ i : C.ι,
          0 ≤ Real.logb 2 (Nat.card (C.factor i)) := fun i =>
        Real.logb_nonneg (by norm_num)
          (by exact_mod_cast Nat.card_pos (α := C.factor i))
      have hsquares := Finset.sum_sq_le_sq_sum_of_nonneg
        (s := (Finset.univ : Finset C.ι)) (fun i _ => hnonneg i)
      calc
        (∑ i : C.ι, 2 * Real.logb 2 (Nat.card (C.factor i)) ^ 2) =
            2 * ∑ i : C.ι, Real.logb 2 (Nat.card (C.factor i)) ^ 2 := by
          rw [Finset.mul_sum]
        _ ≤ 2 * (∑ i : C.ι,
            Real.logb 2 (Nat.card (C.factor i))) ^ 2 :=
          mul_le_mul_of_nonneg_left hsquares (by norm_num)

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]

namespace ActualWreathCompressionTower

/-- Source-independent logarithmic cost of the semisimple constants in the
actual tower, charged to the literal local factors before Scott diagonals
are selected. -/
noncomputable def semisimpleCoefficientLogCost :
    {S : ActualWreathCompressionState Q I} →
      ActualWreathCompressionTower S → ℝ
  | _, .terminal _ _ => 0
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact semisimpleCoefficientLogCost next
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact 2 * ((Fintype.card I : ℝ) *
        (∑ i : C.ι, Real.logb 2 (Nat.card (C.factor i)))) ^ 2 +
          semisimpleCoefficientLogCost next

/-- The total simple-factor logarithm of the actual kernel section is no
larger than the blockwise copies of the literal local factor logarithms. -/
theorem kernelSemisimple_factorLogSum_le
    {S : ActualWreathCompressionState Q I}
    {D' : Type} [Group D'] [Finite D']
    (phi : S.D →* D') (_hphi : Function.Surjective phi)
    (C : SemisimpleNormalChart phi.ker) :
    let E :=
      PermutationalWreathProduct.Compression.kernelSemisimpleChartOfFullComponent
        S.rho phi S.rho_injective S.fullComponent C
    (∑ j : E.ι, Real.logb 2 (Nat.card (E.factor j))) ≤
      (Fintype.card I : ℝ) *
        ∑ i : C.ι, Real.logb 2 (Nat.card (C.factor i)) := by
  dsimp only
  have h :=
    PermutationalWreathProduct.Compression.kernelSemisimpleChartOfFullComponent_sum_factorCard_le
        S.rho phi S.rho_injective S.fullComponent C
        (fun n => Real.logb 2 n)
        (fun n => by
          by_cases hn : n = 0
          · subst n
            simp [Real.logb]
          · exact Real.logb_nonneg (by norm_num)
              (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)))
  calc
    _ ≤ ∑ p : I × C.ι,
        Real.logb 2 (Nat.card (C.factor p.2)) := h
    _ = (Fintype.card I : ℝ) *
        ∑ i : C.ι, Real.logb 2 (Nat.card (C.factor i)) := by
      simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]

/-- The semisimple cost is bounded by the square of the exact local
semisimple order budget. -/
theorem semisimpleCoefficientLogCost_le :
    {S : ActualWreathCompressionState Q I} →
      (T : ActualWreathCompressionTower S) →
      T.semisimpleCoefficientLogCost ≤
        2 * (Fintype.card I : ℝ) ^ 2 * T.semisimpleLogBudget ^ 2
  | _, .terminal _ _ => by
      simp [semisimpleCoefficientLogCost, semisimpleLogBudget]
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      simpa only [semisimpleCoefficientLogCost, semisimpleLogBudget] using
        semisimpleCoefficientLogCost_le next
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      have hnext := semisimpleCoefficientLogCost_le next
      have hx0 : 0 ≤ ∑ i : C.ι,
          Real.logb 2 (Nat.card (C.factor i)) :=
        Finset.sum_nonneg fun i _ => Real.logb_nonneg (by norm_num)
          (by exact_mod_cast Nat.card_pos (α := C.factor i))
      have hn0 := semisimpleLogBudget_nonneg next
      simp only [semisimpleCoefficientLogCost, semisimpleLogBudget]
      nlinarith [mul_nonneg hx0 hn0,
        mul_nonneg (sq_nonneg (Fintype.card I : ℝ))
          (mul_nonneg hx0 hn0)]

private theorem natPow_eq_two_rpow_logb (p n : ℕ) (hp : 0 < p) :
    (p : ℝ) ^ n = (2 : ℝ) ^ (Real.logb 2 p * n) := by
  calc
    (p : ℝ) ^ n = (p : ℝ) ^ (n : ℝ) := (Real.rpow_natCast _ _).symm
    _ = ((2 : ℝ) ^ (Real.logb 2 p)) ^ (n : ℝ) := by
      rw [Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast hp)]
    _ = (2 : ℝ) ^ (Real.logb 2 p * n) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- The complete source-independent constant of the tower is paid by the
sum of its elementary and semisimple logarithmic costs. -/
theorem coefficientConstant_le_two_rpow_cost
    (hgen : FaithfulSimplePermutationGeneratorBound) :
    {S : ActualWreathCompressionState Q I} →
      (T : ActualWreathCompressionTower S) →
      T.coefficientConstant ≤ (2 : ℝ) ^
        (T.elementaryCoefficientLogCost + T.semisimpleCoefficientLogCost)
  | _, .terminal _ _ => by
      simp [coefficientConstant, elementaryCoefficientLogCost,
        semisimpleCoefficientLogCost]
  | S, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      have ih := coefficientConstant_le_two_rpow_cost hgen next
      rw [coefficientConstant, elementaryCoefficientLogCost,
        semisimpleCoefficientLogCost,
        natPow_eq_two_rpow_logb C.p _ C.p_prime.pos]
      calc
        _ ≤ (2 : ℝ) ^ (Real.logb 2 C.p *
              traceyAffineCoefficientExponent
                (Module.finrank (ZMod C.p) C.V) (Fintype.card I)
                (traceyInducedGeneratorCeiling
                  (Module.finrank (ZMod C.p) C.V) (Fintype.card I))
                S.generatorCount S.sourceDegree C.p) *
            (2 : ℝ) ^ (next.elementaryCoefficientLogCost +
              next.semisimpleCoefficientLogCost) :=
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
      have hpoly := semisimplePolynomialConstant_le_orderLogSquare hgen E
      have hsum := kernelSemisimple_factorLogSum_le phi hphi C
      have hsum0 : 0 ≤ ∑ j : E.ι,
          Real.logb 2 (Nat.card (E.factor j)) :=
        Finset.sum_nonneg fun j _ => Real.logb_nonneg (by norm_num)
          (by exact_mod_cast Nat.card_pos (α := E.factor j))
      have hlocal0 : 0 ≤ (Fintype.card I : ℝ) *
          ∑ i : C.ι, Real.logb 2 (Nat.card (C.factor i)) := by
        exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ =>
          Real.logb_nonneg (by norm_num)
            (by exact_mod_cast Nat.card_pos (α := C.factor i)))
      have hpoly' :
          FixedTargetCompositionEnvelope.semisimplePolynomialConstant E ≤
            (2 : ℝ) ^ (2 * ((Fintype.card I : ℝ) *
              ∑ i : C.ι, Real.logb 2 (Nat.card (C.factor i))) ^ 2) :=
        hpoly.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
          nlinarith [sq_le_sq₀ hsum0 hlocal0 |>.2 hsum]))
      have ih := coefficientConstant_le_two_rpow_cost hgen next
      rw [coefficientConstant, elementaryCoefficientLogCost,
        semisimpleCoefficientLogCost]
      calc
        _ ≤ (2 : ℝ) ^ (2 * ((Fintype.card I : ℝ) *
              ∑ i : C.ι, Real.logb 2 (Nat.card (C.factor i))) ^ 2) *
            (2 : ℝ) ^ (next.elementaryCoefficientLogCost +
              next.semisimpleCoefficientLogCost) :=
          mul_le_mul hpoly' ih (coefficientConstant_nonneg next) (by positivity)
        _ = _ := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1
          ring

/-- The source-polynomial degree contributed by the actual semisimple
sections is bounded by twice the block count times the exact local
semisimple logarithmic order budget. -/
theorem coefficientPolynomialDegree_le_semisimpleLogBudget :
    {S : ActualWreathCompressionState Q I} →
      (T : ActualWreathCompressionTower S) →
      (T.coefficientPolynomialDegree : ℝ) ≤
        2 * (Fintype.card I : ℝ) * T.semisimpleLogBudget
  | _, .terminal _ _ => by
      simp [coefficientPolynomialDegree, semisimpleLogBudget]
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      simpa only [coefficientPolynomialDegree, semisimpleLogBudget] using
        coefficientPolynomialDegree_le_semisimpleLogBudget next
  | S, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      let E :=
        PermutationalWreathProduct.Compression.kernelSemisimpleChartOfFullComponent
          S.rho phi S.rho_injective S.fullComponent C
      have hsum := kernelSemisimple_factorLogSum_le phi hphi C
      have hcard : (Fintype.card E.ι : ℝ) ≤
          ∑ j : E.ι, Real.logb 2 (Nat.card (E.factor j)) := by
        calc
          (Fintype.card E.ι : ℝ) = ∑ _j : E.ι, (1 : ℝ) := by simp
          _ ≤ ∑ j : E.ι, Real.logb 2 (Nat.card (E.factor j)) :=
            Finset.sum_le_sum fun j _ => one_le_simple_logb
              (E.factor j) (E.simple j)
      have hlocal := hcard.trans hsum
      have ih := coefficientPolynomialDegree_le_semisimpleLogBudget next
      simp only [coefficientPolynomialDegree, semisimpleLogBudget,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      nlinarith

/-- Fully combined coefficient estimate for an actual tower.  The first
two terms are the elementary finite cost, the next is the semisimple finite
cost, and the last pays the source-polynomial degree. -/
theorem envelope_coefficient_le_two_rpow_budget
    (hgen : FaithfulSimplePermutationGeneratorBound)
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
          2 * (Fintype.card I : ℝ) ^ 2 * T.semisimpleLogBudget ^ 2 +
          2 * Fintype.card I * T.semisimpleLogBudget *
            Real.logb 2 (b + 1)) := by
  have henv := T.envelope_coefficient_le b
  have hconst := T.coefficientConstant_le_two_rpow_cost hgen
  have helem := T.elementaryCoefficientLogCost_le hs
  have hsemi := T.semisimpleCoefficientLogCost_le
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
          (T.elementaryCoefficientLogCost + T.semisimpleCoefficientLogCost) *
        (1 + (b : ℝ)) ^ T.coefficientPolynomialDegree :=
      mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = (2 : ℝ) ^
        (T.elementaryCoefficientLogCost + T.semisimpleCoefficientLogCost +
          Real.logb 2 (b + 1) * T.coefficientPolynomialDegree) := by
      rw [hpow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hdegree' := mul_le_mul_of_nonneg_left hdegree hlog0
      nlinarith

end ActualWreathCompressionTower

end SymmetricSubgroupAsymptotics

end
