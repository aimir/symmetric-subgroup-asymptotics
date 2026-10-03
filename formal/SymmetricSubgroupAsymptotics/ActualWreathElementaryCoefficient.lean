import SymmetricSubgroupAsymptotics.ActualWreathCompressionLogBudget

/-!
# Uniform elementary coefficient of an actual affine wreath tower

Tracey's logarithmic generator ceiling is retained at each elementary chief
factor.  This file converts its literal prime-power coefficient into a
single quadratic/logarithmic expression in the exact elementary order
budget of the local component.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

private theorem traceyInducedGeneratorCeiling_cast_le
    (a s : ℕ) (hs : 2 ≤ s) :
    (traceyInducedGeneratorCeiling a s : ℝ) ≤
      4 * (a : ℝ) * s / Real.sqrt (Real.logb 2 s) + 1 := by
  unfold traceyInducedGeneratorCeiling
  have hlog : 0 < Real.logb 2 (s : ℝ) :=
    Real.logb_pos (by norm_num) (by exact_mod_cast hs)
  have hnonneg : 0 ≤
      4 * (a : ℝ) * s / Real.sqrt (Real.logb 2 s) := by positivity
  exact (Nat.ceil_lt_add_one hnonneg).le

private theorem one_le_primeLog (p : ℕ) (hp : p.Prime) :
    (1 : ℝ) ≤ Real.logb 2 p := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2) hpR
  simpa [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h

/-- One elementary layer is paid by its share `x = a log₂ p` of the exact
local-order budget.  The deliberately coarse `v/p ≤ v` keeps the statement
uniform in the prime while retaining the required logarithmic decay. -/
theorem traceyAffineCoefficientExponent_log_le
    (a s g v p : ℕ) (hp : p.Prime) (hs : 2 ≤ s) :
    Real.logb 2 p *
        traceyAffineCoefficientExponent a s
          (traceyInducedGeneratorCeiling a s) g v p ≤
      4 * (s : ℝ) ^ 2 / Real.sqrt (Real.logb 2 s) *
          ((a : ℝ) * Real.logb 2 p) ^ 2 +
        (4 * s * v / Real.sqrt (Real.logb 2 s) +
            s * (g + 2) + v) * ((a : ℝ) * Real.logb 2 p) := by
  by_cases ha : a = 0
  · subst a
    simp [traceyAffineCoefficientExponent, traceyInducedGeneratorCeiling]
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr ha)
  have hlogp1 := one_le_primeLog p hp
  have hlogp0 : 0 ≤ Real.logb 2 p := zero_le_one.trans hlogp1
  have hs0 : (0 : ℝ) ≤ s := by positivity
  have hv0 : (0 : ℝ) ≤ v := by positivity
  have hg0 : (0 : ℝ) ≤ g := by positivity
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have hsqrt : 0 < Real.sqrt (Real.logb 2 s) :=
    Real.sqrt_pos.2 (Real.logb_pos (by norm_num) (by exact_mod_cast hs))
  let H := traceyInducedGeneratorCeiling a s
  have hH := traceyInducedGeneratorCeiling_cast_le a s hs
  have hdivN : v / p ≤ v := Nat.div_le_self v p
  have hdiv : ((v / p : ℕ) : ℝ) ≤ v := by exact_mod_cast hdivN
  have ha_le_x : (a : ℝ) ≤ a * Real.logb 2 p := by
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hlogp1)]
  change Real.logb 2 p *
      ((a * s * H + H * (v / p) + a * s * (g + 1) : ℕ) : ℝ) ≤ _
  push_cast
  dsimp [H] at hH ⊢
  have hH0 : (0 : ℝ) ≤ traceyInducedGeneratorCeiling a s := by positivity
  have hbound0 : 0 ≤
      4 * (a : ℝ) * s / Real.sqrt (Real.logb 2 s) + 1 := by positivity
  have hlog_le_x : Real.logb 2 p ≤ (a : ℝ) * Real.logb 2 p := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hlogp0]
  have hterm1 : Real.logb 2 p * ((a : ℝ) * s *
      traceyInducedGeneratorCeiling a s) ≤
      4 * (s : ℝ) ^ 2 / Real.sqrt (Real.logb 2 s) *
          ((a : ℝ) * Real.logb 2 p) ^ 2 +
        s * ((a : ℝ) * Real.logb 2 p) := by
    calc
      _ ≤ Real.logb 2 p * ((a : ℝ) * s *
          (4 * (a : ℝ) * s / Real.sqrt (Real.logb 2 s) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hlogp0
        exact mul_le_mul_of_nonneg_left hH (mul_nonneg ha0 hs0)
      _ ≤ _ := by
        rw [show Real.logb 2 p * ((a : ℝ) * s *
              (4 * (a : ℝ) * s / Real.sqrt (Real.logb 2 s) + 1)) =
            (4 * (s : ℝ) ^ 2 / Real.sqrt (Real.logb 2 s) *
              ((a : ℝ) * Real.logb 2 p)) * a +
              s * ((a : ℝ) * Real.logb 2 p) by ring]
        have hh := mul_le_mul_of_nonneg_left ha_le_x
          (show 0 ≤ 4 * (s : ℝ) ^ 2 / Real.sqrt (Real.logb 2 s) *
              ((a : ℝ) * Real.logb 2 p) by positivity)
        convert add_le_add hh le_rfl using 1 <;> ring
  have hterm2 : Real.logb 2 p *
      ((traceyInducedGeneratorCeiling a s : ℝ) * (v / p : ℕ)) ≤
      4 * s * v / Real.sqrt (Real.logb 2 s) *
          ((a : ℝ) * Real.logb 2 p) +
        v * ((a : ℝ) * Real.logb 2 p) := by
    calc
      _ ≤ Real.logb 2 p *
          ((traceyInducedGeneratorCeiling a s : ℝ) * v) := by
        apply mul_le_mul_of_nonneg_left _ hlogp0
        exact mul_le_mul_of_nonneg_left hdiv hH0
      _ ≤ Real.logb 2 p *
          ((4 * (a : ℝ) * s / Real.sqrt (Real.logb 2 s) + 1) * v) := by
        apply mul_le_mul_of_nonneg_left _ hlogp0
        exact mul_le_mul_of_nonneg_right hH hv0
      _ ≤ _ := by
        rw [show Real.logb 2 p *
              ((4 * (a : ℝ) * s / Real.sqrt (Real.logb 2 s) + 1) * v) =
            4 * s * v / Real.sqrt (Real.logb 2 s) *
                ((a : ℝ) * Real.logb 2 p) +
              v * Real.logb 2 p by ring]
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hlog_le_x hv0)
  have hterm3 : Real.logb 2 p *
      ((a : ℝ) * s * (g + 1)) ≤
      (s * (g + 1)) * ((a : ℝ) * Real.logb 2 p) := by
    ring_nf
    exact le_rfl
  nlinarith

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]

namespace ActualWreathCompressionTower

/-- Sum of the literal base-two logarithms of the elementary prime-power
coefficients retained by the tower. -/
noncomputable def elementaryCoefficientLogCost :
    {S : ActualWreathCompressionState Q I} →
      ActualWreathCompressionTower S → ℝ
  | _, .terminal _ _ => 0
  | S, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact Real.logb 2 C.p * traceyAffineCoefficientExponent
          (Module.finrank (ZMod C.p) C.V) (Fintype.card I)
          (traceyInducedGeneratorCeiling
            (Module.finrank (ZMod C.p) C.V) (Fintype.card I))
          S.generatorCount S.sourceDegree C.p +
        elementaryCoefficientLogCost next
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact elementaryCoefficientLogCost next

/-- Sum of squares of the elementary logarithmic order shares. -/
noncomputable def elementaryLogSquareBudget :
    {S : ActualWreathCompressionState Q I} →
      ActualWreathCompressionTower S → ℝ
  | _, .terminal _ _ => 0
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact ((Module.finrank (ZMod C.p) C.V : ℝ) * Real.logb 2 C.p) ^ 2 +
        elementaryLogSquareBudget next
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact elementaryLogSquareBudget next

theorem elementaryLogSquareBudget_le_sq :
    {S : ActualWreathCompressionState Q I} →
      (T : ActualWreathCompressionTower S) →
      T.elementaryLogSquareBudget ≤ T.elementaryLogBudget ^ 2
  | _, .terminal _ _ => by
      simp [elementaryLogSquareBudget, elementaryLogBudget]
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log
        coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      have hx0 : 0 ≤ (Module.finrank (ZMod C.p) C.V : ℝ) *
          Real.logb 2 C.p := mul_nonneg (by positivity)
        (Real.logb_nonneg (by norm_num)
          (by exact_mod_cast C.p_prime.one_lt.le))
      have hn0 := elementaryLogBudget_nonneg next
      have ih := elementaryLogSquareBudget_le_sq next
      simp only [elementaryLogSquareBudget, elementaryLogBudget]
      nlinarith [mul_nonneg hx0 hn0]
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      simpa only [elementaryLogSquareBudget, elementaryLogBudget] using
        elementaryLogSquareBudget_le_sq next

/-- Tower-wide elementary coefficient bound before substituting the local
component order. -/
theorem elementaryCoefficientLogCost_le
    {S : ActualWreathCompressionState Q I}
    (T : ActualWreathCompressionTower S) (hs : 2 ≤ Fintype.card I) :
    T.elementaryCoefficientLogCost ≤
      4 * (Fintype.card I : ℝ) ^ 2 /
          Real.sqrt (Real.logb 2 (Fintype.card I)) *
            T.elementaryLogBudget ^ 2 +
        (4 * Fintype.card I * S.sourceDegree /
              Real.sqrt (Real.logb 2 (Fintype.card I)) +
            Fintype.card I * (S.generatorCount + 2) + S.sourceDegree) *
          T.elementaryLogBudget := by
  induction T with
  | terminal S hD =>
      simp [elementaryCoefficientLogCost, elementaryLogBudget]
  | @elementary S D' groupD' finiteD' phi hphi C H hhalf hlog hcoeff next ih =>
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      have hone := traceyAffineCoefficientExponent_log_le
        (Module.finrank (ZMod C.p) C.V) (Fintype.card I)
        S.generatorCount S.sourceDegree C.p C.p_prime hs
      have ih' := ih
      have hsources : (S.quotient D' phi hphi).sourceDegree = S.sourceDegree := rfl
      have hgens : (S.quotient D' phi hphi).generatorCount = S.generatorCount := rfl
      rw [hsources, hgens] at ih'
      have hnext0 := elementaryLogBudget_nonneg next
      have hscale0 : 0 ≤ 4 * (Fintype.card I : ℝ) ^ 2 /
          Real.sqrt (Real.logb 2 (Fintype.card I)) := by
        have : 0 < Real.sqrt (Real.logb 2 (Fintype.card I)) :=
          Real.sqrt_pos.2 (Real.logb_pos (by norm_num)
            (by exact_mod_cast hs))
        positivity
      have hx0 : 0 ≤ (Module.finrank (ZMod C.p) C.V : ℝ) *
          Real.logb 2 C.p := mul_nonneg (by positivity)
        (Real.logb_nonneg (by norm_num)
          (by exact_mod_cast C.p_prime.one_lt.le))
      simp only [elementaryCoefficientLogCost, elementaryLogBudget]
      nlinarith [mul_nonneg hx0 hnext0,
        mul_nonneg hscale0 (mul_nonneg hx0 hnext0)]
  | @semisimple S D' groupD' finiteD' phi hphi C next ih =>
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      simpa only [elementaryCoefficientLogCost, elementaryLogBudget] using ih

end ActualWreathCompressionTower
end SymmetricSubgroupAsymptotics

end
