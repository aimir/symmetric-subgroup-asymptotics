import SymmetricSubgroupAsymptotics.ActualWreathCompressionWeightedBudget

/-!
# Refined prime-by-prime budgets in an actual wreath tower

The uniform half-capacity estimate is deliberately too coarse for the seven
small affine local degrees.  Every elementary edge of the actual tower also
carries Tracey's retained prime-to, primary and prime-power bounds.  This file
aggregates any chosen one of those bounds without forgetting either the prime
or the dimension of the literal chief factor.

The input `rate p` is a bound for the number of induced generators per local
copy of an elementary `p`-factor.  The first theorem sums those bounds along
the actual chief tower.  The second charges the resulting prime dimensions to
the exact factorization of the original local-component order.  Nonabelian
chief factors cost no linear exponent and are harmless in the comparison.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- A factorization budget in which the exponent of each prime is charged at
an arbitrary nonnegative capacity rate. -/
noncomputable def refinedWeightedFactorBudget
    (rate : ℕ → ℝ) (n : ℕ) : ℝ :=
  n.factorization.sum fun p a =>
    (a : ℝ) * (Real.logb 2 p / p) * rate p

theorem refinedWeightedFactorBudget_nonneg
    (rate : ℕ → ℝ) (hrate : ∀ p, 0 ≤ rate p) (n : ℕ) :
    0 ≤ refinedWeightedFactorBudget rate n := by
  classical
  unfold refinedWeightedFactorBudget
  apply Finsupp.sum_nonneg
  intro p hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors
    (show p ∈ n.primeFactors from hp)
  exact mul_nonneg
    (mul_nonneg (by positivity)
      (div_nonneg
        (Real.logb_nonneg (by norm_num)
          (by exact_mod_cast hpPrime.one_lt.le)) (by positivity)))
    (hrate p)

theorem refinedWeightedFactorBudget_mul
    (rate : ℕ → ℝ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    refinedWeightedFactorBudget rate (m * n) =
      refinedWeightedFactorBudget rate m +
        refinedWeightedFactorBudget rate n := by
  classical
  unfold refinedWeightedFactorBudget
  rw [Nat.factorization_mul hm hn, Finsupp.sum_add_index']
  · intro p
    simp
  · intro p a b
    push_cast
    ring

theorem refinedWeightedFactorBudget_prime_pow
    (rate : ℕ → ℝ) {p a : ℕ} (hp : p.Prime) :
    refinedWeightedFactorBudget rate (p ^ a) =
      (a : ℝ) * (Real.logb 2 p / p) * rate p := by
  classical
  unfold refinedWeightedFactorBudget
  rw [hp.factorization_pow]
  simp

theorem refinedWeightedFactorBudget_mono_of_dvd
    (rate : ℕ → ℝ) (hrate : ∀ p, 0 ≤ rate p)
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hdiv : m ∣ n) :
    refinedWeightedFactorBudget rate m ≤
      refinedWeightedFactorBudget rate n := by
  classical
  have hfac : m.factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd hm hn).2 hdiv
  unfold refinedWeightedFactorBudget
  rw [Finsupp.sum, Finsupp.sum]
  calc
    ∑ p ∈ m.factorization.support,
        (m.factorization p : ℝ) * (Real.logb 2 p / p) * rate p ≤
        ∑ p ∈ m.factorization.support,
          (n.factorization p : ℝ) * (Real.logb 2 p / p) * rate p := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors
        (show p ∈ m.primeFactors from hp)
      have hslope : 0 ≤ Real.logb 2 p / p :=
        div_nonneg
          (Real.logb_nonneg (by norm_num)
            (by exact_mod_cast hpPrime.one_lt.le)) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hfac p) hslope)
        (hrate p)
    _ ≤ ∑ p ∈ n.factorization.support,
          (n.factorization p : ℝ) * (Real.logb 2 p / p) * rate p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finsupp.support_mono hfac)
      intro p hp hmnot
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors
        (show p ∈ n.primeFactors from hp)
      exact mul_nonneg
        (mul_nonneg (by positivity)
          (div_nonneg
            (Real.logb_nonneg (by norm_num)
              (by exact_mod_cast hpPrime.one_lt.le)) (by positivity)))
        (hrate p)

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]

namespace ActualWreathCompressionTower

/-- Per-local-dimension rate obtained from an exact primary exponent of the
block count.  The matching characteristic uses Tracey's square-root bound;
every other characteristic uses the displayed prime-power divisor. -/
noncomputable def traceyPrimaryRate (s q e p : ℕ) : ℝ :=
  if p = q then
    (s : ℝ) * Real.sqrt (2 / (3 * ((q : ℝ) - 1) * e))
  else
    (s : ℝ) / q ^ e

theorem traceyPrimaryRate_nonneg (s q e p : ℕ) :
    0 ≤ traceyPrimaryRate s q e p := by
  unfold traceyPrimaryRate
  split_ifs <;> positivity

/-- At a prime-power block count the matching characteristic may use the
central-binomial soluble-transitive rate, while every other characteristic
uses the whole block count as a prime-to divisor. -/
noncomputable def traceyPrimePowerRate (q e p : ℕ) : ℝ :=
  if p = q then
    let k := e * (q - 1)
    (q ^ e : ℝ) * Nat.choose k (k / 2) / 2 ^ k
  else
    1

theorem traceyPrimePowerRate_nonneg (q e p : ℕ) :
    0 ≤ traceyPrimePowerRate q e p := by
  unfold traceyPrimePowerRate
  split_ifs <;> positivity

/-- The selected refined rate bounds every elementary capacity in the
literal tower, with its actual prime and vector-space dimension retained. -/
def CapacityRateBound (rate : ℕ → ℝ) :
    {S : ActualWreathCompressionState Q I} →
      ActualWreathCompressionTower S → Prop
  | _, .terminal _ _ => True
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log
        capacity_refined coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact H.capacity ≤
          (Module.finrank (ZMod C.p) C.V : ℝ) * rate C.p ∧
        CapacityRateBound rate next
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact CapacityRateBound rate next

/-- Choose Tracey's primary bound in one characteristic and its prime-to
bound in every other characteristic, uniformly along the literal tower. -/
theorem capacityRateBound_traceyPrimary
    (q e : ℕ) (hq : q.Prime) (he : 1 ≤ e)
    (hdiv : q ^ e ∣ Fintype.card I)
    (hmax : ¬ q ^ (e + 1) ∣ Fintype.card I) :
    {S : ActualWreathCompressionState Q I} →
      (T : ActualWreathCompressionTower S) →
      T.CapacityRateBound
        (traceyPrimaryRate (Fintype.card I) q e)
  | _, .terminal _ _ => trivial
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log
        capacity_refined coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      constructor
      · unfold traceyPrimaryRate
        by_cases hpq : C.p = q
        · rw [if_pos hpq]
          subst q
          simpa only [mul_assoc] using
            capacity_refined.primary e he hdiv hmax
        · rw [if_neg hpq]
          simpa only [div_eq_mul_inv, mul_assoc] using
            capacity_refined.primeTo q e hq (Ne.symm hpq) he hdiv
      · exact capacityRateBound_traceyPrimary q e hq he hdiv hmax next
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact capacityRateBound_traceyPrimary q e hq he hdiv hmax next

/-- Choose the soluble-transitive central-binomial rate at an exact
prime-power block count. -/
theorem capacityRateBound_traceyPrimePower
    (q e : ℕ) (hq : q.Prime) (he : 1 ≤ e)
    (hs : Fintype.card I = q ^ e) :
    {S : ActualWreathCompressionState Q I} →
      (T : ActualWreathCompressionTower S) →
      T.CapacityRateBound (traceyPrimePowerRate q e)
  | _, .terminal _ _ => trivial
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log
        capacity_refined coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      constructor
      · unfold traceyPrimePowerRate
        by_cases hpq : C.p = q
        · rw [if_pos hpq]
          subst q
          have h := capacity_refined.primePower C.p e C.p_prime he hs
          dsimp only at h ⊢
          calc
            H.capacity ≤
                (Module.finrank (ZMod C.p) C.V : ℝ) *
                  (Fintype.card I : ℝ) *
                  Nat.choose (e * (C.p - 1)) (e * (C.p - 1) / 2) /
                    2 ^ (e * (C.p - 1)) := h
            _ = (Module.finrank (ZMod C.p) C.V : ℝ) *
                ((C.p ^ e : ℕ) : ℝ) *
                  Nat.choose (e * (C.p - 1)) (e * (C.p - 1) / 2) /
                    2 ^ (e * (C.p - 1)) := by rw [hs]
            _ = (Module.finrank (ZMod C.p) C.V : ℝ) *
                (((C.p : ℝ) ^ e *
                  Nat.choose (e * (C.p - 1)) (e * (C.p - 1) / 2)) /
                    2 ^ (e * (C.p - 1))) := by
              push_cast
              ring
        · rw [if_neg hpq]
          have hqne : q ≠ C.p := Ne.symm hpq
          have hdiv : q ^ e ∣ Fintype.card I := by rw [hs]
          have h := capacity_refined.primeTo q e hq hqne he hdiv
          have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
          calc
            H.capacity ≤
                (Module.finrank (ZMod C.p) C.V : ℝ) *
                  (Fintype.card I : ℝ) / (q : ℝ) ^ e := h
            _ = (Module.finrank (ZMod C.p) C.V : ℝ) * 1 := by
              rw [hs]
              push_cast
              field_simp [hqR]
      · exact capacityRateBound_traceyPrimePower q e hq he hs next
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact capacityRateBound_traceyPrimePower q e hq he hs next

/-- Prime-by-prime refined linear budget displayed by the elementary edges
of the actual tower. -/
noncomputable def refinedWeightedAbelianBudget (rate : ℕ → ℝ) :
    {S : ActualWreathCompressionState Q I} →
      ActualWreathCompressionTower S → ℝ
  | _, .terminal _ _ => 0
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log
        capacity_refined coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact (Module.finrank (ZMod C.p) C.V : ℝ) *
          (Real.logb 2 C.p / C.p) * rate C.p +
        refinedWeightedAbelianBudget rate next
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact refinedWeightedAbelianBudget rate next

/-- Sum a selected retained Tracey bound through every elementary edge. -/
theorem envelope_eta_le_refinedWeightedAbelianBudget
    (rate : ℕ → ℝ) :
    {S : ActualWreathCompressionState Q I} →
      (T : ActualWreathCompressionTower S) →
      T.CapacityRateBound rate →
      T.envelope.eta ≤ T.refinedWeightedAbelianBudget rate
  | _, .terminal _ _, _ => by
      simp [envelope, refinedWeightedAbelianBudget,
        RelativeCompleteSourceEnvelope.identity]
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log
        capacity_refined coefficient_le next, hrate => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      change H.capacity ≤
          (Module.finrank (ZMod C.p) C.V : ℝ) * rate C.p ∧
        next.CapacityRateBound rate at hrate
      have hslope : 0 ≤ Real.logb 2 C.p / C.p :=
        div_nonneg
          (Real.logb_nonneg (by norm_num)
            (by exact_mod_cast C.p_prime.one_lt.le)) (by positivity)
      calc
        (ActualWreathCompressionTower.elementary _ _ phi hphi C H
            capacity_le_half capacity_le_log capacity_refined coefficient_le
              next).envelope.eta =
            Real.logb 2 C.p / C.p * H.capacity + next.envelope.eta := rfl
        _ ≤ (Real.logb 2 C.p / C.p) *
              ((Module.finrank (ZMod C.p) C.V : ℝ) * rate C.p) +
            next.refinedWeightedAbelianBudget rate :=
          add_le_add (mul_le_mul_of_nonneg_left hrate.1 hslope)
            (envelope_eta_le_refinedWeightedAbelianBudget rate next hrate.2)
        _ = (ActualWreathCompressionTower.elementary _ _ phi hphi C H
              capacity_le_half capacity_le_log capacity_refined coefficient_le
                next).refinedWeightedAbelianBudget rate := by
          simp only [refinedWeightedAbelianBudget]
          ring
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next, hrate => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      simpa only [CapacityRateBound, envelope,
        RelativeCompleteSourceEnvelope.semisimpleStep,
        refinedWeightedAbelianBudget] using
        envelope_eta_le_refinedWeightedAbelianBudget rate next hrate

/-- The selected refined tower budget is paid by the exact factorization of
the original local component. -/
theorem refinedWeightedAbelianBudget_le_factorBudget
    (rate : ℕ → ℝ) (hrate : ∀ p, 0 ≤ rate p) :
    {S : ActualWreathCompressionState Q I} →
      (T : ActualWreathCompressionTower S) →
      T.refinedWeightedAbelianBudget rate ≤
        refinedWeightedFactorBudget rate T.localFactorOrderProduct
  | _, .terminal _ _ => by
      simp [refinedWeightedAbelianBudget, localFactorOrderProduct,
        refinedWeightedFactorBudget]
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log
        capacity_refined coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      let a := Module.finrank (ZMod C.p) C.V
      have hpow : C.p ^ a ≠ 0 := pow_ne_zero _ C.p_prime.ne_zero
      have hnext : next.localFactorOrderProduct ≠ 0 := by
        rw [next.localFactorOrderProduct_eq_card]
        exact (Nat.card_pos (α := D')).ne'
      calc
        (ActualWreathCompressionTower.elementary _ _ phi hphi C H
            capacity_le_half capacity_le_log capacity_refined coefficient_le
              next).refinedWeightedAbelianBudget rate =
            (a : ℝ) * (Real.logb 2 C.p / C.p) * rate C.p +
              next.refinedWeightedAbelianBudget rate := rfl
        _ ≤ (a : ℝ) * (Real.logb 2 C.p / C.p) * rate C.p +
              refinedWeightedFactorBudget rate next.localFactorOrderProduct :=
          add_le_add le_rfl
            (refinedWeightedAbelianBudget_le_factorBudget rate hrate next)
        _ = refinedWeightedFactorBudget rate
              (C.p ^ a * next.localFactorOrderProduct) := by
          rw [refinedWeightedFactorBudget_mul rate hpow hnext,
            refinedWeightedFactorBudget_prime_pow rate C.p_prime]
        _ = refinedWeightedFactorBudget rate
            (ActualWreathCompressionTower.elementary _ _ phi hphi C H
              capacity_le_half capacity_le_log capacity_refined coefficient_le
                next).localFactorOrderProduct := rfl
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      let k := ∏ i : C.ι, Nat.card (C.factor i)
      have hk : k ≠ 0 := (Finset.prod_pos fun _ _ => Nat.card_pos).ne'
      have hnext : next.localFactorOrderProduct ≠ 0 := by
        rw [next.localFactorOrderProduct_eq_card]
        exact (Nat.card_pos (α := D')).ne'
      calc
        (ActualWreathCompressionTower.semisimple _ _ phi hphi C
            next).refinedWeightedAbelianBudget rate =
            next.refinedWeightedAbelianBudget rate := rfl
        _ ≤ refinedWeightedFactorBudget rate next.localFactorOrderProduct :=
          refinedWeightedAbelianBudget_le_factorBudget rate hrate next
        _ ≤ refinedWeightedFactorBudget rate
              (k * next.localFactorOrderProduct) :=
          refinedWeightedFactorBudget_mono_of_dvd rate hrate hnext
            (mul_ne_zero hk hnext) (dvd_mul_left _ _)
        _ = refinedWeightedFactorBudget rate
            (ActualWreathCompressionTower.semisimple _ _ phi hphi C
              next).localFactorOrderProduct := rfl

/-- Publication-facing exact-order form of the selected refined budget. -/
theorem envelope_eta_le_refinedFactorBudget_card
    {S : ActualWreathCompressionState Q I}
    (T : ActualWreathCompressionTower S)
    (rate : ℕ → ℝ) (hrate : ∀ p, 0 ≤ rate p)
    (hcapacity : T.CapacityRateBound rate) :
    T.envelope.eta ≤
      refinedWeightedFactorBudget rate (Nat.card S.D) := by
  refine (T.envelope_eta_le_refinedWeightedAbelianBudget rate hcapacity).trans ?_
  rw [← T.localFactorOrderProduct_eq_card]
  exact T.refinedWeightedAbelianBudget_le_factorBudget rate hrate

end ActualWreathCompressionTower
end SymmetricSubgroupAsymptotics

end
