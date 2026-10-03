import SymmetricSubgroupAsymptotics.ActualWreathCompressionTrace
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Squarefree

/-!
# Prime-weighted abelian budgets in the actual wreath tower

The worst-prime composition bound is deliberately coarse.  At a small
affine component it can erase the margin even though the literal prime
factors leave room.  This file retains the exact half-capacity charge
`a * log₂(p) / p` of every elementary chief factor and bounds its sum by
the prime factorization of the literal component order.  Nonabelian chief
factors contribute no linear exponent and therefore only enlarge the order
budget on the right.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The half-capacity weight available from the prime factorization of a
positive integer. -/
noncomputable def weightedAbelianFactorBudget (n : ℕ) : ℝ :=
  n.factorization.sum fun p a =>
    (a : ℝ) * (Real.logb 2 p / p)

theorem weightedAbelianFactorBudget_nonneg (n : ℕ) :
    0 ≤ weightedAbelianFactorBudget n := by
  classical
  unfold weightedAbelianFactorBudget
  apply Finsupp.sum_nonneg
  intro p ha
  have hp : p.Prime := Nat.prime_of_mem_primeFactors
    (show p ∈ n.primeFactors from ha)
  exact mul_nonneg (by positivity)
    (div_nonneg
      (Real.logb_nonneg (by norm_num) (by exact_mod_cast hp.one_lt.le))
      (by positivity))

theorem weightedAbelianFactorBudget_mono_of_dvd
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hdiv : m ∣ n) :
    weightedAbelianFactorBudget m ≤ weightedAbelianFactorBudget n := by
  classical
  have hfac : m.factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd hm hn).2 hdiv
  unfold weightedAbelianFactorBudget
  rw [Finsupp.sum, Finsupp.sum]
  calc
    ∑ p ∈ m.factorization.support,
        (m.factorization p : ℝ) * (Real.logb 2 p / p) ≤
        ∑ p ∈ m.factorization.support,
          (n.factorization p : ℝ) * (Real.logb 2 p / p) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfac p)
        (div_nonneg
          (Real.logb_nonneg (by norm_num) (by
            have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors
              (show p ∈ m.primeFactors from hp)
            exact_mod_cast hpPrime.one_lt.le)) (by positivity))
    _ ≤ ∑ p ∈ n.factorization.support,
          (n.factorization p : ℝ) * (Real.logb 2 p / p) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finsupp.support_mono hfac)
      intro p hp hmnot
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors
        (show p ∈ n.primeFactors from hp)
      exact mul_nonneg (by positivity)
        (div_nonneg
          (Real.logb_nonneg (by norm_num)
            (by exact_mod_cast hpPrime.one_lt.le)) (by positivity))

theorem weightedAbelianFactorBudget_mul
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    weightedAbelianFactorBudget (m * n) =
      weightedAbelianFactorBudget m + weightedAbelianFactorBudget n := by
  classical
  unfold weightedAbelianFactorBudget
  rw [Nat.factorization_mul hm hn, Finsupp.sum_add_index']
  · intro p
    simp
  · intro p a b
    push_cast
    ring

theorem weightedAbelianFactorBudget_prime_pow
    {p a : ℕ} (hp : p.Prime) :
    weightedAbelianFactorBudget (p ^ a) =
      (a : ℝ) * (Real.logb 2 p / p) := by
  classical
  unfold weightedAbelianFactorBudget
  rw [hp.factorization_pow]
  simp

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]

namespace ActualWreathCompressionTower

/-- Exact prime-weighted sum of the elementary chief factors displayed in
an actual compression tower. -/
noncomputable def weightedAbelianBudget :
    {S : ActualWreathCompressionState Q I} →
      ActualWreathCompressionTower S → ℝ
  | _, .terminal _ _ => 0
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log
        capacity_refined coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact (Module.finrank (ZMod C.p) C.V : ℝ) *
          (Real.logb 2 C.p / C.p) + weightedAbelianBudget next
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact weightedAbelianBudget next

theorem envelope_eta_le_weightedAbelianBudget :
    {S : ActualWreathCompressionState Q I} →
      (T : ActualWreathCompressionTower S) →
        T.envelope.eta ≤
          ((Fintype.card I : ℝ) / 2) * T.weightedAbelianBudget
  | _, .terminal _ _ => by
      simp [weightedAbelianBudget, envelope,
        RelativeCompleteSourceEnvelope.identity]
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log
        capacity_refined coefficient_le next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      have hslope : 0 ≤ Real.logb 2 C.p / C.p :=
        div_nonneg
          (Real.logb_nonneg (by norm_num)
            (by exact_mod_cast C.p_prime.one_lt.le)) (by positivity)
      have hfirst : Real.logb 2 C.p / C.p * H.capacity ≤
          ((Fintype.card I : ℝ) / 2) *
            ((Module.finrank (ZMod C.p) C.V : ℝ) *
              (Real.logb 2 C.p / C.p)) := by
        calc
          Real.logb 2 C.p / C.p * H.capacity ≤
              (Real.logb 2 C.p / C.p) *
                ((Module.finrank (ZMod C.p) C.V : ℝ) *
                  Fintype.card I / 2) :=
            mul_le_mul_of_nonneg_left capacity_le_half hslope
          _ = ((Fintype.card I : ℝ) / 2) *
                ((Module.finrank (ZMod C.p) C.V : ℝ) *
                  (Real.logb 2 C.p / C.p)) := by ring
      have hnext := envelope_eta_le_weightedAbelianBudget next
      calc
        (ActualWreathCompressionTower.elementary _ _ phi hphi C H
            capacity_le_half capacity_le_log capacity_refined coefficient_le
              next).envelope.eta =
            Real.logb 2 C.p / C.p * H.capacity + next.envelope.eta := rfl
        _ ≤ ((Fintype.card I : ℝ) / 2) *
              ((Module.finrank (ZMod C.p) C.V : ℝ) *
                (Real.logb 2 C.p / C.p)) +
            ((Fintype.card I : ℝ) / 2) * next.weightedAbelianBudget :=
          add_le_add hfirst hnext
        _ = ((Fintype.card I : ℝ) / 2) *
            (ActualWreathCompressionTower.elementary _ _ phi hphi C H
              capacity_le_half capacity_le_log capacity_refined coefficient_le
                next).weightedAbelianBudget := by
          simp only [weightedAbelianBudget]
          ring
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      simpa only [weightedAbelianBudget, envelope,
        RelativeCompleteSourceEnvelope.semisimpleStep] using
        envelope_eta_le_weightedAbelianBudget next

/-- If the literal local-factor product divides a squarefree integer, every
elementary chief factor in the tower has rank at most one.  Consequently the
integral half-capacity in the tower constructor retains the floor in
`card I / 2`; this is stronger than passing immediately to the real bound
`card I / 2`. -/
theorem envelope_eta_le_natHalf_weightedAbelianBudget_of_squarefree
    {S : ActualWreathCompressionState Q I}
    (T : ActualWreathCompressionTower S)
    (hintegral : T.IntegralCapacities)
    (n : ℕ) (hn : n ≠ 0) (hsq : Squarefree n)
    (hdiv : T.localFactorOrderProduct ∣ n) :
    T.envelope.eta ≤
      ((Fintype.card I / 2 : ℕ) : ℝ) * T.weightedAbelianBudget := by
  induction T with
  | terminal S hD =>
      simp [weightedAbelianBudget, envelope,
        RelativeCompleteSourceEnvelope.identity]
  | @elementary S D' groupD' finiteD' phi hphi C H capacity_le_half
      capacity_le_log capacity_refined coefficient_le next ih =>
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      change (∃ h : ℕ, H.capacity = h) ∧ next.IntegralCapacities at hintegral
      obtain ⟨⟨h, hh⟩, hnextIntegral⟩ := hintegral
      let a := Module.finrank (ZMod C.p) C.V
      have hpow : C.p ^ a ∣
          (ActualWreathCompressionTower.elementary S D' phi hphi C H
            capacity_le_half capacity_le_log capacity_refined coefficient_le
              next).localFactorOrderProduct := by
        simp only [localFactorOrderProduct]
        exact dvd_mul_right _ _
      have hpow_n : C.p ^ a ∣ n := hpow.trans hdiv
      have ha : a ≤ 1 := by
        exact ((C.p_prime.pow_dvd_iff_le_factorization hn).mp hpow_n).trans
          (hsq.natFactorization_le_one C.p)
      have hcap : (h : ℝ) ≤ (a : ℝ) * Fintype.card I / 2 := by
        rw [hh] at capacity_le_half
        simpa only [a] using capacity_le_half
      have hcap' : h ≤ (Fintype.card I / 2) * a := by
        have haCases : a = 0 ∨ a = 1 := by omega
        rcases haCases with ha0 | ha1
        · have hc0R : (h : ℝ) = 0 := by
            apply le_antisymm
            · simpa only [ha0, Nat.cast_zero, zero_mul, zero_div] using hcap
            · positivity
          have hc0 : h = 0 := by exact_mod_cast hc0R
          simp [ha0, hc0]
        · have hcap1 : (h : ℝ) ≤
              (Fintype.card I : ℝ) / 2 := by
            simpa only [ha1, Nat.cast_one, one_mul] using hcap
          have htwiceR : ((2 * h : ℕ) : ℝ) ≤
              (Fintype.card I : ℝ) := by
            push_cast
            nlinarith
          have htwice : 2 * h ≤ Fintype.card I := by
            exact_mod_cast htwiceR
          have hfloor : h ≤ Fintype.card I / 2 :=
            (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 (by
              simpa only [Nat.mul_comm] using htwice)
          simpa only [ha1, Nat.mul_one] using hfloor
      have hslope : 0 ≤ Real.logb 2 C.p / C.p :=
        div_nonneg
          (Real.logb_nonneg (by norm_num)
            (by exact_mod_cast C.p_prime.one_lt.le)) (by positivity)
      have hfirst : Real.logb 2 C.p / C.p * H.capacity ≤
          ((Fintype.card I / 2 : ℕ) : ℝ) *
            ((a : ℝ) * (Real.logb 2 C.p / C.p)) := by
        calc
          Real.logb 2 C.p / C.p * H.capacity ≤
              (Real.logb 2 C.p / C.p) *
                (((Fintype.card I / 2) * a : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left (by
              rw [hh]
              exact_mod_cast hcap') hslope
          _ = ((Fintype.card I / 2 : ℕ) : ℝ) *
                ((a : ℝ) * (Real.logb 2 C.p / C.p)) := by
            push_cast
            ring
      have hnextdiv : next.localFactorOrderProduct ∣ n := by
        apply (dvd_mul_left next.localFactorOrderProduct (C.p ^ a)).trans
        simpa only [localFactorOrderProduct, a] using hdiv
      have hnext := ih hnextIntegral hnextdiv
      calc
        (ActualWreathCompressionTower.elementary S D' phi hphi C H
            capacity_le_half capacity_le_log capacity_refined coefficient_le
              next).envelope.eta =
            Real.logb 2 C.p / C.p * H.capacity + next.envelope.eta := rfl
        _ ≤ ((Fintype.card I / 2 : ℕ) : ℝ) *
              ((a : ℝ) * (Real.logb 2 C.p / C.p)) +
            ((Fintype.card I / 2 : ℕ) : ℝ) *
              next.weightedAbelianBudget := add_le_add hfirst hnext
        _ = ((Fintype.card I / 2 : ℕ) : ℝ) *
            (ActualWreathCompressionTower.elementary S D' phi hphi C H
              capacity_le_half capacity_le_log capacity_refined coefficient_le
                next).weightedAbelianBudget := by
          simp only [weightedAbelianBudget, a]
          ring
  | @semisimple S D' groupD' finiteD' phi hphi C next ih =>
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      change next.IntegralCapacities at hintegral
      let k := ∏ i : C.ι, Nat.card (C.factor i)
      have hnextdiv : next.localFactorOrderProduct ∣ n := by
        apply (dvd_mul_left next.localFactorOrderProduct k).trans
        simpa only [localFactorOrderProduct, k] using hdiv
      simpa only [weightedAbelianBudget, envelope,
        RelativeCompleteSourceEnvelope.semisimpleStep] using
        ih hintegral hnextdiv

/-- The prime-weighted elementary budget is bounded by the factorization of
the exact literal local-component order. -/
theorem weightedAbelianBudget_le_factorBudget :
    {S : ActualWreathCompressionState Q I} →
      (T : ActualWreathCompressionTower S) →
        T.weightedAbelianBudget ≤
          weightedAbelianFactorBudget T.localFactorOrderProduct
  | _, .terminal _ _ => by
      simp [weightedAbelianBudget, localFactorOrderProduct,
        weightedAbelianFactorBudget]
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
              next).weightedAbelianBudget =
            (a : ℝ) * (Real.logb 2 C.p / C.p) +
              next.weightedAbelianBudget := rfl
        _ ≤ (a : ℝ) * (Real.logb 2 C.p / C.p) +
              weightedAbelianFactorBudget next.localFactorOrderProduct :=
          add_le_add le_rfl (weightedAbelianBudget_le_factorBudget next)
        _ = weightedAbelianFactorBudget
              (C.p ^ a * next.localFactorOrderProduct) := by
          rw [weightedAbelianFactorBudget_mul hpow hnext,
            weightedAbelianFactorBudget_prime_pow C.p_prime]
        _ = weightedAbelianFactorBudget
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
      have hmono : weightedAbelianFactorBudget next.localFactorOrderProduct ≤
          weightedAbelianFactorBudget
            (k * next.localFactorOrderProduct) :=
        weightedAbelianFactorBudget_mono_of_dvd hnext (mul_ne_zero hk hnext)
          (dvd_mul_left _ _)
      calc
        (ActualWreathCompressionTower.semisimple _ _ phi hphi C
            next).weightedAbelianBudget = next.weightedAbelianBudget := rfl
        _ ≤ weightedAbelianFactorBudget next.localFactorOrderProduct :=
          weightedAbelianBudget_le_factorBudget next
        _ ≤ weightedAbelianFactorBudget
            (k * next.localFactorOrderProduct) := hmono
        _ = weightedAbelianFactorBudget
            (ActualWreathCompressionTower.semisimple _ _ phi hphi C
              next).localFactorOrderProduct := rfl

/-- Publication-facing exact-order form of the weighted estimate. -/
theorem envelope_eta_le_weightedFactorBudget_card
    {S : ActualWreathCompressionState Q I}
    (T : ActualWreathCompressionTower S) :
    T.envelope.eta ≤ ((Fintype.card I : ℝ) / 2) *
      weightedAbelianFactorBudget (Nat.card S.D) := by
  refine (T.envelope_eta_le_weightedAbelianBudget).trans ?_
  rw [← T.localFactorOrderProduct_eq_card]
  exact mul_le_mul_of_nonneg_left T.weightedAbelianBudget_le_factorBudget
    (by positivity)

end ActualWreathCompressionTower
end SymmetricSubgroupAsymptotics

end
