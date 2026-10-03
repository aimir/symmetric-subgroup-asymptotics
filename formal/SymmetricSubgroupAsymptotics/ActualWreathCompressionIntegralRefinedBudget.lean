import SymmetricSubgroupAsymptotics.ActualWreathCompressionTrace
import SymmetricSubgroupAsymptotics.ActualWreathCompressionRefinedBudget
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Integral prime-by-prime budgets in an actual wreath tower

Every elementary capacity stored in an actual compression trace is a natural
number.  The real-valued refined budget therefore loses a useful floor at
small block counts.  This file retains that floor after all chief factors of
the same characteristic have been combined.  The resulting budget is

`sum_p (log₂ p / p) * floor(v_p(n) * rate p)`.

The floor is taken after multiplying by the full prime multiplicity.  This is
exactly the convention used in the finite affine-capacity table.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- The integral refinement of `refinedWeightedFactorBudget`. -/
noncomputable def integralRefinedWeightedFactorBudget
    (rate : ℕ → ℝ) (n : ℕ) : ℝ :=
  n.factorization.sum fun p a =>
    (Real.logb 2 p / p) * (Nat.floor ((a : ℝ) * rate p) : ℝ)

theorem integralRefinedWeightedFactorBudget_prime_pow
    (rate : ℕ → ℝ) {p a : ℕ} (hp : p.Prime) :
    integralRefinedWeightedFactorBudget rate (p ^ a) =
      (Real.logb 2 p / p) *
        (Nat.floor ((a : ℝ) * rate p) : ℝ) := by
  unfold integralRefinedWeightedFactorBudget
  rw [hp.factorization_pow]
  simp

/-- For coprime factors no characteristic occurs on both sides, so retaining
the integral floor still gives an exact additive factor budget. -/
theorem integralRefinedWeightedFactorBudget_mul_of_coprime
    (rate : ℕ → ℝ) {m n : ℕ} (hcoprime : m.Coprime n) :
    integralRefinedWeightedFactorBudget rate (m * n) =
      integralRefinedWeightedFactorBudget rate m +
        integralRefinedWeightedFactorBudget rate n := by
  unfold integralRefinedWeightedFactorBudget
  rw [Nat.factorization_mul_of_coprime hcoprime,
    Finsupp.sum_add_index_of_disjoint hcoprime.disjoint_primeFactors]

private theorem floor_add_le_floor_add
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Nat.floor x + Nat.floor y ≤ Nat.floor (x + y) := by
  apply Nat.le_floor
  push_cast
  exact add_le_add (Nat.floor_le hx) (Nat.floor_le hy)

private theorem integralRefinedWeightedFactorBudget_mul_superadd
    (rate : ℕ → ℝ) (hrate : ∀ p, 0 ≤ rate p)
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    integralRefinedWeightedFactorBudget rate m +
        integralRefinedWeightedFactorBudget rate n ≤
      integralRefinedWeightedFactorBudget rate (m * n) := by
  let f := m.factorization
  let g := n.factorization
  let term : ℕ → ℕ → ℝ := fun p a =>
    (Real.logb 2 p / p) * (Nat.floor ((a : ℝ) * rate p) : ℝ)
  have hzero : ∀ p, term p 0 = 0 := by
    intro p
    simp [term]
  have hsupport : (f + g).support ⊆ f.support ∪ g.support :=
    Finsupp.support_add
  unfold integralRefinedWeightedFactorBudget
  rw [Nat.factorization_mul hm hn]
  change f.sum term + g.sum term ≤ (f + g).sum term
  rw [Finsupp.sum_of_support_subset f Finset.subset_union_left term
      (fun p _ => hzero p),
    Finsupp.sum_of_support_subset g Finset.subset_union_right term
      (fun p _ => hzero p),
    Finsupp.sum_of_support_subset (f + g) hsupport term
      (fun p _ => hzero p),
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hpPrime : p.Prime := by
    rcases Finset.mem_union.mp hp with hpf | hpg
    · exact Nat.prime_of_mem_primeFactors
        (show p ∈ m.primeFactors from hpf)
    · exact Nat.prime_of_mem_primeFactors
        (show p ∈ n.primeFactors from hpg)
  have hslope : 0 ≤ Real.logb 2 p / p :=
    div_nonneg
      (Real.logb_nonneg (by norm_num)
        (by exact_mod_cast hpPrime.one_lt.le)) (by positivity)
  have hf : 0 ≤ (f p : ℝ) * rate p :=
    mul_nonneg (by positivity) (hrate p)
  have hg : 0 ≤ (g p : ℝ) * rate p :=
    mul_nonneg (by positivity) (hrate p)
  have hfloor := floor_add_le_floor_add hf hg
  dsimp only [term]
  rw [Finsupp.add_apply]
  push_cast at hfloor ⊢
  have harg : ((f p : ℝ) + (g p : ℝ)) * rate p =
      (f p : ℝ) * rate p + (g p : ℝ) * rate p := by ring
  rw [harg, ← mul_add]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hfloor) hslope

private theorem integralRefinedWeightedFactorBudget_mono_of_dvd
    (rate : ℕ → ℝ) (hrate : ∀ p, 0 ≤ rate p)
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hdiv : m ∣ n) :
    integralRefinedWeightedFactorBudget rate m ≤
      integralRefinedWeightedFactorBudget rate n := by
  obtain ⟨k, rfl⟩ := hdiv
  have hk : k ≠ 0 := by
    intro hk
    subst k
    simp at hn
  have hnonneg : 0 ≤ integralRefinedWeightedFactorBudget rate k := by
    unfold integralRefinedWeightedFactorBudget
    apply Finsupp.sum_nonneg
    intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors
      (show p ∈ k.primeFactors from hp)
    exact mul_nonneg
      (div_nonneg
        (Real.logb_nonneg (by norm_num)
          (by exact_mod_cast hpPrime.one_lt.le)) (by positivity))
      (by positivity)
  exact (le_add_of_nonneg_right hnonneg).trans
    (integralRefinedWeightedFactorBudget_mul_superadd rate hrate hm hk)

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]

namespace ActualWreathCompressionTower

/-- Integrality upgrades a capacity-rate bound to the factor budget with
the floor retained after summing equal-characteristic dimensions. -/
theorem envelope_eta_le_integralRefinedFactorBudget
    {S : ActualWreathCompressionState Q I}
    (T : ActualWreathCompressionTower S)
    (hintegral : T.IntegralCapacities)
    (rate : ℕ → ℝ) (hrate : ∀ p, 0 ≤ rate p)
    (hcapacity : T.CapacityRateBound rate) :
    T.envelope.eta ≤
      integralRefinedWeightedFactorBudget rate T.localFactorOrderProduct := by
  induction T with
  | terminal S hD =>
      simp [envelope, RelativeCompleteSourceEnvelope.identity,
        localFactorOrderProduct, integralRefinedWeightedFactorBudget]
  | @elementary S D' groupD' finiteD' phi hphi C H capacity_le_half
      capacity_le_log capacity_refined coefficient_le next ih =>
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      change (∃ h : ℕ, H.capacity = h) ∧ next.IntegralCapacities at hintegral
      obtain ⟨⟨h, hh⟩, hnextIntegral⟩ := hintegral
      change H.capacity ≤
          (Module.finrank (ZMod C.p) C.V : ℝ) * rate C.p ∧
        next.CapacityRateBound rate at hcapacity
      let a := Module.finrank (ZMod C.p) C.V
      have hfloor : h ≤ Nat.floor ((a : ℝ) * rate C.p) := by
        apply Nat.le_floor
        simpa only [hh, a] using hcapacity.1
      have hslope : 0 ≤ Real.logb 2 C.p / C.p :=
        div_nonneg
          (Real.logb_nonneg (by norm_num)
            (by exact_mod_cast C.p_prime.one_lt.le)) (by positivity)
      have hfirst : Real.logb 2 C.p / C.p * H.capacity ≤
          Real.logb 2 C.p / C.p *
            (Nat.floor ((a : ℝ) * rate C.p) : ℝ) := by
        rw [hh]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hfloor) hslope
      have hnext := ih hnextIntegral hcapacity.2
      have hpow : C.p ^ a ≠ 0 := pow_ne_zero _ C.p_prime.ne_zero
      have hnextOrder : next.localFactorOrderProduct ≠ 0 := by
        rw [next.localFactorOrderProduct_eq_card]
        exact (Nat.card_pos (α := D')).ne'
      have hprimePower : integralRefinedWeightedFactorBudget rate (C.p ^ a) =
          Real.logb 2 C.p / C.p *
            (Nat.floor ((a : ℝ) * rate C.p) : ℝ) := by
        unfold integralRefinedWeightedFactorBudget
        rw [C.p_prime.factorization_pow]
        simp
      calc
        (ActualWreathCompressionTower.elementary S D' phi hphi C H
            capacity_le_half capacity_le_log capacity_refined coefficient_le
              next).envelope.eta =
            Real.logb 2 C.p / C.p * H.capacity + next.envelope.eta := rfl
        _ ≤ Real.logb 2 C.p / C.p *
              (Nat.floor ((a : ℝ) * rate C.p) : ℝ) +
            integralRefinedWeightedFactorBudget rate
              next.localFactorOrderProduct := add_le_add hfirst hnext
        _ = integralRefinedWeightedFactorBudget rate (C.p ^ a) +
              integralRefinedWeightedFactorBudget rate
                next.localFactorOrderProduct := by rw [hprimePower]
        _ ≤ integralRefinedWeightedFactorBudget rate
              (C.p ^ a * next.localFactorOrderProduct) :=
          integralRefinedWeightedFactorBudget_mul_superadd rate hrate
            hpow hnextOrder
        _ = integralRefinedWeightedFactorBudget rate
            (ActualWreathCompressionTower.elementary S D' phi hphi C H
              capacity_le_half capacity_le_log capacity_refined coefficient_le
                next).localFactorOrderProduct := rfl
  | @semisimple S D' groupD' finiteD' phi hphi C next ih =>
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      change next.IntegralCapacities at hintegral
      change next.CapacityRateBound rate at hcapacity
      let k := ∏ i : C.ι, Nat.card (C.factor i)
      have hk : k ≠ 0 := (Finset.prod_pos fun _ _ => Nat.card_pos).ne'
      have hnextOrder : next.localFactorOrderProduct ≠ 0 := by
        rw [next.localFactorOrderProduct_eq_card]
        exact (Nat.card_pos (α := D')).ne'
      have hdiv : next.localFactorOrderProduct ∣
          k * next.localFactorOrderProduct := dvd_mul_left _ _
      calc
        (ActualWreathCompressionTower.semisimple S D' phi hphi C
            next).envelope.eta = next.envelope.eta := rfl
        _ ≤ integralRefinedWeightedFactorBudget rate
              next.localFactorOrderProduct := ih hintegral hcapacity
        _ ≤ integralRefinedWeightedFactorBudget rate
              (k * next.localFactorOrderProduct) :=
          integralRefinedWeightedFactorBudget_mono_of_dvd rate hrate
            hnextOrder (mul_ne_zero hk hnextOrder) hdiv
        _ = integralRefinedWeightedFactorBudget rate
            (ActualWreathCompressionTower.semisimple S D' phi hphi C
              next).localFactorOrderProduct := rfl

/-- Exact-order form used by component sources. -/
theorem envelope_eta_le_integralRefinedFactorBudget_card
    {S : ActualWreathCompressionState Q I}
    (T : ActualWreathCompressionTower S)
    (hintegral : T.IntegralCapacities)
    (rate : ℕ → ℝ) (hrate : ∀ p, 0 ≤ rate p)
    (hcapacity : T.CapacityRateBound rate) :
    T.envelope.eta ≤
      integralRefinedWeightedFactorBudget rate (Nat.card S.D) := by
  simpa only [T.localFactorOrderProduct_eq_card] using
    T.envelope_eta_le_integralRefinedFactorBudget hintegral rate hrate hcapacity

/-- Divisor form used by the finite catalogue rows. -/
theorem envelope_eta_le_integralRefinedFactorBudget_of_dvd
    {S : ActualWreathCompressionState Q I}
    (T : ActualWreathCompressionTower S)
    (hintegral : T.IntegralCapacities)
    (rate : ℕ → ℝ) (hrate : ∀ p, 0 ≤ rate p)
    (hcapacity : T.CapacityRateBound rate)
    (n : ℕ) (hn : n ≠ 0) (hdiv : Nat.card S.D ∣ n) :
    T.envelope.eta ≤ integralRefinedWeightedFactorBudget rate n := by
  exact (T.envelope_eta_le_integralRefinedFactorBudget_card
      hintegral rate hrate hcapacity).trans
    (integralRefinedWeightedFactorBudget_mono_of_dvd rate hrate
      (Nat.card_pos (α := S.D)).ne' hn hdiv)

end ActualWreathCompressionTower
end SymmetricSubgroupAsymptotics

end
