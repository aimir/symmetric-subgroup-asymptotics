import SymmetricSubgroupAsymptotics.ActualWreathCharacteristicChiefProfile
import SymmetricSubgroupAsymptotics.InducedMinimumSharpRealLogarithmic

/-! The sharper real logarithmic coefficient follows from the simultaneous
primary and coprime fields of EVERY existing elementary charge. In
particular, it applies to the SAME charges already extracted from the
actual chief trace; neither the structure nor its extraction is changed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ElementaryChargeSharpRealLogarithmic
open ActualWreathCharacteristicChiefProfile

theorem logarithmic_real {t : ℕ} (c : ElementaryCharge t) (ht : 2 ≤ t) :
    (c.capacity : ℝ) ≤ Real.sqrt (5/3)*(c.dimension : ℝ)*t/
      Real.sqrt (Real.logb 2 (t : ℝ)) := by
  let A : ℝ := (c.dimension : ℝ)*t
  let u : ℝ := (((c.p-1)*t.factorization c.p : ℕ) : ℝ)
  let L := Real.logb 2 (t : ℝ)
  have ht0 : t ≠ 0 := by omega
  obtain ⟨v,hv,hpowers,hvchoice⟩ :=
    TraceyElementaryLogBudget.exists_largest_other_power c.p t
  have hbudget := TraceyElementaryLogBudget.log_budget c.p t v
    c.prime.one_lt.le ht0 hv hpowers
  have hu : u = ((c.p : ℝ)-1)*(t.factorization c.p : ℝ) := by
    dsimp only [u]
    rw [Nat.cast_mul,Nat.cast_sub c.prime.one_lt.le,Nat.cast_one]
  have hprimary : (c.capacity : ℝ)^2*u ≤ 2*A^2/3 := by
    by_cases hz : t.factorization c.p = 0
    · simp only [u,hz,mul_zero,Nat.cast_zero]
      positivity
    · have he : 1 ≤ t.factorization c.p := by omega
      have hdiv : c.p^t.factorization c.p ∣ t :=
        (c.prime.pow_dvd_iff_le_factorization ht0).mpr le_rfl
      have h := c.primary (t.factorization c.p) he hdiv
      have hup : (0 : ℝ) < u := by
        rw [hu]
        have hpR : (2 : ℝ) ≤ c.p := by exact_mod_cast c.prime.two_le
        have heR : (0 : ℝ) < t.factorization c.p := by exact_mod_cast he
        have hpmR : (0 : ℝ) < (c.p : ℝ)-1 := by linarith only [hpR]
        positivity
      have hden : 3*((c.p : ℝ)-1)*t.factorization c.p = 3*u := by rw [hu]; ring
      rw [hden] at h
      change (c.capacity : ℝ) ≤ A*Real.sqrt (2/(3*u)) at h
      have hsq := (sq_le_sq₀ (show (0 : ℝ) ≤ c.capacity by positivity)
        (mul_nonneg (show 0 ≤ A by dsimp only [A]; positivity)
          (Real.sqrt_nonneg _))).mpr h
      rw [mul_pow,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2/(3*u))] at hsq
      apply (le_div_iff₀ hup).mp
      calc
        (c.capacity : ℝ)^2 ≤ A^2*(2/(3*u)) := hsq
        _ = (2*A^2/3)/u := by ring
  have hother : (c.capacity : ℝ)*(v : ℝ) ≤ A := by
    rcases hvchoice with hv1 | ⟨q,hq,hqp,hvq⟩
    · have ha : 0 ≤ A := by dsimp only [A]; positivity
      have hh : (c.capacity : ℝ) ≤ A := by
        have hc := c.half
        change (c.capacity : ℝ) ≤ A/2 at hc
        linarith only [hc,ha]
      simpa only [hv1,Nat.cast_one,mul_one] using hh
    · have hqprime := Nat.prime_of_mem_primeFactors hq
      have hdiv : q^t.factorization q ∣ t :=
        (hqprime.pow_dvd_iff_le_factorization ht0).mpr le_rfl
      have h := c.primeTo q (t.factorization q) hqprime hqp hdiv
      have hqR : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
      have hqpR : (0 : ℝ) < (q : ℝ)^t.factorization q := pow_pos hqR _
      have hmul := (le_div_iff₀ hqpR).mp h
      simpa only [hvq,Nat.cast_pow] using hmul
  have hLp : 0 < L := Real.logb_pos (by norm_num) (by exact_mod_cast (by omega : 1 < t))
  have h := InducedMinimumSharpRealLogarithmic.sqrt_budget c.capacity A u v L
    (by positivity) (by dsimp only [A]; positivity) (by positivity) hLp
    hbudget hprimary hother
  simpa only [A,L,mul_assoc] using h

end SymmetricSubgroupAsymptotics.ElementaryChargeSharpRealLogarithmic
