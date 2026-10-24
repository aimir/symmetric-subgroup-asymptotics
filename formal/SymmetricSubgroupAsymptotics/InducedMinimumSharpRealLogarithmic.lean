import SymmetricSubgroupAsymptotics.InducedMinimumRealLogarithmic

/-! The existing primary and coprime estimates already yield the square
constant 5/3, before the older proof weakens it to 4. This leaf retains
that stronger consequence for the SAME least actual induced capacity.
No permutation-generator hypothesis or new module bound is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.InducedMinimumSharpRealLogarithmic

theorem square_budget (H A u v L : ℝ)
    (hH : 0 ≤ H) (hA : 0 ≤ A) (hv : 0 ≤ v)
    (hbudget : L ≤ u+v^2) (hprimary : H^2*u ≤ 2*A^2/3)
    (hother : H*v ≤ A) : H^2*L ≤ (5/3)*A^2 := by
  have hs := (sq_le_sq₀ (mul_nonneg hH hv) hA).mpr hother
  have hb := mul_le_mul_of_nonneg_left hbudget (sq_nonneg H)
  nlinarith only [hs,hb,hprimary]

theorem sqrt_budget (H A u v L : ℝ)
    (hH : 0 ≤ H) (hA : 0 ≤ A) (hv : 0 ≤ v) (hL : 0 < L)
    (hbudget : L ≤ u+v^2) (hprimary : H^2*u ≤ 2*A^2/3)
    (hother : H*v ≤ A) : H ≤ Real.sqrt (5/3)*A/Real.sqrt L := by
  have hsq := square_budget H A u v L hH hA hv hbudget hprimary hother
  have hleft : (H*Real.sqrt L)^2 ≤ (Real.sqrt (5/3)*A)^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt hL.le,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5/3)]
    exact hsq
  have hh := (sq_le_sq₀ (mul_nonneg hH (Real.sqrt_nonneg L))
    (mul_nonneg (Real.sqrt_nonneg _) hA)).mp hleft
  exact (le_div_iff₀ (Real.sqrt_pos.mpr hL)).mpr hh

open InducedMinimumUniformCapacity
variable {p : ℕ} [Fact p.Prime] {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (H : Subgroup G) (rho : Representation (ZMod p) H V)

theorem logarithmic_real (hs : 2 ≤ H.index) :
    (capacity H rho : ℝ) ≤
      Real.sqrt (5/3) * (Module.finrank (ZMod p) V : ℝ) * H.index /
        Real.sqrt (Real.logb 2 (H.index : ℝ)) := by
  let s := H.index
  let a := Module.finrank (ZMod p) V
  let A : ℝ := (a : ℝ)*s
  let u : ℝ := (((p-1)*s.factorization p : ℕ) : ℝ)
  let L : ℝ := Real.logb 2 (s : ℝ)
  have hs0 : s≠0 := H.index_ne_zero_of_finite
  obtain ⟨v,hv,hpowers,hvchoice⟩ := TraceyElementaryLogBudget.exists_largest_other_power p s
  have hbudget := TraceyElementaryLogBudget.log_budget p s v
    (by have := (Fact.out : p.Prime).two_le; omega) hs0 hv hpowers
  have hu : u=((p : ℝ)-1)*(s.factorization p : ℝ) := by
    dsimp [u]
    rw [Nat.cast_mul,Nat.cast_sub (by have := (Fact.out : p.Prime).two_le; omega),Nat.cast_one]
  have hprimary : (capacity H rho : ℝ)^2*u≤2*A^2/3 := by
    by_cases hz : s.factorization p=0
    · simp only [u,hz,mul_zero,Nat.cast_zero]
      positivity
    · have he : 1 ≤ s.factorization p := by omega
      have hdiv : p^s.factorization p∣H.index :=
        ((Fact.out : p.Prime).pow_dvd_iff_le_factorization hs0).mpr le_rfl
      have h := primary H rho (s.factorization p) he hdiv
      have hup : (0 : ℝ)<u := by
        rw [hu]
        have hpR : (2 : ℝ)≤p := by exact_mod_cast (Fact.out : p.Prime).two_le
        have heR : (0 : ℝ)< s.factorization p := by exact_mod_cast he
        have hpmR : (0 : ℝ)<(p : ℝ)-1 := by linarith
        positivity
      have hden : 3*((p : ℝ)-1)*s.factorization p=3*u := by rw [hu]; ring
      rw [hden] at h
      change (capacity H rho : ℝ)≤A*Real.sqrt (2/(3*u)) at h
      have hsq := (sq_le_sq₀ (show (0 : ℝ)≤capacity H rho by positivity)
        (mul_nonneg (show 0≤A by dsimp [A]; positivity) (Real.sqrt_nonneg _))).mpr h
      rw [mul_pow,Real.sq_sqrt (by positivity : (0 : ℝ)≤2/(3*u))] at hsq
      apply (le_div_iff₀ hup).mp
      calc
        (capacity H rho : ℝ)^2≤A^2*(2/(3*u)) := hsq
        _ = (2*A^2/3)/u := by ring
  have hother : (capacity H rho : ℝ)*(v : ℝ)≤A := by
    rcases hvchoice with hv1 | ⟨q,hq,hqp,hvq⟩
    · simpa only [hv1,Nat.cast_one,mul_one] using coarse H rho
    · have hqprime := Nat.prime_of_mem_primeFactors hq
      have hdiv : q^s.factorization q∣H.index :=
        (hqprime.pow_dvd_iff_le_factorization hs0).mpr le_rfl
      have h := primeTo H rho q (s.factorization q) hqprime hqp hdiv
      have hqR : (0 : ℝ)<q := by exact_mod_cast hqprime.pos
      have hqpR : (0 : ℝ)<(q : ℝ)^s.factorization q := pow_pos hqR _
      have hmul := (le_div_iff₀ hqpR).mp h
      simpa only [hvq,Nat.cast_pow] using hmul
  have hLp : 0<L := Real.logb_pos (by norm_num) (by exact_mod_cast (by omega : 1<s))
  have h := sqrt_budget (capacity H rho) A u v L
    (by positivity) (by dsimp [A]; positivity) (by positivity) hLp
    hbudget hprimary hother
  simpa only [A,a,s,L,mul_assoc] using h

end SymmetricSubgroupAsymptotics.InducedMinimumSharpRealLogarithmic
