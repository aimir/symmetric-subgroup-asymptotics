import SymmetricSubgroupAsymptotics.FactorialUniformPolylogSubquadraticCount
import SymmetricSubgroupAsymptotics.ImprimitiveTopLogarithmicScaling

/-! One finite constant absorbs every quadratic-logarithmic local charge.
The finite head is a literal finite supremum/sum, not an assumed list of
primitive bounds. This is a scalar helper for weak ordinary degree
induction, not the exact Tracey ceiling or an LMM count theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Filter
open scoped Topology BigOperators
namespace SymmetricSubgroupAsymptotics.WeakTransitivePolylogAbsorption

def localCharge (A n : ℕ) : ℝ :=
  (A : ℝ) * ((Nat.log 2 n + 2 : ℕ) : ℝ) ^ 2

private theorem scaled_charge_le_log_cube (A n : ℕ) (hn : 2 ≤ n) :
    localCharge A n * Real.sqrt (Real.logb 2 (n : ℝ) + 1) ≤
      (18 * (A : ℝ)) * (Real.logb 2 (n : ℝ)) ^ 3 := by
  let L := Real.logb 2 (n : ℝ)
  have hL : 1 ≤ L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hn : (2 : ℝ) ≤ n)
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hh
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hl : (Nat.log 2 n : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    simpa only [Nat.cast_ofNat] using Real.natLog_le_logb n 2
  have hu : ((Nat.log 2 n + 2 : ℕ) : ℝ) ≤ 3 * L := by
    push_cast
    dsimp only [L] at hL ⊢
    linarith only [hl,hL]
  have hs : ((Nat.log 2 n + 2 : ℕ) : ℝ) ^ 2 ≤ 9 * L ^ 2 := by
    have hh := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ ((Nat.log 2 n + 2 : ℕ) : ℝ))
      (by positivity : (0 : ℝ) ≤ 3 * L)).mpr hu
    nlinarith only [hh]
  have hroot : Real.sqrt (L + 1) ≤ 2 * L := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by linarith only [hL],?_⟩
    nlinarith only [hL,sq_nonneg (L - 1)]
  calc
    _ ≤ ((A : ℝ) * (9 * L ^ 2)) * (2 * L) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg A)) hroot
        (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by dsimp only [L]; ring

theorem exists_uniform_scaled_local_budget (A : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, 2 ≤ n →
      localCharge A n * Real.sqrt (Real.logb 2 (n : ℝ) + 1) ≤ K * n := by
  have ht : Tendsto (fun n : ℕ =>
      (18 * (A : ℝ)) * ((Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ))) atTop (𝓝 0) := by
    simpa only [one_mul,add_zero,mul_zero] using
      ((Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 3 one_ne_zero).comp
        tendsto_natCast_atTop_atTop).const_mul (18 * (A : ℝ))
  have hevent : ∀ᶠ n : ℕ in atTop,
      localCharge A n * Real.sqrt (Real.logb 2 (n : ℝ) + 1) ≤ n := by
    filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
      eventually_ge_atTop 2] with n hs hn
    have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsmall : (18 * (A : ℝ)) * (Real.logb 2 (n : ℝ)) ^ 3 ≤ n := by
      have hs' : ((18 * (A : ℝ)) * (Real.logb 2 (n : ℝ)) ^ 3) / (n : ℝ) < 1 := by
        simpa only [mul_div_assoc] using hs
      have hh := (div_lt_iff₀ hp).mp hs'
      simpa only [one_mul] using hh.le
    exact (scaled_charge_le_log_cube A n hn).trans hsmall
  obtain ⟨N,hN⟩ := eventually_atTop.mp hevent
  let K : ℝ := 1 + ∑ m ∈ Finset.range N,
    localCharge A m * Real.sqrt (Real.logb 2 (m : ℝ) + 1)
  have hK : 1 ≤ K := by
    have hh : (0 : ℝ) ≤ ∑ m ∈ Finset.range N,
        localCharge A m * Real.sqrt (Real.logb 2 (m : ℝ) + 1) := by
      apply Finset.sum_nonneg
      intro m hm
      dsimp only [localCharge]
      positivity
    dsimp only [K]
    linarith only [hh]
  refine ⟨K,hK,?_⟩
  intro n hn
  by_cases hlarge : N ≤ n
  · exact (hN n hlarge).trans (le_mul_of_one_le_left (Nat.cast_nonneg n) hK)
  · have hm : n ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have hh : localCharge A n * Real.sqrt (Real.logb 2 (n : ℝ) + 1) ≤
        ∑ m ∈ Finset.range N, localCharge A m * Real.sqrt (Real.logb 2 (m : ℝ) + 1) := by
      apply Finset.single_le_sum (f := fun m =>
        localCharge A m * Real.sqrt (Real.logb 2 (m : ℝ) + 1)) _ hm
      intro m hm
      dsimp only [localCharge]
      positivity
    have hb : localCharge A n * Real.sqrt (Real.logb 2 (n : ℝ) + 1) ≤ K := by
      dsimp only [K]
      linarith only [hh]
    exact hb.trans (le_mul_of_one_le_right (by linarith only [hK] : 0 ≤ K)
      (by exact_mod_cast (show 1 ≤ n by omega) : (1 : ℝ) ≤ n))

theorem sqrt_log_add_one_le_three_quarters (n : ℕ) (hn : 2 ≤ n) :
    Real.sqrt (Real.logb 2 (n : ℝ) + 1) ≤ (3 / 4 : ℝ) * n := by
  have hlog := BinaryAffineDominantPrimeSwitchNumerics.logb_nat_le_sub_one n hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  nlinarith only [hlog,hnR,sq_nonneg ((n : ℝ) - 2)]

end SymmetricSubgroupAsymptotics.WeakTransitivePolylogAbsorption
