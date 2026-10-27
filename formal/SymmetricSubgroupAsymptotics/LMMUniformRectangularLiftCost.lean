import SymmetricSubgroupAsymptotics.WeakTransitivePolylogAbsorption

/-! Uniform rectangular decay of the genuine whole-base lift cost.
The block-top weak rank bound contributes Ct/sqrt(log₂t); the local
permutation order contributes at most r*log₂r per block. Their complete
lift exponent is o((rt)^2), uniformly as rt grows. No subgroup-kernel
count or global LMM conclusion is asserted here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Filter
open scoped Topology
namespace SymmetricSubgroupAsymptotics.LMMUniformRectangularLiftCost

def liftRate (C : ℝ) (r t : ℕ) : ℝ :=
  (C * (Real.logb 2 (r : ℝ) / (r : ℝ))) / Real.sqrt (Real.logb 2 (t : ℝ))

theorem uniform_rectangle (C : ℝ) (hC : 0 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ r t : ℕ, 2 ≤ r → 2 ≤ t → N ≤ r * t → liftRate C r t ≤ ε := by
  have hlim : Tendsto (fun r : ℕ => C * (Real.logb 2 (r : ℝ) / (r : ℝ)))
      atTop (𝓝 0) := by
    simpa only [pow_one,one_mul,add_zero,mul_zero] using
      ((Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop).const_mul C
  obtain ⟨R₀,hR₀⟩ := eventually_atTop.mp (hlim.eventually (eventually_lt_nhds hε))
  have hlog : Tendsto (fun t : ℕ => Real.logb 2 (t : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  have hroot : Tendsto (fun t : ℕ => Real.sqrt (Real.logb 2 (t : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlog
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp (hroot.eventually_ge_atTop (C / ε))
  let R := max 2 R₀
  let T := max 2 T₀
  refine ⟨R * T,?_⟩
  intro r t hr ht hn
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hrl : 0 < Real.logb 2 (r : ℝ) := Real.logb_pos (by norm_num) (by linarith only [hrR])
  have htl : 1 ≤ Real.logb 2 (t : ℝ) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) htR
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hh
  have hs : 1 ≤ Real.sqrt (Real.logb 2 (t : ℝ)) := Real.one_le_sqrt.mpr htl
  have hspos : 0 < Real.sqrt (Real.logb 2 (t : ℝ)) := by linarith only [hs]
  by_cases hlarge : R ≤ r
  · have hb : C * (Real.logb 2 (r : ℝ) / (r : ℝ)) ≤ ε :=
      (hR₀ r ((le_max_right _ _).trans hlarge)).le
    exact (div_le_self (mul_nonneg hC (div_nonneg hrl.le (by linarith only [hrR]))) hs).trans hb
  · have hlargeT : T ≤ t := by
      by_contra hsmall
      have hp : r * t < R * T :=
        (Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_ge hlarge) (by omega : 0 < t)).trans
          (Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge hsmall)
            (by have hh := le_max_left 2 R₀; omega : 0 < R))
      omega
    have hden : C / ε ≤ Real.sqrt (Real.logb 2 (t : ℝ)) :=
      hT₀ t ((le_max_right _ _).trans hlargeT)
    have hsmall : C / Real.sqrt (Real.logb 2 (t : ℝ)) ≤ ε := by
      apply (div_le_iff₀ hspos).mpr
      simpa only [mul_comm] using (div_le_iff₀ hε).mp hden
    have hlogr := BinaryAffineDominantPrimeSwitchNumerics.logb_nat_le_sub_one r hr
    have hratio : Real.logb 2 (r : ℝ) / (r : ℝ) ≤ 1 :=
      (div_le_one₀ (by linarith only [hrR] : (0 : ℝ) < r)).mpr (by linarith only [hlogr])
    exact (div_le_div_of_nonneg_right
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio hC) hspos.le).trans hsmall

theorem whole_base_lift_exponent (C : ℝ) (hC : 0 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ r t : ℕ, 2 ≤ r → 2 ≤ t → N ≤ r * t →
      C * (t : ℝ) ^ 2 * ((r : ℝ) * Real.logb 2 (r : ℝ)) /
        Real.sqrt (Real.logb 2 (t : ℝ)) ≤ ε * ((r * t : ℕ) : ℝ) ^ 2 := by
  obtain ⟨N,hN⟩ := uniform_rectangle C hC ε hε
  refine ⟨N,?_⟩
  intro r t hr ht hn
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have ht0 : Real.sqrt (Real.logb 2 (t : ℝ)) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    apply Real.logb_pos (by norm_num : (1 : ℝ) < 2)
    exact_mod_cast (show 1 < t by omega)
  calc
    _ = liftRate C r t * ((r * t : ℕ) : ℝ) ^ 2 := by
      dsimp only [liftRate]
      push_cast
      field_simp [hr0,ht0] <;> ring
    _ ≤ ε * ((r * t : ℕ) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (hN r t hr ht hn) (sq_nonneg _)

end SymmetricSubgroupAsymptotics.LMMUniformRectangularLiftCost
