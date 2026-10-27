import SymmetricSubgroupAsymptotics.LMMUniformRectangularLiftCost

/-! The whole-base lift rectangle with any fixed logarithmic power.
Power2 is the actual simple-kernel/top-rank contribution. The finite
small-r window is bounded by a finite sum, without a uniform model
capacity hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Filter
open scoped Topology BigOperators
namespace SymmetricSubgroupAsymptotics.LMMPolylogRectangularLiftCost

private theorem term_le_sum_abs (n : ℕ) (f : Fin n → ℝ) (i : Fin n) :
    f i ≤ ∑ j : Fin n, |f j| := by
  have hh : |f i| ≤ ∑ j : Fin n, |f j| :=
    Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin n => |f j|)
      (fun j _ => abs_nonneg (f j)) (Finset.mem_univ i)
  exact (le_abs_self (f i)).trans hh

def polyRate (C : ℝ) (d r t : ℕ) : ℝ :=
  (C*((Real.logb 2 (r : ℝ))^d/(r : ℝ)))/Real.sqrt (Real.logb 2 (t : ℝ))

theorem uniform_rectangle (C : ℝ) (hC : 0≤C) (d : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, ∀ r t : ℕ, 2≤r → 2≤t → N≤r*t → polyRate C d r t ≤ ε := by
  have hlim : Tendsto (fun r : ℕ => C*((Real.logb 2 (r : ℝ))^d/(r : ℝ)))
      atTop (𝓝 0) := by
    simpa only [one_mul,add_zero,mul_zero] using
      ((Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 d one_ne_zero).comp
        tendsto_natCast_atTop_atTop).const_mul C
  obtain ⟨R₀,hR⟩ := eventually_atTop.mp (hlim.eventually (eventually_lt_nhds hε))
  let R := max 2 R₀
  let M : ℝ := ∑ i : Fin R, |C*((Real.logb 2 (i.val : ℝ))^d/(i.val : ℝ))|
  have hlog : Tendsto (fun t : ℕ => Real.logb 2 (t : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ)<2)).comp tendsto_natCast_atTop_atTop
  have hroot : Tendsto (fun t : ℕ => Real.sqrt (Real.logb 2 (t : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlog
  obtain ⟨T₀,hT⟩ := eventually_atTop.mp (hroot.eventually_ge_atTop (M/ε))
  let T := max 2 T₀
  refine ⟨R*T,?_⟩
  intro r t hr ht hn
  have hrR : (2 : ℝ)≤r := by exact_mod_cast hr
  have htR : (2 : ℝ)≤t := by exact_mod_cast ht
  have hlr : 0≤Real.logb 2 (r : ℝ) := Real.logb_nonneg (by norm_num) (by linarith only [hrR])
  have hlt : 1≤Real.logb 2 (t : ℝ) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
      (by norm_num : (0 : ℝ)<2) htR
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2)] using hh
  have hs : 1≤Real.sqrt (Real.logb 2 (t : ℝ)) := Real.one_le_sqrt.mpr hlt
  have hspos : 0<Real.sqrt (Real.logb 2 (t : ℝ)) := by linarith only [hs]
  by_cases hlarge : R≤r
  · have hb : C*((Real.logb 2 (r : ℝ))^d/(r : ℝ))≤ε :=
      (hR r ((le_max_right _ _).trans hlarge)).le
    exact (div_le_self (by positivity : (0 : ℝ)≤C*((Real.logb 2 (r : ℝ))^d/(r : ℝ))) hs).trans hb
  · have hsmall : r<R := Nat.lt_of_not_ge hlarge
    have hlargeT : T≤t := by
      by_contra hsmallT
      have hh : r*t<R*T :=
        (Nat.mul_lt_mul_of_pos_right hsmall (by omega : 0<t)).trans
          (Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge hsmallT)
            (by have hh := le_max_left 2 R₀; omega : 0<R))
      omega
    have hden : M/ε≤Real.sqrt (Real.logb 2 (t : ℝ)) :=
      hT t ((le_max_right _ _).trans hlargeT)
    have hM : M/Real.sqrt (Real.logb 2 (t : ℝ))≤ε := by
      apply (div_le_iff₀ hspos).mpr
      simpa only [mul_comm] using (div_le_iff₀ hε).mp hden
    have hcoef : C*((Real.logb 2 (r : ℝ))^d/(r : ℝ))≤M :=
      term_le_sum_abs R (fun i : Fin R => C*((Real.logb 2 (i.val : ℝ))^d/(i.val : ℝ)))
        (⟨r,hsmall⟩ : Fin R)
    exact (div_le_div_of_nonneg_right hcoef hspos.le).trans hM

theorem whole_base_lift_exponent (C : ℝ) (hC : 0≤C) (d : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, ∀ r t : ℕ, 2≤r → 2≤t → N≤r*t →
      C*(t : ℝ)^2*(r : ℝ)*(Real.logb 2 (r : ℝ))^d/
        Real.sqrt (Real.logb 2 (t : ℝ)) ≤ ε*((r*t : ℕ) : ℝ)^2 := by
  obtain ⟨N,hN⟩ := uniform_rectangle C hC d ε hε
  refine ⟨N,?_⟩
  intro r t hr ht hn
  have hr0 : (r : ℝ)≠0 := by exact_mod_cast (show r≠0 by omega)
  have ht0 : Real.sqrt (Real.logb 2 (t : ℝ))≠0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    apply Real.logb_pos (by norm_num : (1 : ℝ)<2)
    exact_mod_cast (show 1<t by omega)
  calc
    _ = polyRate C d r t*((r*t : ℕ) : ℝ)^2 := by
      dsimp only [polyRate]
      push_cast
      field_simp [hr0,ht0]
    _ ≤ ε*((r*t : ℕ) : ℝ)^2 :=
      mul_le_mul_of_nonneg_right (hN r t hr ht hn) (sq_nonneg _)

end SymmetricSubgroupAsymptotics.LMMPolylogRectangularLiftCost
