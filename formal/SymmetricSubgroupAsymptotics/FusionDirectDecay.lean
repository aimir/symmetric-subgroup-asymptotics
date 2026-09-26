import SymmetricSubgroupAsymptotics.FusionDirectKernelAssembly

/-! Fixed even-prefix first moments give exponentially small forward
coefficients without a coarse estimate for the total subgroup count.
The original factorials, normalizer divisor and guarded benchmark remain
literal. Only a fixed polynomial is added when the graph prefix is kept
in the smaller continuation degree. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- The residual factorial ratio has only the fixed prefix degree. -/
theorem fusion_factorial_ratio_le (b s : ℕ) :
    ((b+s).factorial : ℝ) / (b.factorial : ℝ) ≤ ((b+s : ℕ) : ℝ)^s := by
  have hb : (b.factorial : ℝ) ≠ 0 := by positivity
  have hid : ((b+s).factorial : ℝ) / (b.factorial : ℝ) =
      ((b+1).ascFactorial s : ℝ) := by
    rw [← Nat.factorial_mul_ascFactorial b s, Nat.cast_mul]
    field_simp
  rw [hid]
  exact_mod_cast Nat.ascFactorial_le_pow_add b s

/-- Exact conversion to a cold benchmark ratio at the smaller target.
The cold gap is `32*e`: the original local exponent loses `2*e*b`. -/
theorem fusionDirectKernel_cold_identity (b h r : ℕ) (hr : r ≤ h)
    (D a e : ℝ) :
    fusionDirectKernel b h (2*r) D a e =
      (((b+2*r).factorial : ℝ) / (b.factorial : ℝ)) *
        (2 : ℝ)^(-(((h-r : ℕ) : ℝ)/4-2*e)*((2*r : ℕ) : ℝ)) *
          fusionColdKernel (b+2*r) (h-r) D a (32*e) := by
  have hn : b+2*r+2*(h-r) = b+2*h := by omega
  have hm : ((b+2*r).factorial : ℝ) ≠ 0 := by positivity
  have he : ((((2*h : ℕ) : ℝ)-((2*r : ℕ) : ℝ)-16*e)/8*(b : ℝ)) =
      -(((h-r : ℕ) : ℝ)/4-2*e)*((2*r : ℕ) : ℝ) +
        (((h-r : ℕ) : ℝ)/4-(32*e)/16)*((b+2*r : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hr]
    ring
  unfold fusionDirectKernel fusionNormalizedPointing fusionLocalFactor
    fusionColdKernel fusionPointingRatio
  rw [hn, he, Real.rpow_add (by norm_num : (0 : ℝ)<2)]
  field_simp

/-- Fixed even-prefix coefficients decay in either ambient parity. No
unknown total-count bound is assumed. Strict `r<h` is needed only when
the coefficient is installed in a genuinely forward recurrence. -/
theorem fusionDirectKernel_eventually (h r : ℕ) (hr : r ≤ h)
    {D a e : ℝ} (hD : 0≤D) (ha : 0<a) (he : 0<e) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ b : ℕ in atTop,
      fusionDirectKernel b h (2*r) D a e ≤ C*(2 : ℝ)^(-(e/2)*(b : ℝ)) := by
  let A : ℝ := (2 : ℝ)^(-(((h-r : ℕ) : ℝ)/4-2*e)*((2*r : ℕ) : ℝ))
  have hA : 0<A := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨C,hC,hcold⟩ := fusionColdKernel_eventually (h-r) hD ha
    (show 0<32*e by positivity)
  have hrate : (32*e)/32 = e := by ring
  rw [hrate] at hcold
  have hshift := (tendsto_add_atTop_nat (2*r)).eventually hcold
  refine ⟨A*C*((2*r+1 : ℕ) : ℝ)^(2*r)+1, by positivity, ?_⟩
  filter_upwards [hshift,
    eventually_shifted_natpow_mul_exponential_le (2*r) (2*r) he] with b hb hpoly
  have hshiftExp : (2 : ℝ)^(-e*((b+2*r : ℕ) : ℝ)) ≤
      (2 : ℝ)^(-e*(b : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) r]
  calc
    _ = (((b+2*r).factorial : ℝ)/(b.factorial : ℝ))*A*
        fusionColdKernel (b+2*r) (h-r) D a (32*e) :=
      fusionDirectKernel_cold_identity b h r hr D a e
    _ ≤ (((b+2*r : ℕ) : ℝ)^(2*r))*A*
        (C*(2 : ℝ)^(-e*((b+2*r : ℕ) : ℝ))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (fusion_factorial_ratio_le b (2*r)) hA.le
      · exact hb
      · exact fusionColdKernel_nonneg _ _ hD ha
      · positivity
    _ ≤ (((b+2*r : ℕ) : ℝ)^(2*r))*A*(C*(2 : ℝ)^(-e*(b : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hshiftExp hC.le)
        (by positivity)
    _ = A*C*(((b+2*r : ℕ) : ℝ)^(2*r)*(2 : ℝ)^(-e*(b : ℝ))) := by ring
    _ ≤ A*C*(((2*r+1 : ℕ) : ℝ)^(2*r)*(2 : ℝ)^(-(e/2)*(b : ℝ))) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ ≤ _ := by
      have hp := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ)<2) (-(e/2)*(b : ℝ))
      nlinarith

/-- A complete fixed finite menu has one positive ambient-degree rate.
Every entry keeps its own original width, graph prefix and action divisor. -/
theorem fusionDirectKernel_shifted_finite_sum {ι : Type*} [Fintype ι]
    (h r : ι → ℕ) (D a e : ι → ℝ) (hr : ∀ i, r i ≤ h i)
    (hD : ∀ i, 0≤D i) (ha : ∀ i, 0<a i) (he : ∀ i, 0<e i) :
    ∃ C κ : ℝ, 0<C ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ i, fusionDirectKernel (n-2*h i) (h i) (2*r i) (D i) (a i) (e i) ≤
        C*(2 : ℝ)^(-κ*(n : ℝ)) := by
  have hdecay := fusion_finite_shifted_decay
    (fun i b => fusionDirectKernel b (h i) (2*r i) (D i) (a i) (e i))
    (fun i => 2*h i) 1 (fun i => ?_)
  · simpa only [pow_one] using hdecay
  · obtain ⟨C,hC,hbound⟩ :=
      fusionDirectKernel_eventually (h i) (r i) (hr i) (hD i) (ha i) (he i)
    exact ⟨C,e i/2,hC,div_pos (he i) (by norm_num),
      by simpa only [pow_one] using hbound⟩

end SymmetricSubgroupAsymptotics
