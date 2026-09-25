import SymmetricSubgroupAsymptotics.FusionPointingRatio

/-!
# Exponential cold rows with the original divisor

These are numerical bounds on the literal approved benchmark ratio. They
do not assume a bound for the unknown total subgroup count. Installing the
row in physical subgroup counting still requires the pointed-orbit encoding.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

theorem eventually_natpow_mul_exponential_le (p : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ b : ℕ in atTop,
      (b:ℝ)^p * (2:ℝ)^(-c*b) ≤ (2:ℝ)^(-(c/2)*b) := by
  filter_upwards [eventually_exponential_le_inv_rpow (show 0<c/2 by positivity) p,
    eventually_ge_atTop 1] with b hb hb1
  have hbpos : 0 < (b:ℝ) := by exact_mod_cast (show 0<b by omega)
  rw [Real.rpow_natCast] at hb
  have hsmall : (b:ℝ)^p * (2:ℝ)^(-(c/2)*b) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hb (pow_nonneg hbpos.le p)
    simpa [ne_of_gt hbpos] using this
  calc
    _ = ((b:ℝ)^p * (2:ℝ)^(-(c/2)*b)) * (2:ℝ)^(-(c/2)*b) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
      congr 2
      ring
    _ ≤ 1 * (2:ℝ)^(-(c/2)*b) := mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = _ := one_mul _

theorem eventually_shifted_natpow_mul_exponential_le (s p : ℕ) {c : ℝ} (hc : 0<c) :
    ∀ᶠ b : ℕ in atTop,
      ((b+s:ℕ):ℝ)^p * (2:ℝ)^(-c*b) ≤
        ((s+1:ℕ):ℝ)^p * (2:ℝ)^(-(c/2)*b) := by
  filter_upwards [eventually_natpow_mul_exponential_le p hc,
    eventually_ge_atTop 1] with b hb hb1
  have hbase : ((b+s:ℕ):ℝ) ≤ ((s+1:ℕ):ℝ)*(b:ℝ) := by
    have hbr : 1 ≤ (b:ℝ) := by exact_mod_cast hb1
    push_cast
    nlinarith [mul_nonneg (show 0≤(s:ℝ) by positivity) (sub_nonneg.mpr hbr)]
  calc
    _ ≤ (((s+1:ℕ):ℝ)*(b:ℝ))^p * (2:ℝ)^(-c*b) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase p) (by positivity)
    _ = ((s+1:ℕ):ℝ)^p * ((b:ℝ)^p * (2:ℝ)^(-c*b)) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)

/-- The original pointing factor and original action divisor are literal.
Here the physical removed width is `2*h`. -/
def fusionColdKernel (b h : ℕ) (D a g : ℝ) : ℝ :=
  fusionPointingRatio b h * (D/a) * (2:ℝ)^(((h:ℝ)/4-g/16)*b)

theorem fusionColdKernel_nonneg (b h : ℕ) {D a g : ℝ} (hD : 0≤D) (ha : 0<a) :
    0 ≤ fusionColdKernel b h D a g := by
  unfold fusionColdKernel
  exact mul_nonneg (mul_nonneg (fusionPointingRatio_nonneg b h)
    (div_nonneg hD ha.le)) (by positivity)

theorem fusionColdKernel_le (b h : ℕ) {D a g : ℝ} (hD : 0≤D) (ha : 0<a) :
    fusionColdKernel b h D a g ≤
      (eulerProduct⁻¹^2 * (2:ℝ)^(((h:ℝ)+1)/4) * (D/a)) *
        ((b+2*h+1:ℕ):ℝ)^(h+1) * (2:ℝ)^(-(g/16)*b) := by
  have hφ := euler_positive
  unfold fusionColdKernel
  calc
    _ ≤ (((eulerProduct⁻¹^2 * (2:ℝ)^(((h:ℝ)+1)/4)) *
        ((b+2*h+1:ℕ):ℝ)^(h+1) * (2:ℝ)^(-(h:ℝ)*b/4-(h:ℝ)^2/4)) *
        (D/a)) * (2:ℝ)^(((h:ℝ)/4-g/16)*b) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (fusionPointingRatio_le b h) (div_nonneg hD ha.le))
        (by positivity)
    _ = (eulerProduct⁻¹^2 * (2:ℝ)^(((h:ℝ)+1)/4) * (D/a)) *
        ((b+2*h+1:ℕ):ℝ)^(h+1) * (2:ℝ)^(-(h:ℝ)^2/4-(g/16)*b) := by
      have he : -(h:ℝ)^2/4-(g/16)*b =
          (-(h:ℝ)*b/4-(h:ℝ)^2/4)+(((h:ℝ)/4-g/16)*b) := by ring
      rw [he, Real.rpow_add (by norm_num : (0:ℝ)<2)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [sq_nonneg (h:ℝ)]))
      (by positivity)

/-- Fixed-width original cold kernels decay exponentially in the complete
complement degree, uniformly across its parity. -/
theorem fusionColdKernel_eventually (h : ℕ) {D a g : ℝ}
    (hD : 0≤D) (ha : 0<a) (hg : 0<g) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ b : ℕ in atTop,
      fusionColdKernel b h D a g ≤ C * (2:ℝ)^(-(g/32)*b) := by
  let A : ℝ := eulerProduct⁻¹^2 * (2:ℝ)^(((h:ℝ)+1)/4) * (D/a)
  have hφ := euler_positive
  have hA : 0≤A := by dsimp [A]; positivity
  refine ⟨A*((2*h+2:ℕ):ℝ)^(h+1)+1, by positivity, ?_⟩
  filter_upwards [eventually_shifted_natpow_mul_exponential_le (2*h+1) (h+1)
    (show 0<g/16 by positivity)] with b hb
  have hshift : b+(2*h+1) = b+2*h+1 := by omega
  rw [hshift] at hb
  have hr : (g/16)/2 = g/32 := by ring
  rw [hr] at hb
  calc
    _ ≤ A * (((b+2*h+1:ℕ):ℝ)^(h+1) * (2:ℝ)^(-(g/16)*b)) := by
      simpa [A,mul_assoc] using fusionColdKernel_le b h hD ha
    _ ≤ A * (((2*h+2:ℕ):ℝ)^(h+1) * (2:ℝ)^(-(g/32)*b)) :=
      mul_le_mul_of_nonneg_left hb hA
    _ ≤ _ := by nlinarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (-(g/32)*b)]

/-- Every fixed finite menu has one positive common cold-row rate. The
normalizer divisors are retained separately in every summand. -/
theorem fusionColdKernel_finite_sum {ι : Type*} [Fintype ι]
    (h : ι → ℕ) (D a g : ι → ℝ) {γ : ℝ} (hγ : 0<γ)
    (hD : ∀ i, 0≤D i) (ha : ∀ i, 0<a i) (hg : ∀ i, γ≤g i) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ b : ℕ in atTop,
      (∑ i, fusionColdKernel b (h i) (D i) (a i) (g i)) ≤
        C * (2:ℝ)^(-(γ/32)*b) := by
  choose C hC hbound using fun i ↦ fusionColdKernel_eventually (h i) (hD i) (ha i)
    (hγ.trans_le (hg i))
  have hs : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ ↦ (hC i).le)
  refine ⟨(∑ i, C i)+1, by positivity, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hbound] with b hb
  calc
    _ ≤ ∑ i, C i * (2:ℝ)^(-(γ/32)*b) := by
      apply Finset.sum_le_sum
      intro i _
      apply (hb i).trans
      apply mul_le_mul_of_nonneg_left _ (hC i).le
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [mul_nonneg (sub_nonneg.mpr (hg i)) (show 0≤(b:ℝ) by positivity)]
    _ = (∑ i, C i) * (2:ℝ)^(-(γ/32)*b) := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end SymmetricSubgroupAsymptotics
