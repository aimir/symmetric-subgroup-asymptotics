import SymmetricSubgroupAsymptotics.BinaryWidthAsymptotics

/-! Subquadratic growth of a numerical exponent proposed for the binary
wide menu. Its five summands correspond to two cumulative-width factors,
a squared Boolean width, a lower-degree cumulative width and a linear
term. This module proves only their asymptotics. It does not assert that
any actual action, normal-subgroup, frame, cut or cohomology menu has this
mass, and it assumes no such counting statement. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace SymmetricSubgroupAsymptotics

/-- A real-valued exponent, avoiding natural subtraction in w−1. At
positive k it is exactly the proposed expression with w=2^k. The value
at k=0 is harmless and plays no role in the asymptotic conclusions. -/
def binaryMenuExponent (k : ℕ) : ℝ :=
  2*((2 : ℝ)^k-1)*(binaryCumulativeWidth k : ℝ)+
    ((k-1).choose ((k-1)/2) : ℝ)^2+
    ((2 : ℝ)^k/2)*(1+(binaryCumulativeWidth (k-1) : ℝ))+(2 : ℝ)^k

/-- The successor normalization separates exactly the two already
proved vanishing width ratios and the reciprocal exponential. -/
theorem binaryMenuExponent_normalized_succ (k : ℕ) :
    binaryMenuExponent (k+1)/((2 : ℝ)^(k+1))^2 =
      2*(1-1/(2 : ℝ)^(k+1))*
          ((binaryCumulativeWidth (k+1) : ℝ)/(2 : ℝ)^(k+1))+
        (((k.choose (k/2) : ℝ)/(2 : ℝ)^k)^2)/4+
        ((binaryCumulativeWidth k : ℝ)/(2 : ℝ)^k)/4+
        (3/2 : ℝ)*(1/(2 : ℝ)^(k+1)) := by
  have hp : (2 : ℝ)^k≠0 := pow_ne_zero _ (by norm_num)
  simp only [binaryMenuExponent,Nat.add_sub_cancel,
    show (2 : ℝ)^(k+1)=(2 : ℝ)^k*2 from pow_succ _ _]
  field_simp [hp]
  <;> ring

/-- The proposed numerical exponent is o(w²), with w=2^k. No weighted
menu estimate or subgroup-count premise is present. -/
theorem binaryMenuExponent_normalized_tendsto_zero :
    Tendsto (fun k : ℕ => binaryMenuExponent k/((2 : ℝ)^k)^2) atTop (𝓝 0) := by
  have hA := binaryCumulativeWidth_normalized_tendsto_zero
  have hB := binary_middle_normalized_tendsto_zero
  have hA1 : Tendsto
      (fun k : ℕ => (binaryCumulativeWidth (k+1) : ℝ)/(2 : ℝ)^(k+1))
      atTop (𝓝 0) := hA.comp (tendsto_add_atTop_nat 1)
  have hinv : Tendsto (fun k : ℕ => 1/(2 : ℝ)^(k+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ)<2)).comp
        (tendsto_add_atTop_nat 1))
  have hfactor : Tendsto (fun k : ℕ => 2*(1-1/(2 : ℝ)^(k+1)))
      atTop (𝓝 (2 : ℝ)) := by
    simpa using (((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hinv).const_mul (2 : ℝ))
  have hsum : Tendsto (fun k : ℕ =>
      2*(1-1/(2 : ℝ)^(k+1))*
          ((binaryCumulativeWidth (k+1) : ℝ)/(2 : ℝ)^(k+1))+
        (((k.choose (k/2) : ℝ)/(2 : ℝ)^k)^2)/4+
        ((binaryCumulativeWidth k : ℝ)/(2 : ℝ)^k)/4+
        (3/2 : ℝ)*(1/(2 : ℝ)^(k+1))) atTop (𝓝 0) := by
    simpa using
      (((hfactor.mul hA1).add
        ((hB.pow 2).div_const 4)).add (hA.div_const 4)).add
          (hinv.const_mul (3/2 : ℝ))
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [binaryMenuExponent_normalized_succ] using hsum

/-- Every positive quadratic coefficient eventually dominates the
proposed exponent. The threshold is purely numerical. -/
theorem binaryMenuExponent_eventually_le (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop, binaryMenuExponent k≤ε*((2 : ℝ)^k)^2 := by
  filter_upwards [binaryMenuExponent_normalized_tendsto_zero.eventually
    (gt_mem_nhds hε)] with k hk
  exact ((div_lt_iff₀ (by positivity : (0 : ℝ)<((2 : ℝ)^k)^2)).mp hk).le

/-- The exact coefficient used by the numerical wide direct-kernel sum. -/
theorem binaryMenuExponent_eventually_le_one128 :
    ∀ᶠ k : ℕ in atTop, binaryMenuExponent k≤((2 : ℝ)^k)^2/128 := by
  filter_upwards [binaryMenuExponent_eventually_le (1/128) (by norm_num)] with k hk
  convert hk using 1 <;> ring

end SymmetricSubgroupAsymptotics
