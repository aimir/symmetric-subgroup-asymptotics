import SymmetricSubgroupAsymptotics.Non2PreE7Y1RankTailDecay

/-! A reusable numerical rank-tail estimate for kernels of fixed finite
index. Any fixed factorial power is absorbed by the same quadratic deficit.
The actual subgroup sum must still be proved by the source constructor. -/
set_option autoImplicit false
noncomputable section
open Filter
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
namespace BinaryKernelRankTailNumerics

def raw (C : ℝ) (k b : ℕ) : ℝ :=
  C * (b.factorial : ℝ)^k *
    ((2 : ℝ)^(-((rankTail51Tilt b : ℝ)*(51/200)*b)) *
      (subgroupCount (b+2*rankTail51Tilt b) : ℝ))

def pointed (h : ℕ) (a C : ℝ) (k b : ℕ) : ℝ :=
  growingQuotientNormalizedPointing b (2*h) a * raw C k b

/-- Arbitrary fixed factorial losses leave a uniform quadratic deficit.
The constant quarter comes only from rounding the marker tilt. -/
theorem raw_eventually
    (hc : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (C : ℝ) (hC : 0 ≤ C) (k : ℕ) :
    ∀ᶠ b : ℕ in atTop,
      raw C k b ≤ C * (2 : ℝ)^((b : ℝ)^2/16-(b : ℝ)^2/50000+1/4) := by
  let epsilon : ℝ := 1/10000000
  let gamma : ℝ := 1/(10000000*((k : ℝ)+1))
  have hepsilon : 0 < epsilon := by norm_num [epsilon]
  have hgamma : 0 < gamma := by dsimp [gamma]; positivity
  have hkg : (k : ℝ)*gamma ≤ 1/10000000 := by
    dsimp [gamma]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ)<10000000)).2
    have hk : 0 ≤ (k : ℝ) := by positivity
    field_simp
    nlinarith
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hc epsilon hepsilon)
  filter_upwards [eventually_ge_atTop (max N 1),
    eventually_succ_le_two_rpow hgamma] with b hb hsucc
  let q := rankTail51Tilt b
  let M := b+2*q
  have hb1 : 1 ≤ b := (le_max_right _ _).trans hb
  have hbN : N ≤ b := (le_max_left _ _).trans hb
  have hM3 : M ≤ 3*b := by dsimp [M,q,rankTail51Tilt]; omega
  have hM3R : (M : ℝ) ≤ 3*(b : ℝ) := by exact_mod_cast hM3
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hM2 : (M : ℝ)^2 ≤ 9*(b : ℝ)^2 := by nlinarith
  have hs := hN M (hbN.trans (Nat.le_add_right _ _))
  have hfac : (b.factorial : ℝ)^k ≤
      (2 : ℝ)^((k : ℝ)*gamma*(b : ℝ)^2) := by
    have hf : (b.factorial : ℝ) ≤ ((b+1 : ℕ) : ℝ)^b := by
      exact_mod_cast factorial_le_succ_pow b
    calc
      _ ≤ ((((b+1 : ℕ) : ℝ)^b)^k) := pow_le_pow_left₀ (by positivity) hf k
      _ = (((b+1 : ℕ) : ℝ)^(k*b)) := by rw [← pow_mul, Nat.mul_comm b k]
      _ ≤ ((2 : ℝ)^(gamma*b))^(k*b) :=
        pow_le_pow_left₀ (by positivity) hsucc _
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ)≤2)]
        congr 1
        push_cast
        ring
  have hsq : (M : ℝ)^2/16-(q : ℝ)*(51/200)*b ≤
      (b : ℝ)^2/16-(b : ℝ)^2/40000+1/4 := by
    simpa only [M,q,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using
      y1RankTail_squareCompletion b
  have herr : epsilon*(M : ℝ)^2 ≤ 9*epsilon*(b : ℝ)^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hM2 hepsilon.le]
  have hkg' := mul_le_mul_of_nonneg_right hkg (sq_nonneg (b : ℝ))
  have hexp : (k : ℝ)*gamma*(b : ℝ)^2 +
      (-((q : ℝ)*(51/200)*b)) + (1/16+epsilon)*(M : ℝ)^2 ≤
      (b : ℝ)^2/16-(b : ℝ)^2/50000+1/4 := by
    dsimp [epsilon] at herr ⊢
    nlinarith
  have hsource : raw C k b ≤
      C * (2 : ℝ)^((k : ℝ)*gamma*(b : ℝ)^2) *
        ((2 : ℝ)^(-((q : ℝ)*(51/200)*b)) *
          (2 : ℝ)^((1/16+epsilon)*(M : ℝ)^2)) := by
    unfold raw
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hfac hC)
      (mul_le_mul_of_nonneg_left hs (by positivity))
      (by positivity) (mul_nonneg hC (by positivity))
  calc
    _ ≤ _ := hsource
    _ = C * (2 : ℝ)^((k : ℝ)*gamma*(b : ℝ)^2+
        (-((q : ℝ)*(51/200)*b))+(1/16+epsilon)*(M : ℝ)^2) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ)<2),
        Real.rpow_add (by norm_num : (0 : ℝ)<2)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) hC

/-- Widths twelve and above pay their original pointing and action divisor.
No source family or action weight has been dropped. -/
theorem pointed_eventually
    (hc : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (h k : ℕ) (hh : 6 ≤ h) (a C : ℝ) (ha : 1 ≤ a) (hC : 0 ≤ C) :
    ∀ᶠ b : ℕ in atTop,
      pointed h a C k b ≤
        (eulerProduct⁻¹*C) * (2 : ℝ)^(-((b : ℝ)^2)/50000) := by
  filter_upwards [raw_eventually hc C hC k, eventually_ge_atTop (2*h)] with b hb hbw
  have hp0 := fusionHot_pointing_denominator_le b h hbw
  have hp : growingQuotientNormalizedPointing b (2*h) a ≤
      eulerProduct⁻¹*(2 : ℝ)^(-(((b+2*h : ℕ) : ℝ)^2)/16+
        5*((b+2*h : ℕ) : ℝ)/8+1/4) := by
    unfold growingQuotientNormalizedPointing
    exact (div_le_div_of_nonneg_right
      (div_le_self (by positivity) ha) (exactBenchmark_pos _).le).trans hp0
  have hraw : 0 ≤ raw C k b := by unfold raw; positivity
  have he : -(((b+2*h : ℕ) : ℝ)^2)/16+
      5*((b+2*h : ℕ) : ℝ)/8+1/4+
      ((b : ℝ)^2/16-(b : ℝ)^2/50000+1/4) ≤ -((b : ℝ)^2)/50000 := by
    have hhR : (6 : ℝ) ≤ h := by exact_mod_cast hh
    have hbR : (0 : ℝ) ≤ b := by positivity
    push_cast
    nlinarith [mul_nonneg hbR (sub_nonneg.mpr hhR)]
  have heuler : 0 ≤ eulerProduct⁻¹ := inv_nonneg.mpr euler_positive.le
  have hcombine (x y : ℝ) : (eulerProduct⁻¹*(2 : ℝ)^x)*(C*(2 : ℝ)^y) =
      (eulerProduct⁻¹*C)*(2 : ℝ)^(x+y) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ)<2)]
    ring
  unfold pointed
  calc
    _ ≤ (eulerProduct⁻¹*(2 : ℝ)^(-(((b+2*h : ℕ) : ℝ)^2)/16+
          5*((b+2*h : ℕ) : ℝ)/8+1/4)) *
        (C*(2 : ℝ)^((b : ℝ)^2/16-(b : ℝ)^2/50000+1/4)) :=
      mul_le_mul hp hb hraw (by positivity)
    _ = (eulerProduct⁻¹*C)*(2 : ℝ)^(
        -(((b+2*h : ℕ) : ℝ)^2)/16+5*((b+2*h : ℕ) : ℝ)/8+1/4+
          ((b : ℝ)^2/16-(b : ℝ)^2/50000+1/4)) := hcombine _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) he) (by positivity)

/-- Fixed finite-index rank tails are admissible exceptional scalars. -/
def exponentialBound
    (hc : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (h k : ℕ) (hh : 6 ≤ h) (a C : ℝ) (ha : 1 ≤ a) (hC : 0 ≤ C) :
    ExponentialScalarBound (pointed h a C k) := by
  let H := eventually_atTop.mp (pointed_eventually hc h k hh a C ha hC)
  let N := Classical.choose H
  have hN := Classical.choose_spec H
  have heuler : 0 ≤ eulerProduct⁻¹ := inv_nonneg.mpr euler_positive.le
  refine
    { threshold := max N 1
      rate := 1 / 50000
      constant := eulerProduct⁻¹*C+1
      rate_pos := by norm_num
      constant_pos := by positivity
      bound := ?_ }
  intro b hb
  have hn : N ≤ b := (le_max_left _ _).trans hb
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (le_max_right _ _).trans hb
  have he : -((b : ℝ)^2)/50000 ≤ -(1/50000 : ℝ)*b := by nlinarith
  exact (hN b hn).trans (mul_le_mul (by linarith)
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) he)
    (by positivity) (by positivity))

end BinaryKernelRankTailNumerics
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
