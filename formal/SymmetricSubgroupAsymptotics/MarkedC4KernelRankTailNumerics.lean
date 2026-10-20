import SymmetricSubgroupAsymptotics.BinaryKernelRankTailNumerics
import SymmetricSubgroupAsymptotics.Non2PreE7F20MarkedC4Numerics

/-! Numerical tails for the full C4 character mark on one actual source.
The marked moment is an explicit input here, proved from ordinary literature
by MarkedC4ActualGlobalMarkedMoment. This module does not replace C4 marks by
binary rank and makes no claim about actual action coverage. -/
set_option autoImplicit false
noncomputable section
open Filter
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
namespace MarkedC4KernelRankTailNumerics

def tilt (b : ℕ) : ℕ := (b+199)/200

def raw (C : ℝ) (k b : ℕ) : ℝ :=
  C*(b.factorial : ℝ)^k*((2 : ℝ)^(-((tilt b : ℝ)*(51/200)*b))*markedC4Moment b (tilt b))

def pointed (h : ℕ) (a C : ℝ) (k b : ℕ) : ℝ :=
  growingQuotientNormalizedPointing b (2*h) a*raw C k b

theorem square_completion (b : ℕ) :
    (b : ℝ)^2/16+(b : ℝ)*(tilt b)/4+(tilt b : ℝ)^2/2-
      (tilt b : ℝ)*(51/200)*b ≤
        (b : ℝ)^2/16-(b : ℝ)^2/80000+1/2 := by
  have hlo : b ≤ 200*tilt b := by unfold tilt; omega
  have hhi : 200*tilt b ≤ b+199 := by unfold tilt; omega
  have hloR : (b : ℝ) ≤ 200*(tilt b : ℝ) := by exact_mod_cast hlo
  have hhiR : 200*(tilt b : ℝ) ≤ (b : ℝ)+199 := by exact_mod_cast hhi
  have hd0 : 0 ≤ (tilt b : ℝ)-(b : ℝ)/200 := by linarith
  have hd1 : (tilt b : ℝ)-(b : ℝ)/200 ≤ 1 := by linarith
  nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hd1)]

/-- The full C4 mark has a strict quadratic tail after any fixed factorial
loss. Uniformity in the moving marker is supplied by the proved moment. -/
theorem raw_eventually (hm : GlobalMarkedC4MomentBound)
    (C : ℝ) (hC : 0 ≤ C) (k : ℕ) :
    ∀ᶠ b : ℕ in atTop,
      raw C k b ≤ C*(2 : ℝ)^((b : ℝ)^2/16-(b : ℝ)^2/100000+1/2) := by
  let epsilon : ℝ := 1/100000000
  let gamma : ℝ := 1/(100000000*((k : ℝ)+1))
  have hepsilon : 0 < epsilon := by norm_num [epsilon]
  have hgamma : 0 < gamma := by dsimp [gamma]; positivity
  have hkg : (k : ℝ)*gamma ≤ 1/100000000 := by
    dsimp [gamma]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ)<100000000)).2
    have hk : 0 ≤ (k : ℝ) := by positivity
    field_simp
    nlinarith
  filter_upwards [hm epsilon hepsilon 1,eventually_ge_atTop 1,
    eventually_succ_le_two_rpow hgamma] with b hmark hb hsucc
  have hq : tilt b ≤ b := by unfold tilt; omega
  have hqR : (tilt b : ℝ) ≤ (b : ℝ) := by exact_mod_cast hq
  have hs := hmark (tilt b) (by simpa using hqR)
  have hfac : (b.factorial : ℝ)^k ≤
      (2 : ℝ)^((k : ℝ)*gamma*(b : ℝ)^2) := by
    have hf : (b.factorial : ℝ) ≤ ((b+1 : ℕ) : ℝ)^b := by
      exact_mod_cast factorial_le_succ_pow b
    calc
      _ ≤ ((((b+1 : ℕ) : ℝ)^b)^k) := pow_le_pow_left₀ (by positivity) hf k
      _ = (((b+1 : ℕ) : ℝ)^(k*b)) := by rw [← pow_mul,Nat.mul_comm b k]
      _ ≤ ((2 : ℝ)^(gamma*b))^(k*b) := pow_le_pow_left₀ (by positivity) hsucc _
      _ = _ := by
        rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0 : ℝ)≤2)]
        congr 1
        push_cast
        ring
  have hdeg : ((b : ℝ)+(tilt b : ℝ))^2 ≤ 4*(b : ℝ)^2 := by
    have hq0 : (0 : ℝ) ≤ tilt b := by positivity
    have hb0 : (0 : ℝ) ≤ b := by positivity
    nlinarith
  have herr := mul_le_mul_of_nonneg_left hdeg hepsilon.le
  have hkg' := mul_le_mul_of_nonneg_right hkg (sq_nonneg (b : ℝ))
  have hsq := square_completion b
  have hexp : (k : ℝ)*gamma*(b : ℝ)^2+(-((tilt b : ℝ)*(51/200)*b))+
      ((b : ℝ)^2/16+(b : ℝ)*(tilt b)/4+(tilt b : ℝ)^2/2+
        epsilon*((b : ℝ)+tilt b)^2) ≤
      (b : ℝ)^2/16-(b : ℝ)^2/100000+1/2 := by
    dsimp [epsilon] at herr ⊢
    nlinarith
  have hmoment0 : 0 ≤ markedC4Moment b (tilt b) := by
    unfold markedC4Moment
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hcombine (x y z : ℝ) : C*(2 : ℝ)^x*((2 : ℝ)^y*(2 : ℝ)^z) =
      C*(2 : ℝ)^(x+y+z) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ)<2),Real.rpow_add (by norm_num : (0 : ℝ)<2)]
    ring
  unfold raw
  calc
    _ ≤ C*(2 : ℝ)^((k : ℝ)*gamma*(b : ℝ)^2)*
        ((2 : ℝ)^(-((tilt b : ℝ)*(51/200)*b))*
          (2 : ℝ)^((b : ℝ)^2/16+(b : ℝ)*(tilt b)/4+(tilt b : ℝ)^2/2+
            epsilon*((b : ℝ)+tilt b)^2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hfac hC)
        (mul_le_mul_of_nonneg_left hs (by positivity))
        (mul_nonneg (by positivity) hmoment0) (mul_nonneg hC (by positivity))
    _ = C*(2 : ℝ)^((k : ℝ)*gamma*(b : ℝ)^2+(-((tilt b : ℝ)*(51/200)*b))+
        ((b : ℝ)^2/16+(b : ℝ)*(tilt b)/4+(tilt b : ℝ)^2/2+
          epsilon*((b : ℝ)+tilt b)^2)) := hcombine _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) hC

theorem pointed_eventually (hm : GlobalMarkedC4MomentBound)
    (h k : ℕ) (hh : 6 ≤ h) (a C : ℝ) (ha : 1 ≤ a) (hC : 0 ≤ C) :
    ∀ᶠ b : ℕ in atTop,
      pointed h a C k b ≤ (eulerProduct⁻¹*C)*(2 : ℝ)^(-((b : ℝ)^2)/100000) := by
  filter_upwards [raw_eventually hm C hC k,eventually_ge_atTop (2*h)] with b hb hbw
  have hp0 := fusionHot_pointing_denominator_le b h hbw
  have hp : growingQuotientNormalizedPointing b (2*h) a ≤
      eulerProduct⁻¹*(2 : ℝ)^(-(((b+2*h : ℕ) : ℝ)^2)/16+
        5*((b+2*h : ℕ) : ℝ)/8+1/4) := by
    unfold growingQuotientNormalizedPointing
    exact (div_le_div_of_nonneg_right
      (div_le_self (by positivity) ha) (exactBenchmark_pos _).le).trans hp0
  have heuler : 0 ≤ eulerProduct⁻¹ := inv_nonneg.mpr euler_positive.le
  have hraw : 0 ≤ raw C k b := by
    have hmoment0 : 0 ≤ markedC4Moment b (tilt b) := by
      unfold markedC4Moment
      exact Finset.sum_nonneg (fun _ _ => by positivity)
    unfold raw
    positivity
  have he : -(((b+2*h : ℕ) : ℝ)^2)/16+5*((b+2*h : ℕ) : ℝ)/8+1/4+
      ((b : ℝ)^2/16-(b : ℝ)^2/100000+1/2) ≤ -((b : ℝ)^2)/100000 := by
    have hhR : (6 : ℝ) ≤ h := by exact_mod_cast hh
    have hbR : (0 : ℝ) ≤ b := by positivity
    push_cast
    nlinarith [mul_nonneg hbR (sub_nonneg.mpr hhR)]
  have hc (x y : ℝ) : (eulerProduct⁻¹*(2 : ℝ)^x)*(C*(2 : ℝ)^y) =
      (eulerProduct⁻¹*C)*(2 : ℝ)^(x+y) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ)<2)]
    ring
  unfold pointed
  calc
    _ ≤ (eulerProduct⁻¹*(2 : ℝ)^(-(((b+2*h : ℕ) : ℝ)^2)/16+
          5*((b+2*h : ℕ) : ℝ)/8+1/4))*
        (C*(2 : ℝ)^((b : ℝ)^2/16-(b : ℝ)^2/100000+1/2)) :=
      mul_le_mul hp hb hraw (by positivity)
    _ = _ := hc _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) he) (by positivity)

/-- The full marked kernel tail is an admissible exceptional scalar. -/
def exponentialBound (hm : GlobalMarkedC4MomentBound)
    (h k : ℕ) (hh : 6 ≤ h) (a C : ℝ) (ha : 1 ≤ a) (hC : 0 ≤ C) :
    ExponentialScalarBound (pointed h a C k) := by
  let H := eventually_atTop.mp (pointed_eventually hm h k hh a C ha hC)
  let N := Classical.choose H
  have hN := Classical.choose_spec H
  have heuler : 0 ≤ eulerProduct⁻¹ := inv_nonneg.mpr euler_positive.le
  refine
    { threshold := max N 1
      rate := 1/100000
      constant := eulerProduct⁻¹*C+1
      rate_pos := by norm_num
      constant_pos := by positivity
      bound := ?_ }
  intro b hb
  have hn : N ≤ b := (le_max_left _ _).trans hb
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (le_max_right _ _).trans hb
  have he : -((b : ℝ)^2)/100000 ≤ -(1/100000 : ℝ)*b := by nlinarith
  exact (hN b hn).trans (mul_le_mul (by linarith)
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) he)
    (by positivity) (by positivity))

end MarkedC4KernelRankTailNumerics
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
