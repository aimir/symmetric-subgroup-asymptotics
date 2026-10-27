import SymmetricSubgroupAsymptotics.LMMPolylogRectangularLiftCost

/-! Scalar absorption of the literal affine local quotient envelope.
The actual affine order gives a quadratic-logarithmic binary order
exponent; no bounded-degree table or generation callback is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Filter
open scoped Topology
namespace SymmetricSubgroupAsymptotics.LMMAffineWreathEnvelopeNumerics

def affineCount (t a q s : ℕ) : ℕ := 2^((t*a)^2)*s^(t*q)

theorem affineCount_large_local (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ r t a q s : ℕ, R ≤ r → 2 ≤ r → 2 ≤ t → 1 ≤ s →
      (a : ℝ) ≤ A*(Real.logb 2 (r : ℝ))^2 → Real.logb 2 (s : ℝ) ≤ a →
      (q : ℝ) ≤ C*(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ)) →
      (affineCount t a q s : ℝ) ≤ (2 : ℝ)^(ε*((r*t : ℕ) : ℝ)^2) := by
  have hlim : Tendsto (fun r : ℕ => A^2*(Real.logb 2 (r : ℝ))^4/(r : ℝ))
      atTop (𝓝 0) := by
    simpa only [one_mul,add_zero,mul_zero,mul_div_assoc] using
      ((Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 4 one_ne_zero).comp
        tendsto_natCast_atTop_atTop).const_mul (A^2)
  obtain ⟨R₀,hR⟩ := eventually_atTop.mp (hlim.eventually (eventually_lt_nhds (by positivity : (0 : ℝ)<ε/2)))
  obtain ⟨N,hN⟩ := LMMPolylogRectangularLiftCost.whole_base_lift_exponent
    (A*C) (mul_nonneg hA hC) 2 (ε/2) (by positivity)
  refine ⟨max R₀ N,?_⟩
  intro r t a q s hlarge hr ht hs ha hslog hq
  let L := Real.logb 2 (r : ℝ)
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hrp : 0 < (r : ℝ) := by linarith only [hrR]
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num) (by linarith only [hrR])
  have hslog0 : 0 ≤ Real.logb 2 (s : ℝ) := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast hs : (1 : ℝ) ≤ s)
  have hroot : 0 < Real.sqrt (Real.logb 2 (t : ℝ)) :=
    Real.sqrt_pos.mpr (Real.logb_pos (by norm_num) (by exact_mod_cast (show 1 < t by omega)))
  have hsmall : A^2*L^4 ≤ (ε/2)*(r : ℝ) :=
    ((div_lt_iff₀ hrp).mp (hR r ((le_max_left _ _).trans hlarge))).le
  have hasq : (a : ℝ)^2 ≤ A^2*L^4 := by
    convert pow_le_pow_left₀ (Nat.cast_nonneg a) ha 2 using 1 <;> ring
  have hrr : (r : ℝ) ≤ (r : ℝ)^2 := by
    have hh := le_mul_of_one_le_right hrp.le (by linarith only [hrR] : (1 : ℝ) ≤ r)
    simpa only [pow_two] using hh
  have himage : ((t*a : ℕ) : ℝ)^2 ≤ (ε/2)*((r*t : ℕ) : ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_left
      (hasq.trans (hsmall.trans (mul_le_mul_of_nonneg_left hrr (by positivity))))
      (sq_nonneg (t : ℝ))
    push_cast
    convert hh using 1 <;> ring
  have hsbound : Real.logb 2 (s : ℝ) ≤ A*(r : ℝ)*L^2 := by
    have hh := le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ A*L^2)
      (by linarith only [hrR] : (1 : ℝ) ≤ r)
    exact (hslog.trans ha).trans (by nlinarith only [hh])
  have htop : (t : ℝ)*(q : ℝ)*Real.logb 2 (s : ℝ) ≤
      (A*C)*(t : ℝ)^2*(r : ℝ)*L^2/Real.sqrt (Real.logb 2 (t : ℝ)) := by
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg t))
      hsbound hslog0 (by positivity)
    convert hh using 1 <;> ring
  have hrt : N ≤ r*t := ((le_max_right _ _).trans hlarge).trans
    (Nat.le_mul_of_pos_right r (by omega))
  have htop' := htop.trans (hN r t hr ht hrt)
  have hs0 : 0 < s := by omega
  have hpositive : (0 : ℝ) < (affineCount t a q s : ℝ) := by
    dsimp only [affineCount]
    positivity
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ)<2) hpositive).mp
  simp only [affineCount,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [Real.logb_mul (by positivity : (2 : ℝ)^((t*a)^2) ≠ 0)
    (by positivity : (s : ℝ)^(t*q) ≠ 0),Real.logb_pow,Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2)]
  push_cast at himage htop' ⊢
  nlinarith only [himage,htop']

end SymmetricSubgroupAsymptotics.LMMAffineWreathEnvelopeNumerics
