import SymmetricSubgroupAsymptotics.MarkedC4UniformCaseIError
import SymmetricSubgroupAsymptotics.MarkedC4ActualUniformEpiReserve

/-! The original-history menu, one terminal stopping cost, and all positive
peel polynomials have a single O_C(b log(b+r+2)) exponent. The global Hall
polynomial is deliberately absent and is paid once by SingleMarkError. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MarkedC4.HistoryMenuError
open RDTNormalFInterface ActualNormalFMarkedPeel

def menuCost (C t : ℕ) : ℝ :=
  (t.factorial : ℝ)*((t : ℝ)+1)^((2^(2^C))*t)

def cost (lit : RDTTheorem46BinaryInput) (C b r t : ℕ) : ℝ :=
  menuCost C t*((b : ℝ)+2)^ActualUniformOriginalCaseI.costExponent C b*
    (ActualUniformEpiReserve.peelFactor lit C b r)^t

def coefficient (lit : RDTTheorem46BinaryInput) (C : ℕ) : ℝ :=
  ((2^(2^C) : ℕ) : ℝ)+1+UniformCaseIError.coefficient C+
    (Real.logb 2 (max (kappa3 lit (2+C)) 1)+kappa4 lit (2+C))

theorem coefficient_nonneg (lit : RDTTheorem46BinaryInput) (C : ℕ) :
    0 ≤ coefficient lit C := by
  have hk : 0 ≤ Real.logb 2 (max (kappa3 lit (2+C)) 1) :=
    Real.logb_nonneg (by norm_num) (le_max_right _ _)
  have he := kappa4_nonneg lit (2+C)
  have hc := UniformCaseIError.coefficient_nonneg C
  unfold coefficient
  positivity

theorem menu_le_power (C b r t : ℕ) (ht : t ≤ b) :
    menuCost C t ≤ ((b : ℝ)+r+2)^((((2^(2^C) : ℕ) : ℝ)+1)*b) := by
  let s : ℝ := (b : ℝ)+r+2
  have hs : 1 ≤ s := by
    dsimp [s]
    linarith [Nat.cast_nonneg (α := ℝ) b,Nat.cast_nonneg (α := ℝ) r]
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hts : (t : ℝ) ≤ s := by
    have htb : (t : ℝ) ≤ b := by exact_mod_cast ht
    dsimp [s]
    linarith [Nat.cast_nonneg (α := ℝ) r]
  have hts1 : (t : ℝ)+1 ≤ s := by
    have htb : (t : ℝ) ≤ b := by exact_mod_cast ht
    dsimp [s]
    linarith [Nat.cast_nonneg (α := ℝ) r]
  have hfac : (t.factorial : ℝ) ≤ s^b := by
    calc
      _ ≤ (t : ℝ)^t := by exact_mod_cast Nat.factorial_le_pow t
      _ ≤ s^t := pow_le_pow_left₀ ht0 hts _
      _ ≤ s^b := pow_le_pow_right₀ hs ht
  have hm : ((t : ℝ)+1)^((2^(2^C))*t) ≤ s^((2^(2^C))*b) :=
    (pow_le_pow_left₀ (by positivity) hts1 _).trans
      (pow_le_pow_right₀ hs (Nat.mul_le_mul_left _ ht))
  unfold menuCost
  calc
    _ ≤ s^b*s^((2^(2^C))*b) := mul_le_mul hfac hm (by positivity) (by positivity)
    _=s^((((2^(2^C) : ℕ) : ℝ)+1)*b) := by
      rw [← pow_add,← Real.rpow_natCast]
      congr 1
      push_cast
      ring

theorem cost_le_power (lit : RDTTheorem46BinaryInput) (C b r t : ℕ)
    (hb : 1 ≤ b) (ht : t ≤ b) :
    cost lit C b r t ≤ ((b : ℝ)+r+2)^(coefficient lit C*b) := by
  let s : ℝ := (b : ℝ)+r+2
  let k : ℝ := max (kappa3 lit (2+C)) 1
  let a : ℝ := Real.logb 2 k
  let e : ℝ := kappa4 lit (2+C)
  have hs2 : 2 ≤ s := by
    dsimp [s]
    linarith [Nat.cast_nonneg (α := ℝ) b,Nat.cast_nonneg (α := ℝ) r]
  have hs : 1 ≤ s := by linarith
  have hs0 : 0<s := by linarith
  have hk : 1 ≤ k := le_max_right _ _
  have ha : 0 ≤ a := Real.logb_nonneg (by norm_num) hk
  have he : 0 ≤ e := kappa4_nonneg lit (2+C)
  have hconst : k ≤ s^a := by
    calc
      k=(2 : ℝ)^a := (Real.rpow_logb (by norm_num) (by norm_num)
        (show 0<k by linarith)).symm
      _ ≤ s^a := Real.rpow_le_rpow (by norm_num) hs2 ha
  have hp : ActualUniformEpiReserve.peelFactor lit C b r ≤ s^(a+e) := by
    unfold ActualUniformEpiReserve.peelFactor
    calc
      _ ≤ s^a*s^e := mul_le_mul_of_nonneg_right hconst (by positivity)
      _=s^(a+e) := (Real.rpow_add hs0 _ _).symm
  have hpeel : (ActualUniformEpiReserve.peelFactor lit C b r)^t ≤ s^((a+e)*b) := by
    calc
      _ ≤ (s^(a+e))^t := pow_le_pow_left₀ (by
        unfold ActualUniformEpiReserve.peelFactor
        positivity) hp _
      _=s^((a+e)*t) := by rw [← Real.rpow_natCast,← Real.rpow_mul hs0.le]
      _ ≤ s^((a+e)*b) := Real.rpow_le_rpow_of_exponent_le hs
        (mul_le_mul_of_nonneg_left (by exact_mod_cast ht) (add_nonneg ha he))
  have hc0 : 0 ≤ ActualUniformOriginalCaseI.costExponent C b := by
    unfold ActualUniformOriginalCaseI.costExponent
    positivity
  have hstop : ((b : ℝ)+2)^ActualUniformOriginalCaseI.costExponent C b ≤
      s^(UniformCaseIError.coefficient C*b) :=
    (Real.rpow_le_rpow (by positivity) (by dsimp [s]; linarith [Nat.cast_nonneg (α := ℝ) r]) hc0).trans
      (Real.rpow_le_rpow_of_exponent_le hs (UniformCaseIError.costExponent_le hb C))
  have hmenu := menu_le_power C b r t ht
  have hp0 : 0 ≤ ActualUniformEpiReserve.peelFactor lit C b r := by
    unfold ActualUniformEpiReserve.peelFactor
    positivity
  unfold cost
  calc
    _ ≤ s^((((2^(2^C) : ℕ) : ℝ)+1)*b)*
        s^(UniformCaseIError.coefficient C*b)*s^((a+e)*b) :=
      mul_le_mul (mul_le_mul hmenu hstop (by positivity) (by positivity))
        hpeel (pow_nonneg hp0 _) (by positivity)
    _=s^(coefficient lit C*b) := by
      rw [← Real.rpow_add hs0,← Real.rpow_add hs0]
      congr 1
      dsimp [coefficient,a,e,k]
      ring

theorem cost_le_error (lit : RDTTheorem46BinaryInput) (C b r t : ℕ)
    (hb : 1 ≤ b) (ht : t ≤ b) :
    cost lit C b r t ≤ (2 : ℝ)^boundedWordError (coefficient lit C) b r := by
  apply (cost_le_power lit C b r t hb ht).trans
  have hd : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hl : 0 ≤ Real.log ((b : ℝ)+r+2) := Real.log_nonneg (by
    linarith [Nat.cast_nonneg (α := ℝ) b,Nat.cast_nonneg (α := ℝ) r])
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ)<2) (by positivity)).mp
  rw [Real.logb,Real.log_rpow (by positivity)]
  apply (div_le_iff₀ hd).mpr
  unfold boundedWordError
  field_simp
  nlinarith [Nat.cast_nonneg (α := ℝ) b]

theorem negligible (lit : RDTTheorem46BinaryInput) (C : ℕ) :
    UniformQuadraticNegligible (boundedWordError (coefficient lit C)) :=
  boundedWordError_negligible (coefficient_nonneg lit C)

end SymmetricSubgroupAsymptotics.MarkedC4.HistoryMenuError
end
