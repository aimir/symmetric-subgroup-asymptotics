import SymmetricSubgroupAsymptotics.MarkedC4ErrorCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Numerical physical-degree convolution. Odd configurations remain in
the sum; their quadratic exponent is paid by the physical degree reserve.
This file makes no assertion that a literal encoding has been constructed. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.PhysicalOddConvolution

def degrees (b : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (b+1)) ×ˢ (Finset.range (b+1))).filter (fun z => z.1+z.2≤b)

def count (binary : ℕ → ℕ → ℝ) (odd : ℕ → ℝ) (b r : ℕ) : ℝ :=
  ∑ z ∈ degrees b, binary z.1 r * odd z.2

def coarseError (C : ℝ) (b : ℕ) : ℝ := C*b*Real.sqrt b

theorem coarseError_negligible {C : ℝ} (hC : 0≤C) :
    UniformQuadraticNegligible (fun b _ => coarseError C b) := by
  intro ε hε K
  filter_upwards [eventually_ge_atTop (⌈(C/ε)^2⌉₊)] with b hb
  intro r _
  have hb0 : (0 : ℝ)≤b := Nat.cast_nonneg b
  have hbb : (C/ε)^2≤(b : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hb)
  have hs := Real.sqrt_le_sqrt hbb
  rw [Real.sqrt_sq (div_nonneg hC hε.le)] at hs
  have hc : C≤ε*Real.sqrt b := by
    have := (div_le_iff₀ hε).mp hs
    simpa only [mul_comm] using this
  have hr0 : (0 : ℝ)≤r := Nat.cast_nonneg r
  have hmul := mul_le_mul_of_nonneg_right hc (mul_nonneg hb0 (Real.sqrt_nonneg (b : ℝ)))
  have heq : ε*Real.sqrt b*((b : ℝ)*Real.sqrt b)=ε*(b : ℝ)^2 := by
    calc
      _ = ε*(b : ℝ)*(Real.sqrt b)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hb0]; ring
  rw [heq] at hmul
  calc
    coarseError C b = C*((b : ℝ)*Real.sqrt b) := by unfold coarseError; ring
    _ ≤ ε*(b : ℝ)^2 := hmul
    _ ≤ ε*((b : ℝ)+r)^2 := by
      apply mul_le_mul_of_nonneg_left _ hε.le
      exact (sq_le_sq₀ hb0 (add_nonneg hb0 hr0)).mpr
        (le_add_of_nonneg_right hr0)

/-- The polynomial number of degree pairs costs only a bounded-word error. -/
theorem degree_card_bound (b _r : ℕ) :
    (degrees b).card ≤ (b+1)^2 := by
  have h := Finset.card_le_card (Finset.filter_subset
    (fun z : ℕ × ℕ => z.1+z.2≤b)
    ((Finset.range (b+1)) ×ˢ (Finset.range (b+1))))
  simpa [degrees,Finset.card_product,pow_two] using h

theorem polynomial_cost (b r : ℕ) :
    ((b+1 : ℕ)^2 : ℝ) ≤ (2 : ℝ)^(boundedWordError 1 b r) := by
  by_cases hb : b=0
  · subst b
    simp [boundedWordError]
  have hb1 : (1 : ℝ)≤b := by exact_mod_cast (show 1≤b by omega)
  have hr0 : (0 : ℝ)≤r := Nat.cast_nonneg r
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ)<2) (by positivity)).mp
  rw [Real.logb,Real.log_pow]
  have hl : Real.log ((b : ℝ)+1)≤Real.log ((b : ℝ)+r+2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hn : 0≤Real.log ((b : ℝ)+r+2) := Real.log_nonneg (by linarith)
  unfold boundedWordError
  push_cast
  have ht := mul_le_mul_of_nonneg_right hb1 hn
  have hd : 0<Real.log 2 := Real.log_pos (by norm_num)
  apply (div_le_iff₀ hd).mpr
  field_simp
  nlinarith

/-- Exact all-mark, all-degree bound before asymptotic specialization. -/
theorem bound {binary : ℕ → ℕ → ℝ} {odd : ℕ → ℝ}
    {E : ℕ → ℕ → ℝ} {C : ℝ} (hC : 0≤C)
    (hbinary0 : ∀ a r, 0≤binary a r) (hodd0 : ∀ d, 0≤odd d)
    (hbinary : ∀ a r, binary a r≤(2 : ℝ)^(markedF a r+E a r))
    (hodd : ∀ d, odd d≤(2 : ℝ)^((d : ℝ)^2/16+coarseError C d))
    (hE : ∀ a b r, a≤b → E a r≤E b r) (b r : ℕ) :
    count binary odd b r≤
      (2 : ℝ)^(markedF b r+E b r+coarseError C b+boundedWordError 1 b r) := by
  have hterm (z : ℕ × ℕ) (hz : z∈degrees b) :
      binary z.1 r*odd z.2≤(2 : ℝ)^(markedF b r+E b r+coarseError C b) := by
    have hsplit : z.1+z.2≤b := (Finset.mem_filter.mp hz).2
    have ha : z.1≤b := by omega
    have hd : z.2≤b := by omega
    have hreserve := markedF_split (m := (z.1 : ℝ)) (d := (z.2 : ℝ))
      (b := (b : ℝ)) (r := (r : ℝ)) (by positivity) (by positivity) (by positivity)
      (by exact_mod_cast hsplit)
    have he := hE z.1 b r ha
    have hc : coarseError C z.2≤coarseError C b := by
      unfold coarseError
      gcongr
    calc
      _ ≤ (2 : ℝ)^(markedF z.1 r+E z.1 r) *
          (2 : ℝ)^((z.2 : ℝ)^2/16+coarseError C z.2) :=
        mul_le_mul (hbinary _ _) (hodd _) (hodd0 _) (by positivity)
      _ = (2 : ℝ)^((markedF z.1 r+E z.1 r)+
          ((z.2 : ℝ)^2/16+coarseError C z.2)) := (Real.rpow_add (by norm_num) _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hs := Finset.sum_le_sum hterm
  unfold count
  calc
    _ ≤ (degrees b).card * (2 : ℝ)^(markedF b r+E b r+coarseError C b) := by
      simpa using hs
    _ ≤ (2 : ℝ)^(boundedWordError 1 b r) *
        (2 : ℝ)^(markedF b r+E b r+coarseError C b) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hcard : ((degrees b).card : ℝ) ≤ ((b+1 : ℕ)^2 : ℝ) := by
        exact_mod_cast degree_card_bound b r
      exact hcard.trans (polynomial_cost b r)
    _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ)<2)]; congr 1; ring

/-- Any negligible monotone binary error and the ordinary coarse odd error
therefore give the same marked main term uniformly in every bounded window. -/
theorem negligible_bound {binary : ℕ → ℕ → ℝ} {odd : ℕ → ℝ}
    {E : ℕ → ℕ → ℝ} {C : ℝ} (hC : 0≤C)
    (hbinary0 : ∀ a r, 0≤binary a r) (hodd0 : ∀ d, 0≤odd d)
    (hbinary : ∀ a r, binary a r≤(2 : ℝ)^(markedF a r+E a r))
    (hodd : ∀ d, odd d≤(2 : ℝ)^((d : ℝ)^2/16+coarseError C d))
    (hE : ∀ a b r, a≤b → E a r≤E b r)
    (hnegligible : UniformQuadraticNegligible E) :
    ∀ ε : ℝ, 0<ε → ∀ K : ℝ, ∀ᶠ b : ℕ in atTop, ∀ r : ℕ,
      (r : ℝ)≤K*b → count binary odd b r≤
        (2 : ℝ)^(markedF b r+ε*((b : ℝ)+r)^2) := by
  apply markedMomentBound_of_error
    (e := fun b r => E b r+coarseError C b+boundedWordError 1 b r)
  · intro b r
    simpa only [add_assoc] using bound hC hbinary0 hodd0 hbinary hodd hE b r
  · exact (hnegligible.add (coarseError_negligible hC)).add
      (boundedWordError_negligible (by norm_num))
end SymmetricSubgroupAsymptotics.MarkedC4.PhysicalOddConvolution
