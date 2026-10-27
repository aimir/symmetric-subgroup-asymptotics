import SymmetricSubgroupAsymptotics.LMMRectangularCountAssembly
import SymmetricSubgroupAsymptotics.WeakTransitiveDegreeInduction

/-! Fixed-local-group chief costs. The compressed quotient has degree
s*t with FIXED s; its weak transitive rank retains that actual degree.
Ceilings and any finite chief iteration are absorbed without a new
bounded-degree group-count hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Filter
open scoped Topology BigOperators
namespace SymmetricSubgroupAsymptotics.LMMFixedLocalChiefCostNumerics
open WeakTransitiveDegreeInduction

theorem scaled_rate_le (s t : ℕ) (hs : 1  ≤  s) (ht : 2  ≤  t) :
    rate (s*t)  ≤  (s : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ)) := by
  have htp : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have htlog : 0  <  Real.logb 2 (t : ℝ) :=
    Real.logb_pos (by norm_num) (by exact_mod_cast (show 1 < t by omega))
  have hts : t  ≤  s*t := by
    simpa only [Nat.mul_comm] using Nat.le_mul_of_pos_right t (by omega : 0 < s)
  have hlog : Real.logb 2 (t : ℝ)  ≤  Real.logb 2 ((s*t : ℕ) : ℝ) :=
    Real.logb_le_logb_of_le (by norm_num) htp (by exact_mod_cast hts)
  have hroot := Real.sqrt_le_sqrt hlog
  have hpos := Real.sqrt_pos.mpr htlog
  have hh := div_le_div_of_nonneg_left (Nat.cast_nonneg (s*t)) hpos hroot
  simpa only [rate,Nat.cast_mul] using hh

theorem fixed_layer_exponent_eventually (a c b K : ℝ)
    (hc : 0 ≤ c) (hK : 0 ≤ K)
    (s : ℕ) (hs : 1 ≤ s) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop,
      (t : ℝ)*K*(a*(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ)) +
        c*rate (s*t)+b)  ≤  ε*(t : ℝ)^2 := by
  let D := K*(a+c*(s : ℝ))
  let E := K*b
  have hlog : Tendsto (fun t : ℕ => Real.logb 2 (t : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  have hroot : Tendsto (fun t : ℕ => Real.sqrt (Real.logb 2 (t : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlog
  filter_upwards [hroot.eventually_ge_atTop (D/(ε/2)),
    (tendsto_natCast_atTop_atTop : Tendsto (fun t : ℕ => (t : ℝ)) atTop atTop).eventually_ge_atTop
      (E/(ε/2)),eventually_ge_atTop 2] with t hden hlin ht
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have htp : (0 : ℝ) < t := by linarith only [htR]
  have hpos : 0  <  Real.sqrt (Real.logb 2 (t : ℝ)) :=
    Real.sqrt_pos.mpr (Real.logb_pos (by norm_num) (by linarith only [htR]))
  have hD : D  ≤  (ε/2)*Real.sqrt (Real.logb 2 (t : ℝ)) := by
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : (0 : ℝ) < ε/2)).mp hden
  have hE : E  ≤  (ε/2)*(t : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : (0 : ℝ) < ε/2)).mp hlin
  have hfirst : D*(t : ℝ)^2/Real.sqrt (Real.logb 2 (t : ℝ))  ≤  (ε/2)*(t : ℝ)^2 := by
    apply (div_le_iff₀ hpos).mpr
    convert mul_le_mul_of_nonneg_right hD (sq_nonneg (t : ℝ)) using 1 <;> ring
  have hsecond : E*(t : ℝ)  ≤  (ε/2)*(t : ℝ)^2 := by
    convert mul_le_mul_of_nonneg_right hE htp.le using 1 <;> ring
  calc
    _  ≤  (t : ℝ)*K*(a*(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ)) +
        c*((s : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ)))+b) :=
      mul_le_mul_of_nonneg_left
        (by linarith only [mul_le_mul_of_nonneg_left (scaled_rate_le s t hs ht) hc])
        (by positivity)
    _ = D*(t : ℝ)^2/Real.sqrt (Real.logb 2 (t : ℝ))+E*(t : ℝ) := by
      dsimp only [D,E]
      ring
    _  ≤  ε*(t : ℝ)^2 := by linarith only [hfirst,hsecond]

theorem ceil_charge_eventually (a : ℕ) (c K : ℝ) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (s : ℕ) (hs : 1 ≤ s) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop,
      ((t * Nat.ceil ((a : ℝ)*t/Real.sqrt (Real.logb 2 (t : ℝ)) +
        c*rate (s*t)) : ℕ) : ℝ)*K  ≤  ε*(t : ℝ)^2 := by
  filter_upwards [fixed_layer_exponent_eventually (a : ℝ) c 1 K hc hK s hs ε hε] with t ht
  have hx : 0  ≤  (a : ℝ)*t/Real.sqrt (Real.logb 2 (t : ℝ))+c*rate (s*t) := by
    dsimp only [rate]
    positivity
  have hceil := (Nat.ceil_lt_add_one hx).le
  calc
    _  ≤  (t : ℝ)*K*((a : ℝ)*t/Real.sqrt (Real.logb 2 (t : ℝ))+c*rate (s*t)+1) := by
      push_cast
      convert mul_le_mul_of_nonneg_left hceil (mul_nonneg (Nat.cast_nonneg t) hK) using 1 <;> ring
    _  ≤  ε*(t : ℝ)^2 := ht

theorem finite_sum_quadratic_eventually {I : Type} [Fintype I] (cost : I → ℕ → ℝ)
    (hcost : ∀ i : I, ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℕ in atTop, cost i t  ≤  ε*(t : ℝ)^2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, ∑ i : I,cost i t  ≤  ε*(t : ℝ)^2 := by
  let δ := ε/((Fintype.card I : ℝ)+1)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hall : ∀ᶠ t : ℕ in atTop, ∀ i : I,cost i t  ≤  δ*(t : ℝ)^2 :=
    Filter.eventually_all.mpr (fun i => hcost i δ hδ)
  filter_upwards [hall] with t ht
  have hcoef : (Fintype.card I : ℝ)*δ  ≤  ε := by
    dsimp only [δ]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (Fintype.card I : ℝ)+1)).mpr
    nlinarith only [hε.le]
  calc
    _  ≤  ∑ _i : I,δ*(t : ℝ)^2 := Finset.sum_le_sum (fun i _ => ht i)
    _ = (Fintype.card I : ℝ)*δ*(t : ℝ)^2 := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring
    _  ≤  ε*(t : ℝ)^2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)

end SymmetricSubgroupAsymptotics.LMMFixedLocalChiefCostNumerics
