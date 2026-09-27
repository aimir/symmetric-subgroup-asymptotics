import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Elementary decay of the Boolean antichain width divided by the
whole Boolean cube. The bound follows from the exact central-binomial
recurrence; no Stirling formula or group-theoretic input is used. -/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology BigOperators

namespace SymmetricSubgroupAsymptotics

/-- A simple square bound sufficient for the normalized width to vanish. -/
theorem centralBinom_square_bound (n : ℕ) :
    (n+1)*(Nat.centralBinom n)^2 ≤ 16^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : (n+1)^2*(Nat.centralBinom (n+1))^2 =
        (2*(2*n+1))^2*(Nat.centralBinom n)^2 := by
      have hs := congrArg (fun t : ℕ => t^2) (Nat.succ_mul_centralBinom_succ n)
      dsimp only at hs
      simpa only [mul_pow] using hs
    have hc : (n+2)*(2*(2*n+1))^2 ≤ 16*(n+1)^3 := by nlinarith
    apply Nat.le_of_mul_le_mul_left _ (pow_pos (Nat.succ_pos n) 2)
    calc
      (n+1)^2*((n+1+1)*(Nat.centralBinom (n+1))^2) =
          (n+2)*((n+1)^2*(Nat.centralBinom (n+1))^2) := by ring
      _ = ((n+2)*(2*(2*n+1))^2)*(Nat.centralBinom n)^2 := by rw [he]; ring
      _ ≤ (16*(n+1)^3)*(Nat.centralBinom n)^2 := Nat.mul_le_mul_right _ hc
      _ = (16*(n+1)^2)*((n+1)*(Nat.centralBinom n)^2) := by ring
      _ ≤ (16*(n+1)^2)*16^n := Nat.mul_le_mul_left _ ih
      _ = (n+1)^2*16^(n+1) := by rw [pow_succ]; ring

private theorem odd_middle_le_twice_central (m : ℕ) :
    (2*m+1).choose m ≤ 2*Nat.centralBinom m := by
  by_cases hm : m=0
  · subst m; decide
  · rw [Nat.choose_succ_left _ _ (by omega)]
    have h := Nat.add_le_add (Nat.choose_le_centralBinom (m-1) m)
      (Nat.choose_le_centralBinom m m)
    simpa only [two_mul] using h

/-- Both parities satisfy the same normalized central-width estimate. -/
theorem binary_middle_square_bound (n : ℕ) :
    (n/2+1)*(n.choose (n/2))^2 ≤ 4^n := by
  obtain ⟨m, he | ho⟩ : ∃ m, n=2*m ∨ n=2*m+1 := ⟨n/2, by omega⟩
  · subst n
    rw [Nat.mul_div_cancel_left _ (by decide : 0<2)]
    change (m+1)*(Nat.centralBinom m)^2 ≤ 4^(2*m)
    have hp : 4^(2*m) = 16^m := by rw [pow_mul]; rfl
    rw [hp]
    exact centralBinom_square_bound _
  · subst n
    rw [show (2*m+1)/2=m by omega]
    calc
      _ ≤ (m+1)*(2*Nat.centralBinom m)^2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (odd_middle_le_twice_central m) 2)
      _ = 4*((m+1)*(Nat.centralBinom m)^2) := by ring
      _ ≤ 4*16^m := Nat.mul_le_mul_left _ (centralBinom_square_bound _)
      _ = 4^(2*m+1) := by rw [pow_succ, pow_mul]; ring

theorem binary_middle_normalized_square_le (n : ℕ) :
    ((n.choose (n/2) : ℝ)/(2:ℝ)^n)^2 ≤ 2/((n:ℝ)+1) := by
  have hn : (0:ℝ)<(n:ℝ)+1 := by positivity
  have hp : 0 < ((2:ℝ)^n)^2 := by positivity
  have hpow : ((2:ℝ)^n)^2 = (4:ℝ)^n := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  have h : ((n/2+1 : ℕ):ℝ)*(n.choose (n/2) : ℝ)^2 ≤ (4:ℝ)^n := by
    exact_mod_cast binary_middle_square_bound n
  have hs : ((n/2+1 : ℕ):ℝ)*((n.choose (n/2) : ℝ)/(2:ℝ)^n)^2 ≤ 1 := by
    rw [div_pow, ← mul_div_assoc]
    apply (div_le_one hp).mpr
    simpa only [hpow] using h
  have hhalf : (n:ℝ)+1 ≤ 2*((n/2+1 : ℕ):ℝ) := by
    exact_mod_cast (show n+1≤2*(n/2+1) by omega)
  apply (le_div_iff₀ hn).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hhalf)
    (sq_nonneg ((n.choose (n/2) : ℝ)/(2:ℝ)^n))]

/-- Only this vanishing ratio is needed to make the proposed binary
menu exponent subquadratic. No menu bound is asserted here. -/
theorem binary_middle_normalized_tendsto_zero :
    Tendsto (fun n : ℕ => (n.choose (n/2) : ℝ)/(2:ℝ)^n) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (2:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have ht' : Tendsto (fun n : ℕ => Real.sqrt ((2:ℝ)/((n:ℝ)+1))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht'
  · intro n; positivity
  · intro n
    have h := Real.sqrt_le_sqrt (binary_middle_normalized_square_le n)
    simpa only [Real.sqrt_sq (show (0:ℝ)≤(n.choose (n/2) : ℝ)/(2:ℝ)^n by positivity)] using h

/-- A geometrically normalized prefix sum preserves a vanishing ratio.
The finite initial segment is absorbed into one fixed constant. -/
theorem sum_range_div_two_pow_tendsto_zero {b : ℕ → ℝ}
    (hb : ∀ n, 0≤b n)
    (ht : Tendsto (fun n => b n/(2:ℝ)^n) atTop (𝓝 0)) :
    Tendsto (fun n => (∑ j ∈ Finset.range n, b j)/(2:ℝ)^n) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Filter.Eventually.of_forall (fun n => ha.trans_le
      (div_nonneg (Finset.sum_nonneg (fun j _ => hb j)) (by positivity)))
  · intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (ht.eventually (gt_mem_nhds (half_pos hε)))
    let C : ℝ := ∑ j ∈ Finset.range N, b j
    have hC : 0≤C := Finset.sum_nonneg (fun j _ => hb j)
    have hsum (n : ℕ) : (∑ j ∈ Finset.range n, b j) ≤ C+(ε/2)*(2:ℝ)^n := by
      induction n with
      | zero => simpa only [Finset.range_zero, Finset.sum_empty, pow_zero, mul_one] using
          (add_nonneg hC (half_pos hε).le)
      | succ n ih =>
        by_cases hn : n<N
        · have hc : (∑ j ∈ Finset.range (n+1), b j) ≤ C :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
              (fun j _ _ => hb j)
          exact hc.trans (le_add_of_nonneg_right (by positivity))
        · have hn' : N≤n := by omega
          have hbn : b n≤(ε/2)*(2:ℝ)^n :=
            ((div_lt_iff₀ (by positivity)).mp (hN n hn')).le
          rw [Finset.sum_range_succ]
          calc
            _ ≤ (C+(ε/2)*(2:ℝ)^n)+(ε/2)*(2:ℝ)^n := add_le_add ih hbn
            _ = C+(ε/2)*(2:ℝ)^(n+1) := by rw [pow_succ]; ring
    have hhead : Tendsto (fun n : ℕ => C/(2:ℝ)^n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
    filter_upwards [hhead.eventually (gt_mem_nhds (half_pos hε))] with n hn
    calc
      _ ≤ (C+(ε/2)*(2:ℝ)^n)/(2:ℝ)^n :=
        div_le_div_of_nonneg_right (hsum n) (by positivity)
      _ = C/(2:ℝ)^n+ε/2 := by rw [add_div, mul_div_cancel_right₀ _ (by positivity)]
      _ < ε := by linarith

/-- The cumulative widths arising from successive original pair kernels. -/
def binaryCumulativeWidth (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, j.choose (j/2)

theorem binaryCumulativeWidth_normalized_tendsto_zero :
    Tendsto (fun k => (binaryCumulativeWidth k : ℝ)/(2:ℝ)^k) atTop (𝓝 0) := by
  simpa only [binaryCumulativeWidth, Nat.cast_sum] using
    sum_range_div_two_pow_tendsto_zero
      (b := fun j => (j.choose (j/2) : ℝ)) (fun _ => by positivity)
      binary_middle_normalized_tendsto_zero

end SymmetricSubgroupAsymptotics
