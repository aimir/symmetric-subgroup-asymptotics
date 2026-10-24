import SymmetricSubgroupAsymptotics.ActualWreathChiefWeightedPrimeBudget

/-! Constructed characteristic weights from ACTUAL prime-power divisors
of the original top degree. The matching characteristic uses the proved
primary bound, all other characteristics the proved prime-to bound. Half
and real-logarithmic bounds are simultaneously retained. The floor one
pays genuine nonabelian ordinary ranks on the SAME chief trace.
No desired aggregate inequality is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathChiefDivisorWeights
open PermutationalWreathProduct ActualWreathCharacteristicChiefProfile
open ActualWreathChiefWeightedPrimeBudget

def divisorRate (t q e p : ℕ) : ℝ :=
  if p = q then (t : ℝ)*Real.sqrt (2/(3*((q : ℝ)-1)*e))
  else (t : ℝ)/(q : ℝ)^e

def divisorWeight (t q e p : ℕ) : ℝ :=
  max 1 (min ((t : ℝ)/2)
    (min (2*(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))) (divisorRate t q e p)))

theorem one_le_divisorWeight (t q e p : ℕ) : 1 ≤ divisorWeight t q e p :=
  le_max_left _ _

theorem capacity_le_divisorWeight {t : ℕ} (c : ElementaryCharge t)
    (q e : ℕ) (hq : q.Prime) (he : 1 ≤ e) (hd : q^e ∣ t) :
    (c.capacity : ℝ) ≤ (c.dimension : ℝ)*divisorWeight t q e c.p := by
  have ha : (0 : ℝ) ≤ c.dimension := by positivity
  have hhalf : (c.capacity : ℝ) ≤ (c.dimension : ℝ)*((t : ℝ)/2) := by
    simpa only [mul_div_assoc] using c.half
  have hlog : (c.capacity : ℝ) ≤
      (c.dimension : ℝ)*(2*(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))) := by
    convert c.logarithmic using 1 <;> ring
  have hbase : (c.capacity : ℝ) ≤ (c.dimension : ℝ)*divisorRate t q e c.p := by
    by_cases hp : c.p = q
    · have hd' : c.p^e ∣ t := by simpa only [hp] using hd
      have hh := c.primary e he hd'
      simpa only [divisorRate,if_pos hp,hp,mul_assoc] using hh
    · have hh := c.primeTo q e hq (Ne.symm hp) hd
      simpa only [divisorRate,if_neg hp,mul_div_assoc] using hh
  have hmin : (c.capacity : ℝ) ≤ (c.dimension : ℝ)*
      min ((t : ℝ)/2)
        (min (2*(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))) (divisorRate t q e c.p)) := by
    rw [mul_min_of_nonneg _ _ ha,mul_min_of_nonneg _ _ ha]
    exact le_min hhalf (le_min hlog hbase)
  exact hmin.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) ha)

theorem capacity_le_min_divisorWeights {t : ℕ} (c : ElementaryCharge t)
    (q e r f : ℕ) (hq : q.Prime) (he : 1 ≤ e) (hd : q^e ∣ t)
    (hr : r.Prime) (hf : 1 ≤ f) (hrd : r^f ∣ t) :
    (c.capacity : ℝ) ≤ (c.dimension : ℝ)*
      min (divisorWeight t q e c.p) (divisorWeight t r f c.p) := by
  rw [mul_min_of_nonneg _ _ (show (0 : ℝ) ≤ c.dimension by positivity)]
  exact le_min (capacity_le_divisorWeight c q e hq he hd)
    (capacity_le_divisorWeight c r f hr hf hrd)

section Chief
variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]

theorem cost_le_divisorWeight {i : I} {S : ActualWreathCompressionState Q I} {n : ℕ}
    (h : ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n)
    (hI : 2 ≤ Fintype.card I) (q e : ℕ) (hq : q.Prime) (he : 1 ≤ e)
    (hd : q^e ∣ Fintype.card I) :
    (n : ℝ) ≤ weightedOrder (divisorWeight (Fintype.card I) q e) (Nat.card S.D) := by
  exact cost_le_weightedOrder h hI _ (one_le_divisorWeight _ q e)
    (fun c => capacity_le_divisorWeight c q e hq he hd)

theorem cost_le_min_divisorWeights {i : I} {S : ActualWreathCompressionState Q I} {n : ℕ}
    (h : ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n)
    (hI : 2 ≤ Fintype.card I) (q e r f : ℕ)
    (hq : q.Prime) (he : 1 ≤ e) (hd : q^e ∣ Fintype.card I)
    (hr : r.Prime) (hf : 1 ≤ f) (hrd : r^f ∣ Fintype.card I) :
    (n : ℝ) ≤ weightedOrder
      (fun p => min (divisorWeight (Fintype.card I) q e p)
        (divisorWeight (Fintype.card I) r f p)) (Nat.card S.D) := by
  apply cost_le_weightedOrder h hI _
  · intro p
    exact le_min (one_le_divisorWeight _ q e p) (one_le_divisorWeight _ r f p)
  · intro c
    exact capacity_le_min_divisorWeights c q e r f hq he hd hr hf hrd
end Chief
end SymmetricSubgroupAsymptotics.ActualWreathChiefDivisorWeights
