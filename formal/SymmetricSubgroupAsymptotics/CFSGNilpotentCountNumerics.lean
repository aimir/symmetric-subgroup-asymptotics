import SymmetricSubgroupAsymptotics.CFSGOddNilpotentCountNumerics

/-! The bounded physical binary/odd convolution has the same leading
quadratic coefficient as its two coordinates. All error terms here are
explicit fixed-cutoff multiples of `b log₂(b+2)`. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGNilpotentCountBudgets
open MarkedC4

def jointCoefficient (C : ℕ) : ℝ :=
  max (CFSGOrdinaryBoundedBinaryCount.coefficient C) (oddCoefficient C)

theorem jointCoefficient_nonneg (C : ℕ) : 0 ≤ jointCoefficient C :=
  (oddCoefficient_nonneg C).trans (le_max_right _ _)

theorem split_quadratic {a d b : ℕ} (h : a + d ≤ b) :
    (a : ℝ) ^ 2 / 16 + (d : ℝ) ^ 2 / 16 ≤ (b : ℝ) ^ 2 / 16 := by
  have hr : (a : ℝ) + d ≤ b := by exact_mod_cast h
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  nlinarith [sq_nonneg ((b : ℝ) - a - d), mul_nonneg ha hd]

theorem joint_term_le (C b a d : ℕ) (h : a + d ≤ b) :
    (Nat.card (BoundedNilpotentTargetConvolution.BinaryFamily C a) : ℝ) *
      (Nat.card (CFSGNilpotentBinaryOddConvolution.OddFamily C d) : ℝ) ≤
    (2 : ℝ) ^ ((b : ℝ) ^ 2 / 16 + jointCoefficient C * b * degreeLog b) := by
  have ha : a ≤ b := by omega
  have hd : d ≤ b := by omega
  have hA := jointCoefficient_nonneg C
  have heA : CFSGOrdinaryBoundedBinaryCount.coefficient C ≤ jointCoefficient C :=
    le_max_left _ _
  have heD : oddCoefficient C ≤ jointCoefficient C := le_max_right _ _
  have hLa : 0 ≤ degreeLog a := le_trans (by norm_num) (one_le_degreeLog a)
  have hLd : 0 ≤ degreeLog d := le_trans (by norm_num) (one_le_degreeLog d)
  have hcostA : CFSGOrdinaryBoundedBinaryCount.coefficient C * a * degreeLog a ≤
      jointCoefficient C * a * degreeLog b := by
    calc
      _ ≤ jointCoefficient C * a * degreeLog a := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left (degreeLog_mono ha) (by positivity)
  have hcostD : oddCoefficient C * d * degreeLog d ≤
      jointCoefficient C * d * degreeLog b := by
    calc
      _ ≤ jointCoefficient C * d * degreeLog d := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left (degreeLog_mono hd) (by positivity)
  have hcost : jointCoefficient C * a * degreeLog b +
      jointCoefficient C * d * degreeLog b ≤ jointCoefficient C * b * degreeLog b := by
    have hr : (a : ℝ) + d ≤ b := by exact_mod_cast h
    nlinarith [mul_le_mul_of_nonneg_left hr
      (mul_nonneg hA (le_trans (by norm_num) (one_le_degreeLog b)))]
  have ht := mul_pow2_bounds (binary_card_le C a) (odd_nilpotent_card_le C d)
    (Nat.cast_nonneg _)
  exact ht.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (by linarith [split_quadratic h]))

theorem nilpotent_card_le_of_one_lt (C b : ℕ) (hC : 1 < C) (hb : 1 ≤ b) :
    (Nat.card (OrbitCutoffFamilies.NilpotentFamily C b) : ℝ) ≤
      (2 : ℝ) ^ ((b : ℝ) ^ 2 / 16 + (jointCoefficient C + 5) * b * degreeLog b) := by
  let E : ℝ := (b : ℝ) ^ 2 / 16 + jointCoefficient C * b * degreeLog b
  have hs : (∑ z : PhysicalOddConvolution.degrees b,
      (Nat.card (BoundedNilpotentTargetConvolution.BinaryFamily C z.1.1) : ℝ) *
        (Nat.card (CFSGNilpotentBinaryOddConvolution.OddFamily C z.1.2) : ℝ)) ≤
      ((PhysicalOddConvolution.degrees b).card : ℝ) * (2 : ℝ) ^ E := by
    calc
      _ ≤ ∑ _z : PhysicalOddConvolution.degrees b, (2 : ℝ) ^ E := by
        apply Finset.sum_le_sum
        intro z _
        exact joint_term_le C b z.1.1 z.1.2 (Finset.mem_filter.mp z.2).2
      _ = _ := by simp
  have hcard : ((PhysicalOddConvolution.degrees b).card : ℝ) ≤ (b + 1 : ℝ) ^ 2 := by
    exact_mod_cast PhysicalOddConvolution.degree_card_bound b 0
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hp := power_le_budget (b + 1) 2 b (by omega)
  have hp₀ : (b + 1 : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * degreeLog b) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hp
  have hp' : (b + 1 : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * (b : ℝ) * degreeLog b) := by
    apply hp₀.trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [one_le_degreeLog b]
  have hl := power_le_budget (b + 1) (3 * b) b (by omega)
  have hlabels : (b + 1 : ℝ) ^ (3 * b) ≤
      (2 : ℝ) ^ (3 * (b : ℝ) * degreeLog b) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using hl
  have hc : (Nat.card (OrbitCutoffFamilies.NilpotentFamily C b) : ℝ) ≤
      (b + 1 : ℝ) ^ (3 * b) *
        (∑ z : PhysicalOddConvolution.degrees b,
          (Nat.card (BoundedNilpotentTargetConvolution.BinaryFamily C z.1.1) : ℝ) *
            (Nat.card (CFSGNilpotentBinaryOddConvolution.OddFamily C z.1.2) : ℝ)) := by
    exact_mod_cast CFSGNilpotentBinaryOddConvolution.nilpotent_card_le (b := b) hC
  have hs' : (∑ z : PhysicalOddConvolution.degrees b,
      (Nat.card (BoundedNilpotentTargetConvolution.BinaryFamily C z.1.1) : ℝ) *
        (Nat.card (CFSGNilpotentBinaryOddConvolution.OddFamily C z.1.2) : ℝ)) ≤
      (2 : ℝ) ^ (2 * (b : ℝ) * degreeLog b + E) := by
    exact (hs.trans (mul_le_mul_of_nonneg_right hcard (by positivity))).trans
      (mul_pow2_bounds hp' le_rfl (by positivity))
  have hprod := mul_pow2_bounds hlabels hs' (by positivity)
  apply hc.trans
  convert hprod using 1 <;> dsimp [E] <;> congr 1 <;> ring

def cutoffEnlargement (C b : ℕ) : OrbitCutoffFamilies.NilpotentFamily C b →
    OrbitCutoffFamilies.NilpotentFamily (max C 2) b :=
  fun G => ⟨G.val, G.property.1, fun x =>
    lt_of_lt_of_le (G.property.2 x) (le_max_left _ _)⟩

theorem bounded_nilpotent_card : ∀ C : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ b : ℕ,
    (Nat.card (OrbitCutoffFamilies.NilpotentFamily C b) : ℝ) ≤
      (2 : ℝ) ^ ((b : ℝ) ^ 2 / 16 + A * b * Real.logb 2 (b + 2)) := by
  intro C
  refine ⟨jointCoefficient (max C 2) + 5, by linarith [jointCoefficient_nonneg (max C 2)], ?_⟩
  intro b
  by_cases hb : b = 0
  · subst b
    simpa using zero_family_card_le_one (fun G => Group.IsNilpotent G ∧
      OrbitCutoffFamilies.OrbitCutoff C G)
  · have hi : Function.Injective (cutoffEnlargement C b) := by
      intro G H h
      apply Subtype.ext
      exact congrArg (fun z : OrbitCutoffFamilies.NilpotentFamily (max C 2) b => z.val) h
    have hc : (Nat.card (OrbitCutoffFamilies.NilpotentFamily C b) : ℝ) ≤
        (Nat.card (OrbitCutoffFamilies.NilpotentFamily (max C 2) b) : ℝ) := by
      exact_mod_cast Nat.card_le_card_of_injective (cutoffEnlargement C b) hi
    exact hc.trans (nilpotent_card_le_of_one_lt (max C 2) b (by omega) (by omega))

end SymmetricSubgroupAsymptotics.CFSGNilpotentCountBudgets
