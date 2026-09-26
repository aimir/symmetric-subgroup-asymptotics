import SymmetricSubgroupAsymptotics.OddCriticalProfiles
import SymmetricSubgroupAsymptotics.BinaryCarrierProfileWeights

/-! Exact original S3 weights after contraction to one additional C2
coordinate. The marker has normalizer six; the extra C2 occurrence has
its own factorial. Every carrier profile and its original normalizers
remain unchanged. The finite sums move from critical rank R to R+1.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierS3Weights

theorem addC2_injective : Function.Injective CriticalProfile.addC2 := by
  rintro ⟨a,v,d,e⟩ ⟨a',v',d',e'⟩ h
  simp_all [CriticalProfile.addC2]

theorem addC2_mem (R : ℕ) (p : CriticalProfile) (hp : p ∈ criticalProfiles R) :
    p.addC2 ∈ criticalProfiles (R+1) := by
  rw [mem_criticalProfiles, CriticalProfile.addC2_rank, (mem_criticalProfiles R p).mp hp]

/-- The shift is injective into, but need not exhaust, rank R+1. -/
def profileEmbedding (R : ℕ) : criticalProfiles R ↪ criticalProfiles (R+1) where
  toFun p := ⟨p.1.addC2, addC2_mem R p.1 p.2⟩
  inj' p q h := Subtype.ext (addC2_injective
    (congrArg (fun r : criticalProfiles (R+1) => r.1) h))

/-- Exact ratio including the original S3 normalizer and the factorial
of the additional original C2 occurrence. -/
theorem addC2_weight_ratio (p : CriticalProfile) :
    p.weight / 6 = (((p.c2+1 : ℕ) : ℚ) / 3) * p.addC2.weight := by
  let D : ℚ := (2 : ℚ)^p.c2 * (p.c2.factorial : ℚ) *
    24^p.v4 * (p.v4.factorial : ℚ) * 8^p.d8 * (p.d8.factorial : ℚ) *
    384^p.e8 * (p.e8.factorial : ℚ)
  have hD : D ≠ 0 := by dsimp only [D]; positivity
  have hc : ((p.c2+1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hbase : p.weight = 1/D := rfl
  have hnext : p.addC2.weight = 1/(2 * ((p.c2+1 : ℕ) : ℚ) * D) := by
    dsimp only [CriticalProfile.weight, CriticalProfile.addC2]
    rw [pow_succ, Nat.factorial_succ, Nat.cast_mul]
    dsimp only [D]
    congr 1
    ring
  rw [hbase, hnext]
  field_simp [hD, hc]
  <;> ring

theorem addC2_weight_ratio_real (p : CriticalProfile) :
    (p.weight : ℝ) / 6 = (((p.c2+1 : ℕ) : ℝ) / 3) * (p.addC2.weight : ℝ) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (addC2_weight_ratio p)
  simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using h

/-- Unused shifted profiles contribute nonnegative terms. No summand is
evaluated at rank R after its C2 coordinate has been added. -/
theorem sum_addC2_le (R : ℕ) (f : CriticalProfile → ℝ)
    (hf : ∀ p ∈ criticalProfiles (R+1), 0 ≤ f p) :
    (∑ p ∈ criticalProfiles R, f p.addC2) ≤
      ∑ p ∈ criticalProfiles (R+1), f p := by
  rw [← Finset.sum_image addC2_injective.injOn]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact addC2_mem R q hq
  · intro p hp _
    exact hf p hp

theorem sum_subtype_addC2_le (R : ℕ) (f : CriticalProfile → ℝ)
    (hf : ∀ p ∈ criticalProfiles (R+1), 0 ≤ f p) :
    (∑ p : criticalProfiles R, f p.1.addC2) ≤
      ∑ p : criticalProfiles (R+1), f p.1 := by
  have hleft : (∑ p : criticalProfiles R, f p.1.addC2) =
      ∑ p ∈ criticalProfiles R, f p.addC2 :=
    Finset.sum_coe_sort (criticalProfiles R) (fun p => f p.addC2)
  rw [hleft, Finset.sum_coe_sort (criticalProfiles (R+1)) f]
  exact sum_addC2_le R f hf

/-- The occurrence factor is at most (R+1)/3 on the original rank-R
profiles, before summing into the complete shifted rank. -/
theorem sum_addC2_coefficient_le (R : ℕ) (f : CriticalProfile → ℝ)
    (hf : ∀ p ∈ criticalProfiles (R+1), 0 ≤ f p) :
    (∑ p : criticalProfiles R, (((p.1.c2+1 : ℕ) : ℝ)/3) * f p.1.addC2) ≤
      (((R+1 : ℕ) : ℝ)/3) * ∑ p : criticalProfiles (R+1), f p.1 := by
  have hcoeff (p : criticalProfiles R) :
      (((p.1.c2+1 : ℕ) : ℝ)/3) ≤ (((R+1 : ℕ) : ℝ)/3) := by
    have hr := (mem_criticalProfiles R p.1).mp p.2
    have hc : p.1.c2+1 ≤ R+1 := by unfold CriticalProfile.rank at hr; omega
    exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by norm_num)
  calc
    _ ≤ ∑ p : criticalProfiles R, (((R+1 : ℕ) : ℝ)/3) * f p.1.addC2 :=
      Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_right (hcoeff p)
        (hf p.1.addC2 (addC2_mem R p.1 p.2)))
    _ = (((R+1 : ℕ) : ℝ)/3) * ∑ p : criticalProfiles R, f p.1.addC2 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_subtype_addC2_le R f hf) (by positivity)

theorem critical_s3_weight_sum_le (R : ℕ) (v : CriticalProfile → ℝ)
    (hv : ∀ p ∈ criticalProfiles (R+1), 0 ≤ v p) :
    (∑ p : criticalProfiles R, (p.1.weight : ℝ)/6 * v p.1.addC2) ≤
      (((R+1 : ℕ) : ℝ)/3) *
        ∑ p : criticalProfiles (R+1), (p.1.weight : ℝ) * v p.1 := by
  have h := sum_addC2_coefficient_le R (fun p => (p.weight : ℝ) * v p)
    (fun p hp => mul_nonneg (by exact_mod_cast p.weight_pos.le) (hv p hp))
  simpa only [addC2_weight_ratio_real, mul_assoc] using h

section OriginalMixedWeights

variable {ι : Type} [Fintype ι] (Ω : ι → Type)
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i)))

/-- Exact mixed-profile ratio. The same literal q occurs on both sides,
so every original carrier normalizer and occurrence factorial is retained. -/
theorem originalDenominator_s3_ratio (p : CriticalProfile) (q : ι → ℕ) (v : ℝ) :
    v / (6 * BinaryCarrierMixedProfile.originalDenominator Ω U p q) =
      (((p.c2+1 : ℕ) : ℝ)/3) *
        (v / BinaryCarrierMixedProfile.originalDenominator Ω U p.addC2 q) := by
  calc
    _ = (1 / BinaryCarrierMixedProfile.originalDenominator Ω U p q) / 6 * v := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = (p.weight : ℝ)/6 *
        (FiniteFactorialProfiles.weight (BinaryCarrierProfileWeights.normalizerOrder Ω U) q * v) := by
      rw [BinaryCarrierProfileWeights.originalDenominator_reciprocal]
      ring
    _ = (((p.c2+1 : ℕ) : ℝ)/3) *
        ((p.addC2.weight : ℝ) *
          FiniteFactorialProfiles.weight (BinaryCarrierProfileWeights.normalizerOrder Ω U) q * v) := by
      rw [addC2_weight_ratio_real]
      ring
    _ = _ := by
      rw [div_eq_mul_one_div v (BinaryCarrierMixedProfile.originalDenominator Ω U p.addC2 q),
        BinaryCarrierProfileWeights.originalDenominator_reciprocal]
      ring

private theorem denominator_nonneg (p : CriticalProfile) (q : ι → ℕ) :
    0 ≤ BinaryCarrierMixedProfile.originalDenominator Ω U p q := by
  unfold BinaryCarrierMixedProfile.originalDenominator
  positivity

/-- Reindex an arbitrary nonnegative actual value on the shifted model.
Only the critical profile changes, and the complete rank-(R+1) sum is
on the right. The finite set of original carrier profiles is unchanged. -/
theorem originalDenominator_s3_sum_le (R : ℕ) (S : Finset (ι → ℕ))
    (v : CriticalProfile → (ι → ℕ) → ℝ)
    (hv : ∀ p ∈ criticalProfiles (R+1), ∀ q ∈ S, 0 ≤ v p q) :
    (∑ p : criticalProfiles R, ∑ q ∈ S,
      v p.1.addC2 q / (6 * BinaryCarrierMixedProfile.originalDenominator Ω U p.1 q)) ≤
      (((R+1 : ℕ) : ℝ)/3) *
        ∑ p : criticalProfiles (R+1), ∑ q ∈ S,
          v p.1 q / BinaryCarrierMixedProfile.originalDenominator Ω U p.1 q := by
  have hterm (p : CriticalProfile) :
      (∑ q ∈ S, v p.addC2 q / (6 * BinaryCarrierMixedProfile.originalDenominator Ω U p q)) =
        (((p.c2+1 : ℕ) : ℝ)/3) *
          ∑ q ∈ S, v p.addC2 q / BinaryCarrierMixedProfile.originalDenominator Ω U p.addC2 q := by
    simp only [originalDenominator_s3_ratio, Finset.mul_sum]
  simp only [hterm]
  apply sum_addC2_coefficient_le R
    (fun p => ∑ q ∈ S, v p q / BinaryCarrierMixedProfile.originalDenominator Ω U p q)
  intro p hp
  exact Finset.sum_nonneg (fun q hq =>
    div_nonneg (hv p hp q hq) (denominator_nonneg Ω U p q))

/-- A larger full half-degree may replace R in the polynomial cost;
the shifted critical rank of the sum remains R+1. -/
theorem originalDenominator_s3_sum_le_of_rank_le (R N : ℕ) (hRN : R ≤ N)
    (S : Finset (ι → ℕ)) (v : CriticalProfile → (ι → ℕ) → ℝ)
    (hv : ∀ p ∈ criticalProfiles (R+1), ∀ q ∈ S, 0 ≤ v p q) :
    (∑ p : criticalProfiles R, ∑ q ∈ S,
      v p.1.addC2 q / (6 * BinaryCarrierMixedProfile.originalDenominator Ω U p.1 q)) ≤
      (((N+1 : ℕ) : ℝ)/3) *
        ∑ p : criticalProfiles (R+1), ∑ q ∈ S,
          v p.1 q / BinaryCarrierMixedProfile.originalDenominator Ω U p.1 q := by
  apply (originalDenominator_s3_sum_le Ω U R S v hv).trans
  apply mul_le_mul_of_nonneg_right
  · exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hRN 1)
      (by norm_num)
  · exact Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun q hq =>
      div_nonneg (hv p.1 p.2 q hq) (denominator_nonneg Ω U p.1 q)))

end OriginalMixedWeights
end SymmetricSubgroupAsymptotics.BinaryCarrierS3Weights
