import SymmetricSubgroupAsymptotics.BinaryCarrierSmallSupportPhysical

/-! The literal finite union over all positive small noncritical supports.
Different supports or original profile presentations may overlap; only
the forgetful surjection is used. The extra support-sum factor is included
in the proved scalar absorption, rather than left in the final estimate. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierAllSmallSupport

open BinaryCarrierSmallSupportPhysical

private theorem cutoff_le (n C : ℕ) (hC : 0<C)
    (hcut : (C : ℝ) ≤ Real.sqrt (n : ℝ)/4) : C ≤ n := by
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hs : (4*(C : ℝ))^2 ≤ (Real.sqrt (n : ℝ))^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  rw [Real.sq_sqrt (Nat.cast_nonneg n)] at hs
  have hm := mul_nonneg (sub_nonneg.mpr hC1) (Nat.cast_nonneg (α := ℝ) C)
  have hn : (C : ℝ) ≤ n := by nlinarith
  exact_mod_cast hn

def supports (n : ℕ) : Finset ℕ :=
  (Finset.range (n+1)).filter (fun C => 0<C ∧ (C : ℝ) ≤ Real.sqrt (n : ℝ)/4)

@[simp] theorem mem_supports (n C : ℕ) :
    C ∈ supports n ↔ 0<C ∧ (C : ℝ) ≤ Real.sqrt (n : ℝ)/4 := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.lt_succ_of_le (cutoff_le n C h.1 h.2)), h⟩

theorem support_le (n : ℕ) (C : supports n) : C.1 ≤ n :=
  cutoff_le n C.1 ((mem_supports n C.1).mp C.2).1
    ((mem_supports n C.1).mp C.2).2

theorem supports_card_le (n : ℕ) : Nat.card (supports n) ≤ n+1 := by
  have h := Finset.card_le_card (Finset.filter_subset
    (fun C : ℕ => 0<C ∧ (C : ℝ) ≤ Real.sqrt (n : ℝ)/4) (Finset.range (n+1)))
  simpa only [supports, Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_range] using h

/-- A subtype of actual subgroups on the single original labelled set.
Support and profile witnesses are forgotten, not counted as new subgroups. -/
abbrev Family (n : ℕ) :=
  {H : Subgroup (Equiv.Perm (Fin (2*n))) //
    ∃ C : supports n, ∃ K : PhysicalFamily (n-C.1) C.1 (Fin (2*n)), K.1=H}

private instance physicalFamilyFinite (R C n : ℕ) :
    Finite (PhysicalFamily R C (Fin (2*n))) := by
  unfold PhysicalFamily AssembledOrbitProfilesOn
  infer_instance

theorem card_le_sum (n : ℕ) :
    Nat.card (Family n) ≤ ∑ C : supports n,
      Nat.card (PhysicalFamily (n-C.1) C.1 (Fin (2*n))) := by
  let f : (Σ C : supports n, PhysicalFamily (n-C.1) C.1 (Fin (2*n))) → Family n :=
    fun K => ⟨K.2.1, K.1, K.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨H, C, K, rfl⟩
    exact ⟨⟨C,K⟩, rfl⟩
  calc
    _ ≤ Nat.card (Σ C : supports n, PhysicalFamily (n-C.1) C.1 (Fin (2*n))) :=
      Nat.card_le_card_of_surjective f hf
    _ = _ := Nat.card_sigma

/-- Complete all-small-support physical union, normalized by the exact
benchmark. This conclusion is only for the stated original finite alphabet. -/
theorem eventually_card_div_benchmark_le :
    ∀ᶠ n : ℕ in Filter.atTop,
      (Nat.card (Family n) : ℝ) / exactBenchmark (2*n) ≤ (2 : ℝ)^(-(n : ℝ)/4) := by
  let A : ℝ := Real.exp 13 * 4 * (eulerProduct⁻¹)^6
  have hA : 0 < A := by dsimp [A]; positivity [euler_positive]
  filter_upwards [BinaryMixtureNumerics.eventually_small_support_prefactor_bound A hA 5]
    with n hn
  have hn1 : (0 : ℝ) < (n : ℝ)+1 := by positivity
  have hlocal (C : supports n) :
      (Nat.card (PhysicalFamily (n-C.1) C.1 (Fin (2*n))) : ℝ) / exactBenchmark (2*n) ≤
        (2 : ℝ)^(-(n : ℝ)/4) / ((n : ℝ)+1) := by
    have hC := (mem_supports n C.1).mp C.2
    have hsum : n-C.1+C.1=n := Nat.sub_add_cancel (support_le n C)
    have hreal : ((n-C.1 : ℕ) : ℝ)+(C.1 : ℝ)=(n : ℝ) := by exact_mod_cast hsum
    have hp := card_div_benchmark_le (n-C.1) C.1 hC.1
    have hm := mul_le_mul_of_nonneg_left hp hn1.le
    have hbound : ((n : ℝ)+1) *
        ((Nat.card (PhysicalFamily (n-C.1) C.1 (Fin (2*n))) : ℝ) /
          exactBenchmark (2*n)) ≤ (2 : ℝ)^(-(n : ℝ)/4) := by
      calc
        _ ≤ ((n : ℝ)+1) * (Real.exp 13 * (2 * (n : ℝ))^C.1 *
            BinaryCarrierSmallSupportNormalized.bound (n-C.1) C.1) := by
          simpa only [hsum] using hm
        _ = A * ((n : ℝ)+1)^5 * (2*(n : ℝ))^C.1 *
            (2 : ℝ)^(-(n : ℝ)/2+1/2+(211/192)*(C.1 : ℝ)^2+(14/3)*C.1+49/3) := by
          simp only [BinaryCarrierSmallSupportNormalized.bound, hreal]
          dsimp [A]
          ring
        _ ≤ _ := hn C.1 hC.2
    apply (le_div_iff₀ hn1).mpr
    simpa only [mul_comm] using hbound
  have hfirst : (Nat.card (Family n) : ℝ) ≤
      ∑ C : supports n, (Nat.card (PhysicalFamily (n-C.1) C.1 (Fin (2*n))) : ℝ) := by
    exact_mod_cast card_le_sum n
  calc
    _ ≤ (∑ C : supports n,
        (Nat.card (PhysicalFamily (n-C.1) C.1 (Fin (2*n))) : ℝ)) / exactBenchmark (2*n) :=
      div_le_div_of_nonneg_right hfirst (exactBenchmark_pos _).le
    _ = ∑ C : supports n,
        (Nat.card (PhysicalFamily (n-C.1) C.1 (Fin (2*n))) : ℝ) / exactBenchmark (2*n) :=
      Finset.sum_div _ _ _
    _ ≤ ∑ _C : supports n, (2 : ℝ)^(-(n : ℝ)/4) / ((n : ℝ)+1) :=
      Finset.sum_le_sum fun C _ => hlocal C
    _ = (Nat.card (supports n) : ℝ) * ((2 : ℝ)^(-(n : ℝ)/4) / ((n : ℝ)+1)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
    _ ≤ ((n : ℝ)+1) * ((2 : ℝ)^(-(n : ℝ)/4) / ((n : ℝ)+1)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast supports_card_le n
    _ = _ := by field_simp [hn1.ne']

end SymmetricSubgroupAsymptotics.BinaryCarrierAllSmallSupport
