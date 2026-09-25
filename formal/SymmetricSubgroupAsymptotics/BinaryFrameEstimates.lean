import SymmetricSubgroupAsymptotics.BinaryFrameIncidence
import SymmetricSubgroupAsymptotics.GaussianEstimates

/-!
# Quantitative conversion from ordered maps to subspace incidences

The original ordered-injection count is bounded below uniformly by the
positive binary Euler product. No independence assumption is used for the
selected incidence family.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- Exact Euler-tail expression for the ordered-injection product. -/
theorem binary_injection_product_euler (R k : ℕ) (hk : k ≤ R) :
    ((∏ i : Fin k, (2 ^ R - 2 ^ (i : ℕ)) : ℕ) : ℝ) =
      (2 : ℝ) ^ (R * k) * ∏ i ∈ Finset.range k, eulerFactor (R - k + i) := by
  rw [Nat.cast_prod]
  have hcast (i : Fin k) : ((2 ^ R - 2 ^ (i : ℕ) : ℕ) : ℝ) =
      (2 : ℝ) ^ R - 2 ^ (i : ℕ) := by
    rw [Nat.cast_sub (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2)
      (le_trans i.isLt.le hk))]
    push_cast
    rfl
  simp only [hcast]
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ ↦ (2 : ℝ) ^ R - 2 ^ i) k,
    ← Finset.prod_range_reflect]
  calc
    _ = ∏ i ∈ Finset.range k, (2 : ℝ) ^ R * eulerFactor (R - k + i) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [eulerFactor_eq_inv_pow]
      have hp : (2 : ℝ) ^ R =
          2 ^ (k - 1 - i) * 2 ^ (R - k + i + 1) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hp]
      have hne : (2 : ℝ) ^ (R - k + i + 1) ≠ 0 := by positivity
      field_simp
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]

/-- Uniform positive lower bound on the literal ordered-injection count. -/
theorem binary_injection_product_lower (R k : ℕ) (hk : k ≤ R) :
    eulerProduct * (2 : ℝ) ^ (R * k) ≤
      ((∏ i : Fin k, (2 ^ R - 2 ^ (i : ℕ)) : ℕ) : ℝ) := by
  rw [binary_injection_product_euler R k hk]
  have hs : eulerPartialProduct R = eulerPartialProduct (R - k) *
      ∏ i ∈ Finset.range k, eulerFactor (R - k + i) := by
    unfold eulerPartialProduct
    conv_lhs => rw [← Nat.sub_add_cancel hk]
    exact Finset.prod_range_add eulerFactor (R - k) k
  have ht : 0 ≤ ∏ i ∈ Finset.range k, eulerFactor (R - k + i) :=
    Finset.prod_nonneg (fun i _ ↦ (eulerFactor_pos _).le)
  have h := (eulerProduct_le_partial R).trans (hs.le.trans
    (mul_le_of_le_one_left ht (eulerPartialProduct_le_one (R - k))))
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left h
    (show 0 ≤ (2 : ℝ) ^ (R * k) by positivity)

/-- Converting any ordered-incidence upper bound to a Gaussian subspace
bound retains its complete predicate on the actual range. -/
theorem binary_subspace_incidence_le_gaussian {R k : ℕ} (hk : k ≤ R)
    (P : Submodule (ZMod 2) (Fin R → ZMod 2) → Prop) (A : ℝ)
    (hA : (Nat.card {f : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin R → ZMod 2) //
      Function.Injective f ∧ P f.range} : ℝ) ≤ A) :
    (Nat.card {S : Submodule (ZMod 2) (Fin R → ZMod 2) //
      Module.finrank (ZMod 2) S = k ∧ P S} : ℝ) ≤
      eulerProduct⁻¹ * (binaryGaussianCoefficient R k : ℝ) * A /
        (2 : ℝ) ^ (R * k) := by
  let N : ℕ := Nat.card {S : Submodule (ZMod 2) (Fin R → ZMod 2) //
    Module.finrank (ZMod 2) S = k ∧ P S}
  let T : ℕ := Nat.card {S : Submodule (ZMod 2) (Fin R → ZMod 2) //
    Module.finrank (ZMod 2) S = k}
  let L : ℕ := ∏ i : Fin k, (2 ^ k - 2 ^ (i : ℕ))
  let J : ℕ := ∏ i : Fin k, (2 ^ R - 2 ^ (i : ℕ))
  have hφ := euler_positive
  have hp : 0 < (2 : ℝ) ^ (R * k) := by positivity
  have hNL : (N : ℝ) * L ≤ A := by
    have he := congrArg (fun n : ℕ ↦ (n : ℝ)) (binary_subspace_incidence_count_mul k P)
    push_cast at he
    simpa only [N, L, Nat.cast_prod] using he.trans_le hA
  have hTJ : (T : ℝ) * L = J := by
    exact_mod_cast binary_rank_count_mul R k hk
  have hJ : eulerProduct * (2 : ℝ) ^ (R * k) ≤ (J : ℝ) :=
    binary_injection_product_lower R k hk
  have hT : (T : ℝ) = binaryGaussianCoefficient R k := by
    exact_mod_cast binary_rank_count_eq R k hk
  have hNA : (N : ℝ) * (eulerProduct * (2 : ℝ) ^ (R * k)) ≤ (T : ℝ) * A := by
    calc
      _ ≤ (N : ℝ) * J := mul_le_mul_of_nonneg_left hJ (by positivity)
      _ = (T : ℝ) * ((N : ℝ) * L) := by rw [← hTJ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hNL (by positivity)
  change (N : ℝ) ≤ _
  rw [← hT]
  apply (le_div_iff₀ hp).mpr
  apply (mul_le_mul_iff_right₀ hφ).mp
  calc
    _ = (N : ℝ) * (eulerProduct * (2 : ℝ) ^ (R * k)) := by ring
    _ ≤ (T : ℝ) * A := hNA
    _ = _ := by field_simp

end SymmetricSubgroupAsymptotics
