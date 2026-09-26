import SymmetricSubgroupAsymptotics.BinaryCarrierS3Physical
import SymmetricSubgroupAsymptotics.BinaryMixturePolynomialDecay

/-! Actual odd S3-marked subgroup unions over positive original
noncritical support. The contracted half-degree is R+2a+4T+1, so the
critical rank in a bin is n-(2a+4T+1). Parameter witnesses are forgotten;
no uniqueness or disjointness of their physical presentations is required.
A linear per-bin prefactor and quadratic number of bins are absorbed as
one cubic polynomial. No final decay estimate is assumed beyond the
explicit generic per-bin input. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierS3Union

open BinaryCarrierS3Physical

def bins (n : ℕ) (P : ℕ → ℕ → Prop) : Finset (ℕ × ℕ) :=
  ((Finset.range (n+1)) ×ˢ (Finset.range (n+1))).filter
    (fun b => 0 < 2*b.1+4*b.2 ∧ 2*b.1+4*b.2+1 ≤ n ∧ P b.1 b.2)

@[simp] theorem mem_bins (n a T : ℕ) (P : ℕ → ℕ → Prop) :
    (a,T) ∈ bins n P ↔ 0 < 2*a+4*T ∧ 2*a+4*T+1 ≤ n ∧ P a T := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, h⟩ <;>
      apply Finset.mem_range.mpr <;> omega

theorem bin_properties (n : ℕ) (P : ℕ → ℕ → Prop) (b : bins n P) :
    0 < 2*b.1.1+4*b.1.2 ∧ 2*b.1.1+4*b.1.2+1 ≤ n ∧ P b.1.1 b.1.2 :=
  (mem_bins n b.1.1 b.1.2 P).mp b.2

theorem bins_card_le (n : ℕ) (P : ℕ → ℕ → Prop) :
    Nat.card (bins n P) ≤ (n+1)^2 := by
  have h := Finset.card_le_card (Finset.filter_subset
    (fun b : ℕ × ℕ => 0 < 2*b.1+4*b.2 ∧ 2*b.1+4*b.2+1 ≤ n ∧ P b.1 b.2)
    ((Finset.range (n+1)) ×ˢ (Finset.range (n+1))))
  simpa only [bins, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_product, Finset.card_range, pow_two] using h

theorem bin_degree (n : ℕ) (P : ℕ → ℕ → Prop) (b : bins n P) :
    n-(2*b.1.1+4*b.1.2+1)+2*b.1.1+4*b.1.2+1 = n := by
  have h := (bin_properties n P b).2.1
  omega

/-- One fixed original point set. Bin/profile witnesses are existential
and are not counted as distinct physical subgroups. -/
abbrev Family (n : ℕ) (P : ℕ → ℕ → Prop) :=
  {H : Subgroup (Equiv.Perm (Fin (2*n+1))) //
    ∃ b : bins n P,
      ∃ K : PhysicalFamily (n-(2*b.1.1+4*b.1.2+1)) b.1.1 b.1.2 (Fin (2*n+1)), K.1=H}

private instance physicalFamilyFinite (R a T n : ℕ) :
    Finite (PhysicalFamily R a T (Fin (2*n+1))) := by
  unfold PhysicalFamily AssembledOrbitProfilesOn
  infer_instance

theorem card_le_sum (n : ℕ) (P : ℕ → ℕ → Prop) :
    Nat.card (Family n P) ≤ ∑ b : bins n P,
      Nat.card (PhysicalFamily (n-(2*b.1.1+4*b.1.2+1)) b.1.1 b.1.2 (Fin (2*n+1))) := by
  let f : (Σ b : bins n P,
      PhysicalFamily (n-(2*b.1.1+4*b.1.2+1)) b.1.1 b.1.2 (Fin (2*n+1))) → Family n P :=
    fun K => ⟨K.2.1, K.1, K.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨H, b, K, rfl⟩
    exact ⟨⟨b,K⟩, rfl⟩
  calc
    _ ≤ Nat.card (Σ b : bins n P,
        PhysicalFamily (n-(2*b.1.1+4*b.1.2+1)) b.1.1 b.1.2 (Fin (2*n+1))) :=
      Nat.card_le_card_of_surjective f hf
    _ = _ := Nat.card_sigma

/-- The odd benchmark lower bound retains the original physical factorial.
The full support and marker shift are subtracted before recovering rank. -/
theorem bin_card_div_benchmark_le_weightedSum
    (n : ℕ) (P : ℕ → ℕ → Prop) (b : bins n P) :
    (Nat.card (PhysicalFamily (n-(2*b.1.1+4*b.1.2+1)) b.1.1 b.1.2 (Fin (2*n+1))) : ℝ) /
      exactBenchmark (2*n+1) ≤
        weightedSum (n-(2*b.1.1+4*b.1.2+1)) b.1.1 b.1.2 /
          ((criticalCoefficient n : ℝ)*(binaryGaussianSum n : ℝ)) := by
  have h := card_div_benchmark_le_weightedSum
    (n-(2*b.1.1+4*b.1.2+1)) b.1.1 b.1.2
  simpa only [bin_degree n P b] using h

/-- A proved bound for each literal physical bin passes to their actual
union. No uniqueness of a profile or a parameter witness is assumed. -/
theorem card_div_benchmark_le_sum (n : ℕ) (P : ℕ → ℕ → Prop)
    (E : bins n P → ℝ)
    (hE : ∀ b : bins n P,
      (Nat.card (PhysicalFamily (n-(2*b.1.1+4*b.1.2+1)) b.1.1 b.1.2 (Fin (2*n+1))) : ℝ) /
        exactBenchmark (2*n+1) ≤ E b) :
    (Nat.card (Family n P) : ℝ) / exactBenchmark (2*n+1) ≤ ∑ b : bins n P, E b := by
  have hfirst : (Nat.card (Family n P) : ℝ) ≤
      ∑ b : bins n P,
        (Nat.card (PhysicalFamily (n-(2*b.1.1+4*b.1.2+1)) b.1.1 b.1.2 (Fin (2*n+1))) : ℝ) := by
    exact_mod_cast card_le_sum n P
  calc
    _ ≤ (∑ b : bins n P,
        (Nat.card (PhysicalFamily (n-(2*b.1.1+4*b.1.2+1)) b.1.1 b.1.2 (Fin (2*n+1))) : ℝ)) /
          exactBenchmark (2*n+1) :=
      div_le_div_of_nonneg_right hfirst (exactBenchmark_pos _).le
    _ = ∑ b : bins n P,
        (Nat.card (PhysicalFamily (n-(2*b.1.1+4*b.1.2+1)) b.1.1 b.1.2 (Fin (2*n+1))) : ℝ) /
          exactBenchmark (2*n+1) := Finset.sum_div _ _ _
    _ ≤ _ := Finset.sum_le_sum (fun b _ => hE b)

/-- Weighted-bin version: the actual original denominator is already in
weightedSum and is converted by the preceding exact physical adapter. -/
theorem card_div_benchmark_le_sum_of_weighted (n : ℕ) (P : ℕ → ℕ → Prop)
    (E : bins n P → ℝ)
    (hE : ∀ b : bins n P,
      weightedSum (n-(2*b.1.1+4*b.1.2+1)) b.1.1 b.1.2 /
        ((criticalCoefficient n : ℝ)*(binaryGaussianSum n : ℝ)) ≤ E b) :
    (Nat.card (Family n P) : ℝ) / exactBenchmark (2*n+1) ≤ ∑ b : bins n P, E b :=
  card_div_benchmark_le_sum n P E (fun b =>
    (bin_card_div_benchmark_le_weightedSum n P b).trans (hE b))

theorem card_div_benchmark_le_polynomial (n : ℕ) (P : ℕ → ℕ → Prop) (δ : ℝ)
    (hbin : ∀ b : bins n P,
      (Nat.card (PhysicalFamily (n-(2*b.1.1+4*b.1.2+1)) b.1.1 b.1.2 (Fin (2*n+1))) : ℝ) /
        exactBenchmark (2*n+1) ≤ ((n : ℝ)+1) * (2 : ℝ)^(-δ*(n : ℝ))) :
    (Nat.card (Family n P) : ℝ) / exactBenchmark (2*n+1) ≤
      ((n : ℝ)+1)^3 * (2 : ℝ)^(-δ*(n : ℝ)) := by
  calc
    _ ≤ ∑ _b : bins n P, ((n : ℝ)+1) * (2 : ℝ)^(-δ*(n : ℝ)) :=
      card_div_benchmark_le_sum n P _ hbin
    _ = (Nat.card (bins n P) : ℝ) * (((n : ℝ)+1) * (2 : ℝ)^(-δ*(n : ℝ))) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
    _ ≤ ((n : ℝ)+1)^2 * (((n : ℝ)+1) * (2 : ℝ)^(-δ*(n : ℝ))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast bins_card_le n P
    _ = _ := by ring

/-- Uniform proved per-bin bounds imply an exponential bound on the
complete literal union, with the polynomial bin cost actually absorbed. -/
theorem eventually_card_div_benchmark_le
    (P : ℕ → ℕ → ℕ → Prop) (δ : ℝ) (hδ : 0 < δ)
    (hbin : ∀ᶠ n : ℕ in Filter.atTop, ∀ b : bins n (P n),
      (Nat.card (PhysicalFamily (n-(2*b.1.1+4*b.1.2+1)) b.1.1 b.1.2 (Fin (2*n+1))) : ℝ) /
        exactBenchmark (2*n+1) ≤ ((n : ℝ)+1) * (2 : ℝ)^(-δ*(n : ℝ))) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (Nat.card (Family n (P n)) : ℝ) / exactBenchmark (2*n+1) ≤
        (2 : ℝ)^(-(δ/2)*(n : ℝ)) := by
  filter_upwards [hbin, BinaryMixtureNumerics.eventually_polynomial_bins_le 3 δ hδ]
    with n hlocal hpoly
  exact (card_div_benchmark_le_polynomial n (P n) δ hlocal).trans hpoly

/-- The same union theorem can consume the original weighted sums
directly; the final actual counting theorem still uses the physical union. -/
theorem eventually_card_div_benchmark_le_of_weighted
    (P : ℕ → ℕ → ℕ → Prop) (δ : ℝ) (hδ : 0 < δ)
    (hbin : ∀ᶠ n : ℕ in Filter.atTop, ∀ b : bins n (P n),
      weightedSum (n-(2*b.1.1+4*b.1.2+1)) b.1.1 b.1.2 /
        ((criticalCoefficient n : ℝ)*(binaryGaussianSum n : ℝ)) ≤
          ((n : ℝ)+1) * (2 : ℝ)^(-δ*(n : ℝ))) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (Nat.card (Family n (P n)) : ℝ) / exactBenchmark (2*n+1) ≤
        (2 : ℝ)^(-(δ/2)*(n : ℝ)) := by
  apply eventually_card_div_benchmark_le P δ hδ
  filter_upwards [hbin] with n hn
  intro b
  exact (bin_card_div_benchmark_le_weightedSum n (P n) b).trans (hn b)

end SymmetricSubgroupAsymptotics.BinaryCarrierS3Union
