import SymmetricSubgroupAsymptotics.SingletonBenchmark
import SymmetricSubgroupAsymptotics.BinaryCarrierMixtureCompletion

/-! The literal singleton extensions of the proved even finite-alphabet
mixture, on Fin (2*n+1). At each labelled point the deletion chart is
`finSuccEquiv'`; arbitrary chart invariance is not a premise or conclusion.
This does not include S3 markers, all odd actions, or the global T1 remainder.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierSingletonMixture

/-- The actual odd subgroups, with point and even-family witnesses
forgotten. Original even subgroups retain all their profile conditions. -/
abbrev Family (n : ℕ) :=
  SingletonExtension.FinFamily (2*n)
    (fun H : BinaryCarrierMixtureCompletion.Family n => H.1)

private instance evenFamilyFinite (n : ℕ) : Finite (BinaryCarrierMixtureCompletion.Family n) := by
  unfold BinaryCarrierMixtureCompletion.Family BinaryCarrierParameterUnion.Family
  infer_instance

theorem card_le (n : ℕ) :
    Nat.card (Family n) ≤ (2*n+1) * Nat.card (BinaryCarrierMixtureCompletion.Family n) :=
  SingletonExtension.card_finFamily_le (2*n) _

theorem has_fixed_point (n : ℕ) (K : Family n) :
    ∃ x : Fin (2*n+1), ∀ g ∈ K.1, g x = x :=
  SingletonExtension.finFamily_has_fixed_point (2*n) _ K

theorem card_div_benchmark_le (n : ℕ) :
    (Nat.card (Family n) : ℝ) / exactBenchmark (2*n+1) ≤
      (Nat.card (BinaryCarrierMixtureCompletion.Family n) : ℝ) / exactBenchmark (2*n) :=
  singletonExtension_card_div_benchmark_le n _

/-- The same exponential rate in half-degree, now for actual singleton
extensions. No additional model count, profile weight, or normalizer is assumed. -/
theorem eventually_card_div_benchmark_le :
    ∀ᶠ n : ℕ in Filter.atTop,
      (Nat.card (Family n) : ℝ) / exactBenchmark (2*n+1) ≤
        (2 : ℝ)^(-(29/2980864)*(n : ℝ)) := by
  filter_upwards [BinaryCarrierMixtureCompletion.eventually_card_div_benchmark_le] with n hn
  exact (card_div_benchmark_le n).trans hn

end SymmetricSubgroupAsymptotics.BinaryCarrierSingletonMixture
