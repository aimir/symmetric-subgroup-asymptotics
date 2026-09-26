import SymmetricSubgroupAsymptotics.SingletonExtensionCharts
import SymmetricSubgroupAsymptotics.BinaryCarrierSingletonMixture
import SymmetricSubgroupAsymptotics.BinaryCarrierMixtureRelabel

/-! Every original singleton complement chart is included. Actual ambient
subgroups, rather than chart witnesses, are counted. Relabelling closure
is proved for the complete even mixture, so no naturality or count premise
is added here. The conclusion remains the singleton sector only.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierOddSingleton

abbrev Family (n : ℕ) :=
  SingletonExtension.AllChartsFamily (X := Fin (2*n+1))
    (fun H : BinaryCarrierMixtureCompletion.Family n => H.1)

private theorem value_closed (n : ℕ) (a : Equiv.Perm (Fin (2*n)))
    (H : BinaryCarrierMixtureCompletion.Family n) :
    ∃ H' : BinaryCarrierMixtureCompletion.Family n,
      H'.1 = H.1.map a.permCongrHom.toMonoidHom := by
  refine ⟨BinaryCarrierMixtureCompletion.relabelFamilyEquiv n a H, ?_⟩
  rfl

/-- Identity on the same physical subgroup, with all arbitrary-chart
witnesses replaced by the standard chart at its fixed point. -/
def familyEquiv (n : ℕ) : Family n ≃ BinaryCarrierSingletonMixture.Family n :=
  SingletonExtension.allChartsEquiv
    (fun x : Fin (2*n+1) => finSuccEquiv' x) finSuccEquiv'_at
    (fun H : BinaryCarrierMixtureCompletion.Family n => H.1) (value_closed n)

@[simp] theorem familyEquiv_val (n : ℕ) (K : Family n) :
    (familyEquiv n K).1 = K.1 := rfl

theorem card_le (n : ℕ) :
    Nat.card (Family n) ≤ (2*n+1) * Nat.card (BinaryCarrierMixtureCompletion.Family n) := by
  rw [Nat.card_congr (familyEquiv n)]
  exact BinaryCarrierSingletonMixture.card_le n

theorem has_fixed_point (n : ℕ) (K : Family n) :
    ∃ x : Fin (2*n+1), ∀ g ∈ K.1, g x = x :=
  BinaryCarrierSingletonMixture.has_fixed_point n (familyEquiv n K)

theorem card_div_benchmark_le (n : ℕ) :
    (Nat.card (Family n) : ℝ) / exactBenchmark (2*n+1) ≤
      (Nat.card (BinaryCarrierMixtureCompletion.Family n) : ℝ) / exactBenchmark (2*n) := by
  rw [Nat.card_congr (familyEquiv n)]
  exact BinaryCarrierSingletonMixture.card_div_benchmark_le n

/-- Odd singleton mixture decay at the unchanged half-degree rate, with
all original complement charts and physical labels already included. -/
theorem eventually_card_div_benchmark_le :
    ∀ᶠ n : ℕ in Filter.atTop,
      (Nat.card (Family n) : ℝ) / exactBenchmark (2*n+1) ≤
        (2 : ℝ)^(-(29/2980864)*(n : ℝ)) := by
  filter_upwards [BinaryCarrierMixtureCompletion.eventually_card_div_benchmark_le] with n hn
  exact (card_div_benchmark_le n).trans hn

end SymmetricSubgroupAsymptotics.BinaryCarrierOddSingleton
