import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalUpperNormalizer
import SymmetricSubgroupAsymptotics.CFSGSurjectiveMinimalOvergroups

/-! The same original G2 positive Sylow normalizer has exactly two
minimal strict overgroups. Their Bool labels remain unordered: no
root-length preservation is asserted in characteristic three. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalMinimalParabolics
open CFSGGTwoD4GeckOriginalProjection CFSGGTwoD4GeckOriginalUpperNormalizer
open CFSGTrialityGeckGeneratedParabolics CFSGSurjectiveMinimalOvergroups
open CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] [IsSimpleGroup (Projective CartanMatrix.G₂ K)]

theorem original_upper_lt_simpleParabolic (p : ℕ) [Fact p.Prime] [CharP K p] (a : Bool) :
    Subgroup.normalizer (originalPositiveSylow K p : Set (Projective CartanMatrix.G₂ K)) <
      originalSimpleParabolic K a := by
  have hh := map_lt_map_of_kernel_le (generatedToOriginal K)
    (original_kernel_le_upperGenerated K)
    (upperGenerated_lt_parabolicGenerated K (RingEquiv.refl K) a)
  rwa [upperGenerated_map_original K p] at hh

theorem original_simpleParabolic_minimal (p : ℕ) [Fact p.Prime] [CharP K p] (a : Bool)
    (H : Subgroup (Projective CartanMatrix.G₂ K))
    (hBH : Subgroup.normalizer
      (originalPositiveSylow K p : Set (Projective CartanMatrix.G₂ K)) < H)
    (hHP : H ≤ originalSimpleParabolic K a) : H = originalSimpleParabolic K a := by
  have hh := map_minimal_overgroup (generatedToOriginal K) (generatedToOriginal_surjective K)
    (original_kernel_le_upperGenerated K)
    (upperGenerated_lt_parabolicGenerated K (RingEquiv.refl K) a)
    (parabolicGenerated_minimal K (RingEquiv.refl K) a)
  rw [upperGenerated_map_original K p] at hh
  exact hh H hBH hHP

theorem original_minimal_overgroup_eq_simpleParabolic (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : Subgroup (Projective CartanMatrix.G₂ K))
    (hBH : Subgroup.normalizer
      (originalPositiveSylow K p : Set (Projective CartanMatrix.G₂ K)) < H)
    (hmin : ∀ M : Subgroup (Projective CartanMatrix.G₂ K),
      Subgroup.normalizer (originalPositiveSylow K p : Set (Projective CartanMatrix.G₂ K)) < M →
      M ≤ H → M = H) : ∃ a : Bool, H = originalSimpleParabolic K a := by
  apply minimal_overgroup_family_surjective (generatedToOriginal K) (generatedToOriginal_surjective K)
    (original_kernel_le_upperGenerated K) (parabolicGenerated K (RingEquiv.refl K))
  · intro M hBM hminimal
    obtain ⟨a, ha⟩ := exists_parabolicGenerated_le K (RingEquiv.refl K) M hBM
    exact ⟨a, (hminimal _ (upperGenerated_lt_parabolicGenerated K (RingEquiv.refl K) a) ha).symm⟩
  · rwa [upperGenerated_map_original K p]
  · simpa only [upperGenerated_map_original K p] using hmin

theorem originalSimpleParabolic_injective : Function.Injective (originalSimpleParabolic K) :=
  map_family_injective (generatedToOriginal K) (original_kernel_le_upperGenerated K)
    (parabolicGenerated K (RingEquiv.refl K))
    (fun a => (upperGenerated_lt_parabolicGenerated K (RingEquiv.refl K) a).le)
    (parabolicGenerated_injective K (RingEquiv.refl K))

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalMinimalParabolics
