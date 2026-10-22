import SymmetricSubgroupAsymptotics.CFSGTwistedDPartialFlagGeometry
import SymmetricSubgroupAsymptotics.CFSGPSubgroupConjugateSylow
import SymmetricSubgroupAsymptotics.CFSGQuadraticFlagConjugator
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSylow
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPrefixFixedSpace

/-! An actual ambient Sylow conjugator and the literal test matrices force
every defining-characteristic p-subgroup containing them to act trivially
on the SAME positive prefix quotients. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAmbientSylowFlag
open CFSGOrthogonalDSerreMatrices CFSGTwistedDSingularPrefix
open CFSGTwistedDPartialFlagGeometry CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexPositiveSpace CFSGOrthogonalDIndexBundledQuadratic
variable (K : Type) [Field K] (s : ℕ)

theorem pSubgroup_fixed_prefix [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : Subgroup (elementaryRootGroup K (s + 4))) (hP : IsPGroup p P)
    (hT : ∀ i, testRoot K s i ∈ P) :
    ∀ k, k < s + 3 → ∀ g ∈ P, ∀ v ∈ positivePrefix K (s + 2) (k + 1),
      ((g.val : Mat K (s + 4)) *ᵥ v) - v ∈ positivePrefix K (s + 2) k := by
  let ρ := naturalLinearHom K (s + 4)
  let U := unipotent K (s + 4)
  obtain ⟨a, ha⟩ := CFSGPSubgroupConjugateSylow.exists_conjugator P hP
    (CFSGOrthogonalDIndexSylow.unipotentSylow K s p)
  have hrecover : ∀ k, k < s + 3 → ∀ v, splitQuadraticForm K (s + 4) v = 0 →
      (∀ t ∈ Set.range (testRoot K s), ρ t v - v ∈ positivePrefix K (s + 2) k) →
      v ∈ positivePrefix K (s + 2) (k + 1) := by
    intro k hk v hv ht
    apply prefix_succ_of_singular_fixed K (s + 2) k (by omega) v hv
    · intro i
      exact ht (testRoot K s (Sum.inl i)) ⟨Sum.inl i, rfl⟩
    · exact ht (testRoot K s (Sum.inr ())) ⟨Sum.inr (), rfl⟩
  have hUfixed : ∀ k, k < s + 3 → ∀ u ∈ U,
      ∀ v ∈ positivePrefix K (s + 2) (k + 1),
      ρ u v - v ∈ positivePrefix K (s + 2) k := by
    intro k _ u hu v hv
    exact CFSGOrthogonalDIndexPrefixFixedSpace.prefix_succ_fixed K s k v hv ⟨u, hu⟩
  have hpres := CFSGQuadraticFlagConjugator.preserves_flag ρ
    (splitQuadraticForm K (s + 4)) (positivePrefix K (s + 2)) (basisVector K s) (s + 3)
    (prefix_zero K s) (prefix_span K s)
    (fun g v => elementary_preserves_bundledQ K s g v) (basis_singular K s)
    U (Set.range (testRoot K s)) a
    (by rintro _ ⟨i, rfl⟩; exact ha _ (hT i))
    (fun k hk u hu => hUfixed k hk u hu _ (basis_mem K s k hk)) hrecover
  have hmap : ∀ k, k ≤ s + 3 →
      (positivePrefix K (s + 2) k).map (ρ a).toLinearMap = positivePrefix K (s + 2) k := by
    intro k hk
    exact CFSGQuadraticFlagConjugator.map_eq_of_preserves (ρ a)
      (positivePrefix K (s + 2) k) (hpres k hk)
  intro k hk g hg v hv
  exact CFSGQuadraticFlagConjugator.fixed_on_flag_of_conjugate ρ
    (positivePrefix K (s + 2)) (s + 3) U a hmap hUfixed g (ha g hg) k hk v hv

end SymmetricSubgroupAsymptotics.CFSGTwistedDAmbientSylowFlag
