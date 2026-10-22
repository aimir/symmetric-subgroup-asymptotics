import SymmetricSubgroupAsymptotics.CFSGGTwoD4Inclusion
import SymmetricSubgroupAsymptotics.CFSGGTwoPrefixGeometry
import SymmetricSubgroupAsymptotics.CFSGPSubgroupConjugateSylow
import SymmetricSubgroupAsymptotics.CFSGQuadraticFlagConjugator
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSylow
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPrefixFixedSpace

/-! Actual ambient Sylow containment, followed by singular flag recovery,
places EVERY p-subgroup containing the two G2 test roots on the SAME
standard flag. No choice of a standard Sylow is assumed to contain it. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoAmbientSylowFlag
open CFSGGTwoSerreMatrices CFSGGTwoD4Inclusion CFSGGTwoSingularPrefix
open CFSGGTwoPrefixGeometry CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexPositiveSpace CFSGOrthogonalDIndexBundledQuadratic
variable (K : Type) [Field K]

def testRoot (i : Fin 2) : CFSGOrthogonalDSerreMatrices.elementaryRootGroup K 4 :=
  ⟨rootTransvection K false i 1, root_mem_D4 K false i 1⟩

theorem pSubgroup_fixed_prefix [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : Subgroup (CFSGOrthogonalDSerreMatrices.elementaryRootGroup K 4))
    (hP : IsPGroup p P) (hT : ∀ i, testRoot K i ∈ P) :
    ∀ k, k < 3 → ∀ g ∈ P, ∀ v ∈ positivePrefix K (k + 1),
      ((g.val : Mat K) *ᵥ v) - v ∈ positivePrefix K k := by
  let ρ := naturalLinearHom K 4
  let U := unipotent K 4
  obtain ⟨a, ha⟩ := CFSGPSubgroupConjugateSylow.exists_conjugator P hP
    (CFSGOrthogonalDIndexSylow.unipotentSylow K 0 p)
  have hrecover : ∀ k, k < 3 → ∀ v, splitQuadraticForm K 4 v = 0 →
      (∀ t ∈ Set.range (testRoot K), ρ t v - v ∈ positivePrefix K k) →
      v ∈ positivePrefix K (k + 1) := by
    intro k hk v hv ht
    apply prefix_succ_of_singular_fixed K k (by omega) v hv
    · exact ht (testRoot K 0) ⟨0, rfl⟩
    · exact ht (testRoot K 1) ⟨1, rfl⟩
  have hUfixed : ∀ k, k < 3 → ∀ u ∈ U, ∀ v ∈ positivePrefix K (k + 1),
      ρ u v - v ∈ positivePrefix K k := by
    intro k _ u hu v hv
    exact CFSGOrthogonalDIndexPrefixFixedSpace.prefix_succ_fixed K 0 k v hv ⟨u, hu⟩
  have hpres := CFSGQuadraticFlagConjugator.preserves_flag ρ
    (splitQuadraticForm K 4) (positivePrefix K) (basisVector K) 3
    (prefix_zero K) (prefix_span K)
    (fun g v => elementary_preserves_bundledQ K 0 g v) (basis_singular K)
    U (Set.range (testRoot K)) a
    (by rintro _ ⟨i, rfl⟩; exact ha _ (hT i))
    (fun k hk u hu => hUfixed k hk u hu _ (basis_mem K k hk)) hrecover
  have hmap : ∀ k, k ≤ 3 → (positivePrefix K k).map (ρ a).toLinearMap =
      positivePrefix K k := by
    intro k hk
    exact CFSGQuadraticFlagConjugator.map_eq_of_preserves (ρ a)
      (positivePrefix K k) (hpres k hk)
  intro k hk g hg v hv
  exact CFSGQuadraticFlagConjugator.fixed_on_flag_of_conjugate ρ
    (positivePrefix K) 3 U a hmap hUfixed g (ha g hg) k hk v hv

end SymmetricSubgroupAsymptotics.CFSGGTwoAmbientSylowFlag
