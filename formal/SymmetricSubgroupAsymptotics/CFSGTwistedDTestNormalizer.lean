import SymmetricSubgroupAsymptotics.CFSGTwistedDAmbientSylowFlag
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDPartialFlagUpper
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBorelSoluble

/-! The normalizer of any actual defining-p subgroup containing the
chain/folded-fork tests is soluble. Genuine D component parity supplies
the final triangular step; no fixed-group recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDTestNormalizer
open CFSGOrthogonalDSerreMatrices CFSGTwistedDSingularPrefix
open CFSGTwistedDPartialFlagGeometry CFSGTwistedDAmbientSylowFlag
open CFSGOrthogonalDIndexPositiveSpace CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexBundledQuadratic
variable (K : Type) [Field K] [Finite K] (s : ℕ)

theorem normalizer_triangular (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : Subgroup (elementaryRootGroup K (s + 4))) (hP : IsPGroup p P)
    (hT : ∀ i, testRoot K s i ∈ P) (g : elementaryRootGroup K (s + 4))
    (hg : g ∈ Subgroup.normalizer (P : Set (elementaryRootGroup K (s + 4)))) :
    (g.val : Mat K (s + 4)).BlockTriangular (flagEquiv (s + 4)) := by
  let ρ := naturalLinearHom K (s + 4)
  have hfixed := pSubgroup_fixed_prefix K s p P hP hT
  have hrecover : ∀ k, k < s + 3 → ∀ v, splitQuadraticForm K (s + 4) v = 0 →
      (∀ t ∈ Set.range (testRoot K s), ρ t v - v ∈ positivePrefix K (s + 2) k) →
      v ∈ positivePrefix K (s + 2) (k + 1) := by
    intro k hk v hv ht
    apply prefix_succ_of_singular_fixed K (s + 2) k (by omega) v hv
    · intro i
      exact ht (testRoot K s (Sum.inl i)) ⟨Sum.inl i, rfl⟩
    · exact ht (testRoot K s (Sum.inr ())) ⟨Sum.inr (), rfl⟩
  have hpres := CFSGQuadraticFlagNormalizer.preserves_flag ρ
    (splitQuadraticForm K (s + 4)) (positivePrefix K (s + 2)) (s + 3)
    (prefix_zero K s) (fun a v => elementary_preserves_bundledQ K s a v)
    (prefix_singular K s) P (Set.range (testRoot K s))
    (by rintro _ ⟨i, rfl⟩; exact hT i) hfixed hrecover g hg
  exact CFSGOrthogonalDPartialFlagUpper.triangular K s g hpres

theorem normalizer_soluble (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : Subgroup (elementaryRootGroup K (s + 4))) (hP : IsPGroup p P)
    (hT : ∀ i, testRoot K s i ∈ P) :
    IsSolvable (Subgroup.normalizer (P : Set (elementaryRootGroup K (s + 4)))) := by
  let N := Subgroup.normalizer (P : Set (elementaryRootGroup K (s + 4)))
  letI : IsSolvable (borel K (s + 4)) := borel_soluble K (s + 4)
  let f : N →* borel K (s + 4) :=
    { toFun := fun g => ⟨g.val, normalizer_triangular K s p P hP hT g.val g.property⟩
      map_one' := Subtype.ext rfl
      map_mul' _ _ := Subtype.ext rfl }
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : borel K (s + 4) => z.val) he)
  exact solvable_of_solvable_injective (f := f) hf

end SymmetricSubgroupAsymptotics.CFSGTwistedDTestNormalizer
