import SymmetricSubgroupAsymptotics.CFSGGTwoAmbientSylowFlag
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDFourPartialFlagUpper
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBorelSoluble
import SymmetricSubgroupAsymptotics.CFSGGTwoPositivePGroup

/-! Actual G2 p-subgroup normalizers are soluble when the subgroup
contains the two positive simple root groups. Ambient Sylow alignment,
singular flag recovery and actual D4 component parity supply the proof. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoSylowNormalizer
open CFSGGTwoSerreMatrices CFSGGTwoPositivePGroup CFSGGTwoD4Inclusion
open CFSGGTwoSingularPrefix CFSGGTwoPrefixGeometry CFSGGTwoAmbientSylowFlag
open CFSGOrthogonalDIndexPositiveSpace CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexBundledQuadratic
variable (K : Type) [Field K] [Finite K]

def positiveSubgroup : Subgroup (naturalGroup K) :=
  (rootGroup K false).subgroupOf (naturalGroup K)

theorem root_mem_positive (i : Fin 2) (t : K) :
    naturalRoot K false i t ∈ positiveSubgroup K :=
  Subgroup.subset_closure ⟨(i, t), rfl⟩

theorem normalizer_triangular (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : Subgroup (naturalGroup K)) (hP : IsPGroup p P)
    (hUP : positiveSubgroup K ≤ P) (g : naturalGroup K)
    (hg : g ∈ Subgroup.normalizer (P : Set (naturalGroup K))) :
    (g.val : Mat K).BlockTriangular (flagEquiv 4) := by
  let f := naturalIntoD4 K
  let ρ := (naturalLinearHom K 4).comp f
  let T : Set (naturalGroup K) := Set.range (fun i : Fin 2 => naturalRoot K false i 1)
  have hT : ∀ i, testRoot K i ∈ P.map f := by
    intro i
    exact ⟨naturalRoot K false i 1, hUP (root_mem_positive K i 1), rfl⟩
  have hfixed := pSubgroup_fixed_prefix K p (P.map f) (hP.map f) hT
  have hrecover : ∀ k, k < 3 → ∀ v, splitQuadraticForm K 4 v = 0 →
      (∀ t ∈ T, ρ t v - v ∈ positivePrefix K k) → v ∈ positivePrefix K (k + 1) := by
    intro k hk v hv ht
    apply prefix_succ_of_singular_fixed K k (by omega) v hv
    · exact ht (naturalRoot K false 0 1) ⟨0, rfl⟩
    · exact ht (naturalRoot K false 1 1) ⟨1, rfl⟩
  have hpres := CFSGQuadraticFlagNormalizer.preserves_flag ρ (splitQuadraticForm K 4)
    (positivePrefix K) 3 (prefix_zero K)
    (fun a v => natural_preserves_Q K a v) (prefix_singular K) P T
    (by rintro _ ⟨i, rfl⟩; exact hUP (root_mem_positive K i 1))
    (fun k hk a ha v hv => hfixed k hk (f a) ⟨a, ha, rfl⟩ v hv) hrecover g hg
  exact CFSGOrthogonalDFourPartialFlagUpper.triangular K (f g) hpres

theorem normalizer_soluble (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : Subgroup (naturalGroup K)) (hP : IsPGroup p P)
    (hUP : positiveSubgroup K ≤ P) :
    IsSolvable (Subgroup.normalizer (P : Set (naturalGroup K))) := by
  let N := Subgroup.normalizer (P : Set (naturalGroup K))
  letI : IsSolvable (borel K 4) := borel_soluble K 4
  let f : N →* borel K 4 :=
    { toFun := fun g => ⟨naturalIntoD4 K g.val,
        normalizer_triangular K p P hP hUP g.val g.property⟩
      map_one' := Subtype.ext rfl
      map_mul' _ _ := Subtype.ext rfl }
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply naturalIntoD4_injective K
    exact congrArg (fun z : borel K 4 => z.val) he
  exact solvable_of_solvable_injective (f := f) hf

end SymmetricSubgroupAsymptotics.CFSGGTwoSylowNormalizer
