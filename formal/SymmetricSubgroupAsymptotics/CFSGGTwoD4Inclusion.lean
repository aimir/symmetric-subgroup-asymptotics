import SymmetricSubgroupAsymptotics.CFSGGTwoD4RootFactorization
import SymmetricSubgroupAsymptotics.CFSGGTwoImageRealization
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBundledQuadratic

/-! The SAME folded natural G2 group is an actual subgroup of the
literal elementary D4 group. This is root-word inclusion, not a
recognition theorem for either full orthogonal or exceptional groups. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4Inclusion
open CFSGGTwoSerreMatrices CFSGGTwoD4RootFactorization

theorem root_mem_D4 (K : Type) [Field K] (negRoot : Bool) (i : Fin 2) (t : K) :
    rootTransvection K negRoot i t ∈ CFSGOrthogonalDSerreMatrices.elementaryRootGroup K 4 := by
  have hm (neg : Bool) (j : Fin 4) :
      CFSGOrthogonalDSerreMatrices.rootTransvection K 4 neg j t ∈
        CFSGOrthogonalDSerreMatrices.elementaryRootGroup K 4 :=
    CFSGOrthogonalDSerreMatrices.rootTransvection_mem K 4 neg j t
  by_cases hi : i = 0
  · subst i
    cases negRoot
    · rw [positive_outer_factor]
      exact (CFSGOrthogonalDSerreMatrices.elementaryRootGroup K 4).mul_mem
        ((CFSGOrthogonalDSerreMatrices.elementaryRootGroup K 4).mul_mem (hm false 0) (hm false 2))
        (hm false 3)
    · rw [negative_outer_factor]
      exact (CFSGOrthogonalDSerreMatrices.elementaryRootGroup K 4).mul_mem
        ((CFSGOrthogonalDSerreMatrices.elementaryRootGroup K 4).mul_mem (hm true 3) (hm true 2))
        (hm true 0)
  · have hi1 : i = 1 := Fin.eq_one_of_ne_zero i hi
    subst i
    cases negRoot
    · rw [positive_central_factor]
      exact hm false 1
    · rw [negative_central_factor]
      exact hm true 1

theorem naturalGroup_le_D4 (K : Type) [Field K] :
    naturalGroup K ≤ CFSGOrthogonalDSerreMatrices.elementaryRootGroup K 4 := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨negRoot, i, t, rfl⟩
  exact root_mem_D4 K negRoot i t

def naturalIntoD4 (K : Type) [Field K] :
    naturalGroup K →* CFSGOrthogonalDSerreMatrices.elementaryRootGroup K 4 :=
  Subgroup.inclusion (naturalGroup_le_D4 K)

theorem naturalIntoD4_injective (K : Type) [Field K] :
    Function.Injective (naturalIntoD4 K) :=
  Subgroup.inclusion_injective (naturalGroup_le_D4 K)

theorem natural_preserves_Q (K : Type) [Field K] (g : naturalGroup K) (v : Index → K) :
    CFSGOrthogonalDIndexBundledQuadratic.splitQuadraticForm K 4
        ((g.val : Mat K) *ᵥ v) =
      CFSGOrthogonalDIndexBundledQuadratic.splitQuadraticForm K 4 v :=
  CFSGOrthogonalDIndexBundledQuadratic.elementary_preserves_bundledQ K 0
    (naturalIntoD4 K g) v

end SymmetricSubgroupAsymptotics.CFSGGTwoD4Inclusion
