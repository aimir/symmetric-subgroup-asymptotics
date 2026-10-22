import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularPlaneOrbit
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectivePlaneLabel
import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyPermutation

/-! Automorphisms of the ACTUAL projective D quotient permute ALL
original Q-singular two-planes, through their injective intrinsic root-
subgroup labels. No lift of an automorphism or triality classification
is assumed. Every witness stays in the original natural D group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneRootLine
open CFSGOrthogonalDIndexRootPlaneImage CFSGOrthogonalDIndexSingularRootPlanes
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexSingularPlaneOrbit
open CFSGOrthogonalDIndexProjectiveUnipotent CFSGOrthogonalDIndexProjectiveRootFamily
open CFSGOrthogonalDIndexProjectivePlaneLabel
variable (K : Type) [Field K]

abbrev SingularPlanes (s : ℕ) := {P : Submodule K (Index (s + 4) → K) //
  Module.finrank K P = 2 ∧ ∀ x ∈ P, splitQuadraticForm K (s + 4) x = 0}

def representative (s : ℕ) (P : SingularPlanes K s) : elementaryRootGroup K (s + 4) :=
  Classical.choose (exists_conjugateRootPlane_of_singular K s P.val P.property.1 P.property.2)

theorem representative_spec (s : ℕ) (P : SingularPlanes K s) :
    P.val = conjugateRootPlane K s (representative K s P) :=
  Classical.choose_spec (exists_conjugateRootPlane_of_singular K s P.val P.property.1 P.property.2)

def singularLabel (s : ℕ) (P : SingularPlanes K s) : Subgroup (elementaryProjective K (s + 4)) :=
  projectiveConjugateRootLine K s (projection K s (representative K s P))

def singularPlane (s : ℕ) (g : elementaryRootGroup K (s + 4)) : SingularPlanes K s :=
  ⟨conjugateRootPlane K s g, conjugateRootPlane_finrank K s g, conjugateRootPlane_singular K s g⟩

theorem singularLabel_plane (s : ℕ) (g : elementaryRootGroup K (s + 4)) :
    singularLabel K s (singularPlane K s g) = projectiveConjugateRootLine K s (projection K s g) := by
  apply (projectiveConjugateRootLine_eq_iff_plane_eq K s _ g).mpr
  exact (representative_spec K s (singularPlane K s g)).symm

theorem singularLabel_injective (s : ℕ) : Function.Injective (singularLabel K s) := by
  intro P Q he
  apply Subtype.ext
  have hp := (projectiveConjugateRootLine_eq_iff_plane_eq K s (representative K s P)
    (representative K s Q)).mp he
  exact (representative_spec K s P).trans (hp.trans (representative_spec K s Q).symm)

theorem singular_stable [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)
    (f : MulAut (elementaryProjective K (s + 4))) (P : SingularPlanes K s) :
    ∃ Q, singularLabel K s Q = (singularLabel K s P).map f.toMonoidHom := by
  obtain ⟨h, he⟩ := automorphism_maps_projectiveConjugateRootLine K p s f
    (projection K s (representative K s P))
  have hsurj : Function.Surjective (projection K s) := QuotientGroup.mk'_surjective _
  obtain ⟨g, hg⟩ := hsurj h
  refine ⟨singularPlane K s g, (singularLabel_plane K s g).trans ?_⟩
  rw [hg]
  exact he.symm

def singularActionHom [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ) :
    MulAut (elementaryProjective K (s + 4)) →* Equiv.Perm (SingularPlanes K s) :=
  CFSGSubgroupFamilyPermutation.permutationHom (singularLabel K s)
    (singularLabel_injective K s) (singular_stable K p s)

theorem singularLabel_action [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)
    (f : MulAut (elementaryProjective K (s + 4))) (P : SingularPlanes K s) :
    singularLabel K s (singularActionHom K p s f P) =
      (singularLabel K s P).map f.toMonoidHom :=
  CFSGSubgroupFamilyPermutation.label_permutation (singularLabel K s)
    (singularLabel_injective K s) (singular_stable K p s) f P

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
