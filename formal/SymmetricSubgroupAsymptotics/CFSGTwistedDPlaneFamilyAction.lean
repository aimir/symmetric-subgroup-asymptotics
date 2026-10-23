import SymmetricSubgroupAsymptotics.CFSGTwistedDProjectivePlaneLabel
import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyPermutation

/-! Arbitrary automorphisms of the actual relative central quotient
permute all singular two-planes of its fixed-field quadratic space.
The action uses exact injective whole-root-subgroup labels, rather
than a presumed polar point action or a lift to the matrix group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPlaneFamilyAction
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedDProjectiveUnipotent CFSGTwistedDProjectiveRootFamily
open CFSGTwistedDSingularPlaneOrbit CFSGTwistedDProjectivePlaneLabel CFSGTwistedA2FixedField

abbrev SingularPlanes (s : ℕ) (q : CFSG.PrimePower) :=
  {P : Submodule (fixedField q) (fixedSpace (s + 2) q) //
    Module.finrank (fixedField q) P = 2 ∧ ∀ x ∈ P, fixedQuadraticForm (s + 2) q x = 0}

def representative (s : ℕ) (q : CFSG.PrimePower) (P : SingularPlanes s q) :
    relativeRootGroup (s + 2) q :=
  Classical.choose (exists_conjugateRootPlane_of_singular s q P.val P.property.1 P.property.2)

theorem representative_spec (s : ℕ) (q : CFSG.PrimePower) (P : SingularPlanes s q) :
    P.val = conjugateRootPlane s q (representative s q P) :=
  Classical.choose_spec (exists_conjugateRootPlane_of_singular s q P.val P.property.1 P.property.2)

def singularLabel (s : ℕ) (q : CFSG.PrimePower) (P : SingularPlanes s q) :
    Subgroup (Projective s q) :=
  projectiveConjugateRootLine s q (projection s q (representative s q P))

def singularPlane (s : ℕ) (q : CFSG.PrimePower) (g : relativeRootGroup (s + 2) q) :
    SingularPlanes s q :=
  ⟨conjugateRootPlane s q g, conjugateRootPlane_finrank s q g, conjugateRootPlane_singular s q g⟩

theorem singularLabel_plane (s : ℕ) (q : CFSG.PrimePower) (g : relativeRootGroup (s + 2) q) :
    singularLabel s q (singularPlane s q g) = projectiveConjugateRootLine s q (projection s q g) := by
  apply (projectiveConjugateRootLine_eq_iff_plane_eq s q _ g).mpr
  exact (representative_spec s q (singularPlane s q g)).symm

theorem singularLabel_injective (s : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (singularLabel s q) := by
  intro P Q he
  apply Subtype.ext
  have hp := (projectiveConjugateRootLine_eq_iff_plane_eq s q (representative s q P)
    (representative s q Q)).mp he
  exact (representative_spec s q P).trans (hp.trans (representative_spec s q Q).symm)

theorem singular_stable (s : ℕ) (q : CFSG.PrimePower)
    (f : MulAut (Projective s q)) (P : SingularPlanes s q) :
    ∃ Q, singularLabel s q Q = (singularLabel s q P).map f.toMonoidHom := by
  obtain ⟨h, he⟩ := automorphism_maps_projectiveConjugateRootLine s q f
    (projection s q (representative s q P))
  have hsurj : Function.Surjective (projection s q) := QuotientGroup.mk'_surjective _
  obtain ⟨g, hg⟩ := hsurj h
  refine ⟨singularPlane s q g, (singularLabel_plane s q g).trans ?_⟩
  rw [hg]
  exact he.symm

def singularActionHom (s : ℕ) (q : CFSG.PrimePower) :
    MulAut (Projective s q) →* Equiv.Perm (SingularPlanes s q) :=
  CFSGSubgroupFamilyPermutation.permutationHom (singularLabel s q)
    (singularLabel_injective s q) (singular_stable s q)

theorem singularLabel_action (s : ℕ) (q : CFSG.PrimePower)
    (f : MulAut (Projective s q)) (P : SingularPlanes s q) :
    singularLabel s q (singularActionHom s q f P) = (singularLabel s q P).map f.toMonoidHom :=
  CFSGSubgroupFamilyPermutation.label_permutation (singularLabel s q)
    (singularLabel_injective s q) (singular_stable s q) f P

end SymmetricSubgroupAsymptotics.CFSGTwistedDPlaneFamilyAction
