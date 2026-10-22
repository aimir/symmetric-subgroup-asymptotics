import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneRootLineLabel
import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyAction

/-! Every actual automorphism acts on the original natural two-plane
orbit by its intrinsically recognized long-root subgroup labels. The
label is injective by the literal displacement-image correspondence.
No action on polar points or semilinear recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent CFSGOrthogonalBIntrinsicLongRoots
variable {K : Type} [Field K] [Finite K]

abbrev Planes (s : ℕ) := {P : Submodule K (Index (s + 3) → K) //
  ∃ g : elementaryRootGroup K (s + 3), P = conjugateRootPlane (K := K) s g}

def representative (s : ℕ) (P : Planes (K := K) s) : elementaryRootGroup K (s + 3) :=
  Classical.choose P.property

theorem representative_spec (s : ℕ) (P : Planes (K := K) s) :
    P.val = conjugateRootPlane (K := K) s (representative s P) :=
  Classical.choose_spec P.property

def label (h2 : (2 : K) ≠ 0) (s : ℕ) (P : Planes (K := K) s) :
    Subgroup (elementaryRootGroup K (s + 3)) :=
  conjugateRootLine h2 s (representative s P)

def plane (s : ℕ) (g : elementaryRootGroup K (s + 3)) : Planes (K := K) s :=
  ⟨conjugateRootPlane (K := K) s g, g, rfl⟩

theorem label_plane (h2 : (2 : K) ≠ 0) (s : ℕ) (g : elementaryRootGroup K (s + 3)) :
    label h2 s (plane s g) = conjugateRootLine h2 s g := by
  apply (conjugateRootLine_eq_iff_plane_eq h2 s _ g).mpr
  exact (representative_spec s (plane s g)).symm

theorem label_injective (h2 : (2 : K) ≠ 0) (s : ℕ) :
    Function.Injective (label (K := K) h2 s) := by
  intro P Q he
  apply Subtype.ext
  have hp := (conjugateRootLine_eq_iff_plane_eq h2 s (representative s P)
    (representative s Q)).mp he
  exact (representative_spec s P).trans (hp.trans (representative_spec s Q).symm)

theorem stable (p : ℕ) [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) (s : ℕ)
    (f : MulAut (elementaryRootGroup K (s + 3))) (P : Planes (K := K) s) :
    ∃ Q, label h2 s Q = (label h2 s P).map f.toMonoidHom := by
  obtain ⟨h, he⟩ := automorphism_maps_conjugateRootLine p h2 s f (representative s P)
  exact ⟨plane s h, (label_plane h2 s h).trans he.symm⟩

def actionHom (p : ℕ) [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) (s : ℕ) :
    MulAut (elementaryRootGroup K (s + 3)) →* Equiv.Perm (Planes (K := K) s) :=
  CFSGSubgroupFamilyAction.permutationHom (MonoidHom.id _) (label h2 s)
    (label_injective h2 s) (stable p h2 s)

theorem label_action (p : ℕ) [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) (s : ℕ)
    (f : MulAut (elementaryRootGroup K (s + 3))) (P : Planes (K := K) s) :
    label h2 s (actionHom p h2 s f P) = (label h2 s P).map f.toMonoidHom :=
  CFSGSubgroupFamilyAction.label_permutation (MonoidHom.id _) (label h2 s)
    (label_injective h2 s) (stable p h2 s) f P

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
