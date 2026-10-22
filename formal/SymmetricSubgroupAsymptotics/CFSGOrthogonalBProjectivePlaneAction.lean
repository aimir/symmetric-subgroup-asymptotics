import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBProjectiveRootLines

/-! The actual centre-quotient automorphism group acts on the SAME
natural B two-plane orbit. Injectivity uses the proved odd-B centre
quotient equivalence; no general automorphism lifting premise occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBIntrinsicLongRoots
variable {K : Type} [Field K] [Finite K]

def projectiveLabel (h2 : (2 : K) ≠ 0) (s : ℕ) (P : Planes (K := K) s) :
    Subgroup (elementaryProjective K (s + 3)) :=
  projectiveConjugateRootLine h2 s (representative s P)

theorem projectiveLabel_plane (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g : elementaryRootGroup K (s + 3)) :
    projectiveLabel h2 s (plane s g) = projectiveConjugateRootLine h2 s g := by
  exact congrArg (fun H : Subgroup (elementaryRootGroup K (s + 3)) => H.map
    (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 3)))))
      (label_plane h2 s g)

theorem projectiveLabel_injective (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) :
    Function.Injective (projectiveLabel (K := K) h2 s) := by
  intro P Q he
  let e := oddProjectiveEquiv K p h2 (s + 2)
  change (label h2 s P).map e.toMonoidHom = (label h2 s Q).map e.toMonoidHom at he
  exact label_injective h2 s ((Subgroup.map_injective (f := e.toMonoidHom) e.injective) he)

theorem projective_stable (p : ℕ) [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) (s : ℕ)
    (f : MulAut (elementaryProjective K (s + 3))) (P : Planes (K := K) s) :
    ∃ Q, projectiveLabel h2 s Q = (projectiveLabel h2 s P).map f.toMonoidHom := by
  obtain ⟨h, he⟩ := automorphism_maps_projectiveConjugateRootLine p h2 s f (representative s P)
  exact ⟨plane s h, (projectiveLabel_plane h2 s h).trans he.symm⟩

def projectiveActionHom (p : ℕ) [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) (s : ℕ) :
    MulAut (elementaryProjective K (s + 3)) →* Equiv.Perm (Planes (K := K) s) :=
  CFSGSubgroupFamilyAction.permutationHom (MonoidHom.id _) (projectiveLabel h2 s)
    (projectiveLabel_injective p h2 s) (projective_stable p h2 s)

theorem projectiveLabel_action (p : ℕ) [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) (s : ℕ)
    (f : MulAut (elementaryProjective K (s + 3))) (P : Planes (K := K) s) :
    projectiveLabel h2 s (projectiveActionHom p h2 s f P) =
      (projectiveLabel h2 s P).map f.toMonoidHom :=
  CFSGSubgroupFamilyAction.label_permutation (MonoidHom.id _) (projectiveLabel h2 s)
    (projectiveLabel_injective p h2 s) (projective_stable p h2 s) f P

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
