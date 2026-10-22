import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicRootLines
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBProjectiveEquiv

/-! Every actual projective automorphism preserves the literal image
of the SAME original long-root-subgroup family. The natural/projective
isomorphism is the actual centre quotient, not a lifting assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent
variable {K : Type} [Field K] [Finite K]

def projectiveConjugateRootLine (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g : elementaryRootGroup K (s + 3)) : Subgroup (elementaryProjective K (s + 3)) :=
  (conjugateRootLine h2 s g).map
    (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 3))))

theorem automorphism_maps_projectiveConjugateRootLine (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (f : MulAut (elementaryProjective K (s + 3)))
    (g : elementaryRootGroup K (s + 3)) :
    ∃ h : elementaryRootGroup K (s + 3),
      (projectiveConjugateRootLine h2 s g).map f.toMonoidHom =
        projectiveConjugateRootLine h2 s h := by
  let e := oddProjectiveEquiv K p h2 (s + 2)
  let fE : MulAut (elementaryRootGroup K (s + 3)) := e.trans (f.trans e.symm)
  obtain ⟨h, hh⟩ := automorphism_maps_conjugateRootLine p h2 s fE g
  refine ⟨h, ?_⟩
  change ((conjugateRootLine h2 s g).map e.toMonoidHom).map f.toMonoidHom =
    (conjugateRootLine h2 s h).map e.toMonoidHom
  have heq : f.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp fE.toMonoidHom := by
    ext x
    change f (e x) = e (e.symm (f (e x)))
    exact (e.apply_symm_apply _).symm
  calc
    ((conjugateRootLine h2 s g).map e.toMonoidHom).map f.toMonoidHom =
        ((conjugateRootLine h2 s g).map fE.toMonoidHom).map e.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map, heq]
    _ = (conjugateRootLine h2 s h).map e.toMonoidHom :=
      congrArg (fun H : Subgroup (elementaryRootGroup K (s + 3)) => H.map e.toMonoidHom) hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
