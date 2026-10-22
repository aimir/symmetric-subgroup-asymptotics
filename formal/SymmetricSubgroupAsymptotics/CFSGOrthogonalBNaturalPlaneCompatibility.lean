import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPointAction
import SymmetricSubgroupAsymptotics.CFSGSingularSubspaceIsometry

/-! The original group-automorphism action agrees on singular planes
with the SAME natural matrix action for inner automorphisms. This is
proved through the literal root-line labels, without lifting arbitrary
projective automorphisms. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent
open CFSGOrthogonalBIntrinsicLongRoots CFSGOrthogonalBSingularVectorCount
variable {K : Type} [Field K] [Finite K]

def naturalProjection (s : ℕ) : elementaryRootGroup K (s+3) →* elementaryProjective K (s+3) :=
  QuotientGroup.mk' (Subgroup.center _)

def orbitSingularPlane (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g : elementaryRootGroup K (s+3)) : SingularPlanes (K:=K) s :=
  (singularPlaneEquiv h2 s).symm (plane s g)

theorem singularLabel_orbit (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g : elementaryRootGroup K (s+3)) :
    singularLabel h2 s (orbitSingularPlane h2 s g)=projectiveConjugateRootLine h2 s g := by
  change projectiveLabel h2 s ((singularPlaneEquiv h2 s)
    ((singularPlaneEquiv h2 s).symm (plane s g)))=_
  rw [(singularPlaneEquiv h2 s).apply_symm_apply,projectiveLabel_plane]

theorem singularLabel_inner_orbit (h2 : (2 : K) ≠ 0) (s : ℕ)
    (g h : elementaryRootGroup K (s+3)) :
    singularLabel h2 s (orbitSingularPlane h2 s (g*h))=
      (singularLabel h2 s (orbitSingularPlane h2 s h)).map
        (MulAut.conj (naturalProjection s g)).toMonoidHom := by
  rw [singularLabel_orbit,singularLabel_orbit]
  change ((highestRootLine h2 s).map (MulAut.conj (g*h)).toMonoidHom).map (naturalProjection s)=
    (((highestRootLine h2 s).map (MulAut.conj h).toMonoidHom).map (naturalProjection s)).map
      (MulAut.conj (naturalProjection s g)).toMonoidHom
  simp only [Subgroup.map_map]
  apply congrArg (fun k : elementaryRootGroup K (s+3) →* elementaryProjective K (s+3) =>
    (highestRootLine h2 s).map k)
  apply MonoidHom.ext
  intro x
  simp [MulAut.conj_apply,map_mul,mul_assoc]

theorem singularAction_inner_orbit (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (g h : elementaryRootGroup K (s+3)) :
    singularActionHom p h2 s
      (MulAut.conj (naturalProjection s g)) (orbitSingularPlane h2 s h)=
      orbitSingularPlane h2 s (g*h) := by
  apply singularLabel_injective p h2 s
  rw [singularLabel_action]
  exact (singularLabel_inner_orbit h2 s g h).symm

theorem singularAction_inner_map (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (g : elementaryRootGroup K (s+3))
    (P : SingularPlanes (K:=K) s) :
    (singularActionHom p h2 s
      (MulAut.conj (naturalProjection s g)) P).val=
      P.val.map (Matrix.mulVecLin (g.val : Mat K (s+3))) := by
  obtain ⟨h,hh⟩ := (singularPlaneEquiv h2 s P).property
  have he : P=orbitSingularPlane h2 s h := Subtype.ext hh
  rw [he,singularAction_inner_orbit]
  change (standardRootPlane (K:=K) s).map
    (Matrix.mulVecLin ((g*h).val : Mat K (s+3)))=
      ((standardRootPlane (K:=K) s).map (Matrix.mulVecLin (h.val : Mat K (s+3)))).map
        (Matrix.mulVecLin (g.val : Mat K (s+3)))
  change (standardRootPlane (K:=K) s).map
    (Matrix.mulVecLin ((g.val : Mat K (s+3))*(h.val : Mat K (s+3))))=_
  rw [Matrix.mulVecLin_mul,Submodule.map_comp]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
