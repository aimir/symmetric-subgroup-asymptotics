import SymmetricSubgroupAsymptotics.CFSGHermitianSimilitudeLocalAction
import SymmetricSubgroupAsymptotics.CFSGHermitianPointFunctionals

/-! Agreement with a local linear piece up to one nonzero scalar gives
agreement on the actual singular points in its original domain. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization

namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGHermitianSimilitudeGroup
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem singularPointHom_eq_of_piece_scalar (sigma : K ≃+* K) (H : (Matrix I I K)ˣ)
    (f : Equiv.Perm (SingularPoint sigma (H : Matrix I I K)))
    (S : IsotropicSpace sigma (H : Matrix I I K))
    (F : SemilinearPiece sigma (H : Matrix I I K) f S (RingEquiv.refl K))
    (g : similitudes sigma H) (c : K) (hc : c ≠ 0)
    (hg : ∀ x : S.val, g.val x.val = c • F.map x)
    (R : SingularPoint sigma (H : Matrix I I K)) (hR : R.val ≤ S.val) :
    singularPointHom sigma H g R = f R := by
  obtain ⟨x,hx,hx0⟩ := singularPoint_nonzero sigma (H : Matrix I I K) R
  let v : S.val := ⟨x,hR hx⟩
  have hv : v ≠ 0 := fun h => hx0 (congrArg (fun z : S.val => z.val) h)
  have hray : R.val = K ∙ x := singularPoint_span sigma (H : Matrix I I K) R x hx hx0
  have hpoint : (projectiveInside sigma (H : Matrix I I K) S (Projectivization.mk K v hv)).val = R := by
    apply Subtype.ext
    exact (projectiveInside_mk_submodule sigma (H : Matrix I I K) S v hv).trans hray.symm
  have hF := F.ray v hv
  rw [hpoint] at hF
  apply Subtype.ext
  rw [singularPointHom_val,hray,Submodule.map_span,Set.image_singleton]
  change K ∙ g.val x = (f R).val
  rw [hg v,Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc)]
  exact hF

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
