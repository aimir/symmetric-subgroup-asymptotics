import SymmetricSubgroupAsymptotics.CFSGHermitianSimilitudePointAction
import SymmetricSubgroupAsymptotics.CFSGHermitianSemilinearPiece

/-! Constructed actual linear similitudes preserve original point
orthogonality and transport the SAME local semilinear representatives.
These are the explicit composition rules for ambient normalization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters CFSGHermitianSimilitudeGroup
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem hermitian_similitude_point_preserves_orthogonality (sigma : K ≃+* K)
    (H : (Matrix I I K)ˣ) (g : similitudes sigma H) :
    PreservesOrthogonality sigma (H : Matrix I I K) (singularPointHom sigma H g) := by
  intro P Q
  rw [singularPointHom_val,singularPointHom_val]
  constructor
  · intro h x hx y hy
    have he := h (g.val x) ⟨x,hx,rfl⟩ (g.val y) ⟨y,hy,rfl⟩
    rw [multiplier_spec] at he
    exact (mul_eq_zero.mp he).resolve_left (Units.ne_zero _)
  · rintro h x ⟨v,hv,rfl⟩ y ⟨w,hw,rfl⟩
    change hermitianPair sigma (H : Matrix I I K) (g.val v) (g.val w) = 0
    rw [multiplier_spec,h v hv w hw,mul_zero]

def hermitian_similitude_postcompose_piece (sigma : K ≃+* K) (H : (Matrix I I K)ˣ)
    (f : Equiv.Perm (SingularPoint sigma (H : Matrix I I K)))
    (S : IsotropicSpace sigma (H : Matrix I I K)) (tau : K ≃+* K)
    (g : similitudes sigma H) (F : SemilinearPiece sigma (H : Matrix I I K) f S tau) :
    SemilinearPiece sigma (H : Matrix I I K) (singularPointHom sigma H g * f) S tau where
  map := g.val.toLinearMap.comp F.map
  injective := g.val.injective.comp F.injective
  ray := by
    intro z hz
    let P := (projectiveInside sigma (H : Matrix I I K) S (Projectivization.mk K z hz)).val
    calc
      (K ∙ g.val (F.map z)) = (K ∙ F.map z).map g.val.toLinearMap := by
        rw [Submodule.map_span,Set.image_singleton]
        rfl
      _ = (f P).val.map g.val.toLinearMap :=
        congrArg (Submodule.map g.val.toLinearMap) (F.ray z hz)
      _ = (singularPointHom sigma H g (f P)).val := (singularPointHom_val sigma H g (f P)).symm

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
