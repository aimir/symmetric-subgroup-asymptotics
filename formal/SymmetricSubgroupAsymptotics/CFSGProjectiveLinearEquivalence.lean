import SymmetricSubgroupAsymptotics.CFSGProjectiveFrameCoordinates
import Mathlib.LinearAlgebra.Pi

/-! Actual linear coordinate equivalences transport projective points
and their original ternary incidence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveFrameCoordinates
variable {F n m : Type*} [Field F]

def linearPointEquiv (L : (n→F)≃ₗ[F](m→F)) :
    Points (F:=F) (n:=n)≃Points (F:=F) (n:=m) where
  toFun := Projectivization.map L.toLinearMap L.injective
  invFun := Projectivization.map L.symm.toLinearMap L.symm.injective
  left_inv p := by
    induction p using Projectivization.ind with
    | h v hv =>
      change Projectivization.mk F (L.symm (L v)) _=Projectivization.mk F v hv
      simp only [LinearEquiv.symm_apply_apply]
  right_inv p := by
    induction p using Projectivization.ind with
    | h v hv =>
      change Projectivization.mk F (L (L.symm v)) _=Projectivization.mk F v hv
      simp only [LinearEquiv.apply_symm_apply]

theorem linearPointEquiv_mk (L : (n→F)≃ₗ[F](m→F)) (v : n→F) (hv : v≠0) :
    linearPointEquiv L (Projectivization.mk F v hv)=
      Projectivization.mk F (L v) (by
        intro he
        exact hv (L.injective (he.trans L.map_zero.symm))) := rfl

theorem linearPointEquiv_submodule (L : (n→F)≃ₗ[F](m→F))
    (p : Points (F:=F) (n:=n)) :
    (linearPointEquiv L p).submodule=p.submodule.map L.toLinearMap := by
  induction p using Projectivization.ind with
  | h v hv =>
    change F ∙ (L v)=(F ∙ v).map L.toLinearMap
    rw [Submodule.map_span,Set.image_singleton]
    rfl

theorem onLine_linearPointEquiv (L : (n→F)≃ₗ[F](m→F))
    (p q r : Points (F:=F) (n:=n)) :
    OnLine (linearPointEquiv L p) (linearPointEquiv L q) (linearPointEquiv L r)↔OnLine p q r := by
  unfold OnLine
  rw [linearPointEquiv_submodule,linearPointEquiv_submodule,linearPointEquiv_submodule,
    ←Submodule.map_sup]
  exact Submodule.map_le_map_iff_of_injective L.injective _ _

end SymmetricSubgroupAsymptotics.CFSGProjectiveFrameCoordinates
