import SymmetricSubgroupAsymptotics.CFSGProjectiveFrameAlignment
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-! The literal general-linear point action descends through its actual
scalar centre to PGL. The linear map constructed by frame alignment
therefore supplies an actual PGL element with those frame images. -/
set_option autoImplicit false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization Matrix
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveLinearPointAction
open CFSGProjectiveFrameCoordinates CFSGProjectiveFrameAlignment
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

def linearEquiv : Matrix.GeneralLinearGroup n F ≃* ((n → F) ≃ₗ[F] (n → F)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (n → F))

def generalLinearPointHom : Matrix.GeneralLinearGroup n F →*
    Equiv.Perm (Points (F := F) (n := n)) :=
  (MulAction.toPermHom ((n → F) ≃ₗ[F] (n → F)) (Points (F := F) (n := n))).comp
    linearEquiv.toMonoidHom

theorem linearEquiv_scalar (u : Fˣ) (v : n → F) :
    linearEquiv (Matrix.GeneralLinearGroup.scalar n u) v = (u : F) • v := by
  change (Matrix.scalar n (u : F)) *ᵥ v = (u : F) • v
  ext i
  simp only [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]

theorem generalLinearPointHom_scalar :
    generalLinearPointHom.comp (Matrix.GeneralLinearGroup.scalar n :
      Fˣ →* Matrix.GeneralLinearGroup n F) = 1 := by
  apply MonoidHom.ext
  intro u
  apply Equiv.ext
  intro p
  change linearEquiv (Matrix.GeneralLinearGroup.scalar n u) • p = p
  rw [← Projectivization.mk_rep p, Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
  exact ⟨u, (linearEquiv_scalar u p.rep).symm⟩

def projectivePointHom : Matrix.ProjGenLinGroup n F →*
    Equiv.Perm (Points (F := F) (n := n)) :=
  Matrix.ProjGenLinGroup.lift generalLinearPointHom generalLinearPointHom_scalar

theorem projectivePointHom_mk (g : Matrix.GeneralLinearGroup n F)
    (p : Points (F := F) (n := n)) :
    projectivePointHom (Matrix.ProjGenLinGroup.mk g) p = linearEquiv g • p := rfl

theorem projectivePointHom_of_linearEquiv (a : (n → F) ≃ₗ[F] (n → F))
    (p : Points (F := F) (n := n)) :
    projectivePointHom (Matrix.ProjGenLinGroup.mk (linearEquiv.symm a)) p = a • p := by
  rw [projectivePointHom_mk, linearEquiv.apply_symm_apply]

theorem exists_projective_frame_alignment (f : collineationGroup (F := F) (n := n)) (b : n) :
    ∃ a : Matrix.ProjGenLinGroup n F,
      (∀ i : n, projectivePointHom a (basisPoint i) = f.val (basisPoint i)) ∧
        projectivePointHom a (sumPoint b) = f.val (sumPoint b) := by
  obtain ⟨a, ha, hs⟩ := exists_frame_alignment f b
  refine ⟨Matrix.ProjGenLinGroup.mk (linearEquiv.symm a), ?_, ?_⟩
  · intro i
    rw [projectivePointHom_of_linearEquiv]
    exact ha i
  · rw [projectivePointHom_of_linearEquiv]
    exact hs

end SymmetricSubgroupAsymptotics.CFSGProjectiveLinearPointAction
