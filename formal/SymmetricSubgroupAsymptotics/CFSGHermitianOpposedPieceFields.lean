import SymmetricSubgroupAsymptotics.CFSGHermitianCrossDuality
import SymmetricSubgroupAsymptotics.CFSGHermitianLocalFieldCoherence
import SymmetricSubgroupAsymptotics.CFSGHermitianPointFunctionals

/-! The constructed local semilinear pieces on two nondegenerately
paired singular planes have one field component. Their cross-zero
relation comes from the SAME point permutation, and the original
pairing constructs the required duality. No target duality or field
coherence is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization

namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]
local instance (tau : K ≃+* K) : RingHomInvPair tau.toRingHom tau.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv tau
local instance (tau : K ≃+* K) : RingHomInvPair tau.symm.toRingHom tau.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm tau

theorem semilinearPiece_cross_zero_iff (sigma : K ≃+* K) (H : Matrix I I K)
    (f : Equiv.Perm (SingularPoint sigma H)) (hf : PreservesOrthogonality sigma H f)
    (P Z : IsotropicSpace sigma H) (tauP tauZ : K ≃+* K)
    (F : SemilinearPiece sigma H f P tauP) (G : SemilinearPiece sigma H f Z tauZ)
    (x : P.val) (y : Z.val) :
    hermitianPair sigma H (F.map x) (G.map y) = 0 ↔ hermitianPair sigma H x.val y.val = 0 := by
  by_cases hx : x = 0
  · subst x
    simp only [map_zero, ZeroMemClass.coe_zero, pair_zero_left]
  by_cases hy : y = 0
  · subst y
    simp only [map_zero, ZeroMemClass.coe_zero, pair_zero_right]
  have hx0 : x.val ≠ 0 := fun h => hx (Subtype.ext h)
  have hy0 : y.val ≠ 0 := fun h => hy (Subtype.ext h)
  have hFx0 : F.map x ≠ 0 := fun h => hx (F.injective (h.trans F.map.map_zero.symm))
  have hGy0 : G.map y ≠ 0 := fun h => hy (G.injective (h.trans G.map.map_zero.symm))
  let R := (projectiveInside sigma H P (Projectivization.mk K x hx)).val
  let T := (projectiveInside sigma H Z (Projectivization.mk K y hy)).val
  have hxR : x.val ∈ R.val := by
    rw [projectiveInside_mk_submodule]
    exact Submodule.mem_span_singleton_self _
  have hyT : y.val ∈ T.val := by
    rw [projectiveInside_mk_submodule]
    exact Submodule.mem_span_singleton_self _
  have hFx : F.map x ∈ (f R).val := by
    rw [← F.ray x hx]
    exact Submodule.mem_span_singleton_self _
  have hGy : G.map y ∈ (f T).val := by
    rw [← G.ray y hy]
    exact Submodule.mem_span_singleton_self _
  exact (orthogonal_iff_singular_representatives sigma H (f R) (f T)
    (F.map x) (G.map y) hFx hGy hFx0 hGy0).symm.trans
      ((hf R T).trans (orthogonal_iff_singular_representatives sigma H R T
        x.val y.val hxR hyT hx0 hy0))

theorem semilinearPiece_fields_eq_of_opposed_planes [Finite K]
    (sigma : K ≃+* K) (H : Matrix I I K)
    (f : Equiv.Perm (SingularPoint sigma H)) (hf : PreservesOrthogonality sigma H f)
    (P Z : IsotropicSpace sigma H) (hP : Module.finrank K P.val = 2)
    (hZ : Module.finrank K Z.val = 2)
    (hND : ∀ x : P.val, (∀ y : Z.val, hermitianPair sigma H x.val y.val = 0) → x = 0)
    (tauP tauZ : K ≃+* K) (F : SemilinearPiece sigma H f P tauP)
    (G : SemilinearPiece sigma H f Z tauZ) (hcomm : Function.Commute sigma tauZ) :
    tauP = tauZ := by
  classical
  let eP : (Fin 2 → K) ≃ₗ[K] P.val := LinearEquiv.ofFinrankEq _ _ (by simp [hP])
  let eZ : (Fin 2 → K) ≃ₗ[K] Z.val := LinearEquiv.ofFinrankEq _ _ (by simp [hZ])
  let a : (Fin 2 → K) →ₗ[K] (I → K) := P.val.subtype.comp eP.toLinearMap
  let b : (Fin 2 → K) →ₗ[K] (I → K) := Z.val.subtype.comp eZ.toLinearMap
  have hNDc (v : Fin 2 → K) (hv : ∀ w, hermitianPair sigma H (a v) (b w) = 0) : v = 0 := by
    have hx : eP v = 0 := by
      apply hND
      intro y
      obtain ⟨w, rfl⟩ := eZ.surjective y
      exact hv w
    exact eP.injective (hx.trans eP.map_zero.symm)
  let D := CFSGHermitianCrossDuality.crossDuality sigma H a b hNDc
  apply CFSGHermitianCrossEmbeddingFieldCoherence.fields_eq_of_cross_zero_iff sigma tauP tauZ H D
    (CFSGHermitianCrossDuality.crossDuality_smul sigma H a b hNDc)
    (F.map.comp eP.toLinearMap) (G.map.comp eZ.toLinearMap) _ hcomm
    (0 : Fin 2) 1 (by decide)
  intro v w
  exact semilinearPiece_cross_zero_iff sigma H f hf P Z tauP tauZ F G (eP v) (eZ w)

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
