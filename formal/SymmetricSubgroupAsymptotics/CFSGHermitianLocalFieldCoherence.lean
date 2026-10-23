import SymmetricSubgroupAsymptotics.CFSGHermitianSemilinearPiece
import SymmetricSubgroupAsymptotics.CFSGSemilinearEmbeddingFieldUniqueness

/-! The constructed representatives on literal isotropic subspaces
have the same field automorphism on every common plane. No global
semilinearity or connectedness assumption is used for this local step. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

theorem projectiveInside_mk_submodule (S : IsotropicSpace sigma H)
    (x : S.val) (hx : x ≠ 0) :
    (projectiveInside sigma H S (Projectivization.mk K x hx)).val.val =
      Submodule.span K {x.val} := by
  rw [projectiveInside_submodule]
  change (Submodule.span K {x}).map S.val.subtype = _
  rw [Submodule.map_span, Set.image_singleton]
  rfl

theorem semilinearPiece_fields_eq_of_common_plane
    (f : Equiv.Perm (SingularPoint sigma H))
    (S T : IsotropicSpace sigma H) (tau rho : K ≃+* K)
    (F : SemilinearPiece sigma H f S tau) (G : SemilinearPiece sigma H f T rho)
    (W : Submodule K (I → K)) (hW : Module.finrank K W = 2)
    (hWS : W ≤ S.val) (hWT : W ≤ T.val) : tau = rho := by
  let e : (Fin 2 → K) ≃ₗ[K] W := LinearEquiv.ofFinrankEq _ _ (by simp [hW])
  let a : (Fin 2 → K) →ₗ[K] S.val := (Submodule.inclusion hWS).comp e.toLinearMap
  let b : (Fin 2 → K) →ₗ[K] T.val := (Submodule.inclusion hWT).comp e.toLinearMap
  have ha : Function.Injective a := by
    intro x y h
    apply e.injective
    apply Subtype.ext
    exact congrArg (fun v : S.val => v.val) h
  have hb : Function.Injective b := by
    intro x y h
    apply e.injective
    apply Subtype.ext
    exact congrArg (fun v : T.val => v.val) h
  apply CFSGSemilinearRayRigidity.field_eq_of_embedding_rays tau rho
    (F.map.comp a) (G.map.comp b) (G.injective.comp hb) 0 1 (by decide)
  intro x hx
  have hax : a x ≠ 0 := fun hz => hx (ha (hz.trans a.map_zero.symm))
  have hbx : b x ≠ 0 := fun hz => hx (hb (hz.trans b.map_zero.symm))
  have hp : (projectiveInside sigma H S (Projectivization.mk K (a x) hax)).val =
      (projectiveInside sigma H T (Projectivization.mk K (b x) hbx)).val := by
    apply Subtype.ext
    rw [projectiveInside_mk_submodule, projectiveInside_mk_submodule]
    rfl
  have hF := F.ray (a x) hax
  have hG := G.ray (b x) hbx
  rw [hp] at hF
  have he : Submodule.span K {F.map (a x)} = Submodule.span K {G.map (b x)} := hF.trans hG.symm
  obtain ⟨c, hc⟩ := Submodule.span_singleton_eq_span_singleton.mp he.symm
  refine ⟨(c : K), Units.ne_zero c, ?_⟩
  simpa only [LinearMap.comp_apply, Units.smul_def] using hc.symm

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
