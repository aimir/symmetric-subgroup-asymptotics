import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
import SymmetricSubgroupAsymptotics.CFSGSemilinearEmbeddingFieldUniqueness

/-! Two semilinear representatives of the SAME quadratic singular-point map have
the same field component whenever their original Q-singular domains share
a two-dimensional subspace. The common plane and its images are literal
submodules; no global field-coherence hypothesis is supplied. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

structure SemilinearPiece (q : QuadraticForm K V) (f : Points q≃Points q)
    (W : Subspaces q) (σ : K≃+*K) where
  map : W.val→ₛₗ[σ.toRingHom]V
  injective : Function.Injective map
  point : ∀x : W.val,∀hx : x≠0,
    Submodule.span K {map x}=
      (f (ray q x.val (fun h=>hx (Subtype.ext h)) (W.property x.val x.property))).val

theorem fields_eq_of_common_plane (q : QuadraticForm K V) (f : Points q≃Points q)
    (W Z : Subspaces q) (σ τ : K≃+*K)
    (F : SemilinearPiece q f W σ) (G : SemilinearPiece q f Z τ)
    (T : Submodule K V) (hT : Module.finrank K T=2) (hTW : T≤W.val) (hTZ : T≤Z.val) : σ=τ := by
  let e : (Fin 2→K)≃ₗ[K]T := LinearEquiv.ofFinrankEq _ _ (by simp [hT])
  let a : (Fin 2→K)→ₗ[K]W.val := (Submodule.inclusion hTW).comp e.toLinearMap
  let b : (Fin 2→K)→ₗ[K]Z.val := (Submodule.inclusion hTZ).comp e.toLinearMap
  have ha : Function.Injective a := by
    intro x y h
    apply e.injective
    apply Subtype.ext
    exact congrArg (fun w : W.val=>w.val) h
  have hb : Function.Injective b := by
    intro x y h
    apply e.injective
    apply Subtype.ext
    exact congrArg (fun w : Z.val=>w.val) h
  apply CFSGSemilinearRayRigidity.field_eq_of_embedding_rays σ τ
    (F.map.comp a) (G.map.comp b) (G.injective.comp hb) 0 1 (by decide)
  intro x hx
  have hax : a x≠0 := by
    intro hz
    exact hx (ha (hz.trans a.map_zero.symm))
  have hbx : b x≠0 := by
    intro hz
    exact hx (hb (hz.trans b.map_zero.symm))
  have hF := F.point (a x) hax
  have hG := G.point (b x) hbx
  have he : Submodule.span K {F.map (a x)}=Submodule.span K {G.map (b x)} := hF.trans hG.symm
  obtain ⟨c,hc⟩ := Submodule.span_singleton_eq_span_singleton.mp he.symm
  refine ⟨(c : K),Units.ne_zero c,?_⟩
  simpa only [LinearMap.comp_apply,Units.smul_def] using hc.symm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
