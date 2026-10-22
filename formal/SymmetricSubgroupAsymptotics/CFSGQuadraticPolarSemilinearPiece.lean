import SymmetricSubgroupAsymptotics.CFSGQuadraticPolarFieldCoherence
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspaceSemilinearRestriction

/-! The proved local projective decomposition yields genuine injective
semilinear representatives on the original Q-singular subspaces. Their
ray equation is retained literally, so the overlap field-coherence
theorem applies to these constructed representatives. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
open CFSGPolarSubspacePoints (linearProjectiveEquiv linearProjectiveEquiv_submodule)
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
local instance (s : K≃+*K) : RingHomInvPair s.toRingHom s.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv s
local instance (s : K≃+*K) : RingHomInvPair s.symm.toRingHom s.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm s

theorem coordinatePoint_original (q : QuadraticForm K V) (W : Subspaces q)
    (d : ℕ) (e : W.val≃ₗ[K](Fin d→K)) (p : ℙ K W.val) :
    (linearProjectiveEquiv e p).submodule.map (W.val.subtype.comp e.symm.toLinearMap)=
      (projectiveInside q W p).val.val := by
  rw [linearProjectiveEquiv_submodule,←Submodule.map_comp]
  have he : (W.val.subtype.comp e.symm.toLinearMap).comp e.toLinearMap=W.val.subtype := by
    ext x
    exact congrArg Subtype.val (e.symm_apply_apply x)
  rw [he,projectiveInside_submodule]

variable (q : QuadraticForm K V) (f : Points q≃Points q) (l : Planes q≃Planes q)
    (hinc : ∀P L,(f P).val ≤ (l L).val ↔ P.val ≤ L.val)

theorem coordinateRestriction_original (W : Subspaces q) (d : ℕ)
    (e : W.val≃ₗ[K](Fin d→K))
    (e' : (imageSubspace q f l hinc W).val≃ₗ[K](Fin d→K)) (p : ℙ K W.val) :
    ((coordinateRestriction q f l hinc W d e e').val (linearProjectiveEquiv e p)).submodule.map
      ((imageSubspace q f l hinc W).val.subtype.comp e'.symm.toLinearMap)=
        (f (projectiveInside q W p).val).val := by
  have he : linearProjectiveEquiv e.symm (linearProjectiveEquiv e p)=p :=
    (linearProjectiveEquiv e).symm_apply_apply p
  change (linearProjectiveEquiv e' (projectiveRestriction q f l hinc W
    (linearProjectiveEquiv e.symm (linearProjectiveEquiv e p)))).submodule.map _=_
  rw [he,coordinatePoint_original,projectiveRestriction_point]

include l hinc in
theorem exists_semilinearPiece [Finite K] (W : Subspaces q) (d : ℕ)
    (hd : Module.finrank K W.val=d+3) : ∃σ : K≃+*K,Nonempty (SemilinearPiece q f W σ) := by
  let W' := imageSubspace q f l hinc W
  let e : W.val≃ₗ[K](Fin (d+3)→K) := LinearEquiv.ofFinrankEq _ _ (by simp [hd])
  have hd' : Module.finrank K W'.val=d+3 := (imageSubspace_finrank q f l hinc W).trans hd
  let e' : W'.val≃ₗ[K](Fin (d+3)→K) := LinearEquiv.ofFinrankEq _ _ (by simp [hd'])
  obtain ⟨a,σ,ha⟩ := exists_coordinate_semilinear q f l hinc W d e e'
  let L : (Fin (d+3)→K)→ₗ[K]V := W'.val.subtype.comp e'.symm.toLinearMap
  let C : W.val→ₛₗ[σ.toRingHom](Fin (d+3)→K) :=
    a.toLinearMap.comp ((CFSGProjectiveFieldAction.coordinateEquiv σ).toLinearMap.comp e.toLinearMap)
  let R : W.val→ₛₗ[σ.toRingHom]V := L.comp C
  have hL : Function.Injective L := W'.val.subtype_injective.comp e'.symm.injective
  have hC : Function.Injective C := a.injective.comp
    ((CFSGProjectiveFieldAction.coordinateEquiv σ).injective.comp e.injective)
  refine ⟨σ,⟨⟨R,hL.comp hC,?_⟩⟩⟩
  intro x hx
  let p : ℙ K W.val := Projectivization.mk K x hx
  have hh := congrArg (fun q : ℙ K (Fin (d+3)→K)=>q.submodule.map L)
    (ha (linearProjectiveEquiv e p))
  have hleft := coordinateRestriction_original q f l hinc W (d+3) e e' p
  have hright : (CFSGProjectiveFrameCoordinates.linearPointEquiv a
      (CFSGProjectiveFieldAction.pointEquiv σ (linearProjectiveEquiv e p))).submodule.map L=
        Submodule.span K {R x} := by
    change (Submodule.span K {a (σ ∘ e x)}).map L=Submodule.span K {R x}
    rw [Submodule.map_span,Set.image_singleton]
    rfl
  have hp : (projectiveInside q W p).val=
      ray q x.val (fun h=>hx (Subtype.ext h)) (W.property x.val x.property) := by
    apply Subtype.ext
    rw [projectiveInside_submodule]
    change (Submodule.span K {x}).map W.val.subtype=Submodule.span K {x.val}
    rw [Submodule.map_span,Set.image_singleton]
    rfl
  exact hright.symm.trans (hh.symm.trans (hleft.trans (congrArg (fun Q : Points q=>(f Q).val) hp)))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
