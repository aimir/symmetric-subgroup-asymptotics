import SymmetricSubgroupAsymptotics.CFSGPolarLocalFieldCoherence
import SymmetricSubgroupAsymptotics.CFSGPolarSubspaceSemilinearRestriction

/-! The proved local projective decomposition yields genuine injective
semilinear representatives on the original singular subspaces. Their
ray equation is retained literally, so the overlap field-coherence
theorem applies to these constructed representatives. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
open CFSGSingularPlaneTriangle
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
local instance (s : K≃+*K) : RingHomInvPair s.toRingHom s.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv s
local instance (s : K≃+*K) : RingHomInvPair s.symm.toRingHom s.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm s

theorem coordinatePoint_original (B : LinearMap.BilinForm K V) (W : Subspaces B)
    (d : ℕ) (e : W.val≃ₗ[K](Fin d→K)) (p : ℙ K W.val) :
    (linearProjectiveEquiv e p).submodule.map (W.val.subtype.comp e.symm.toLinearMap)=
      (projectiveInside B W p).val.val := by
  rw [linearProjectiveEquiv_submodule,←Submodule.map_comp]
  have he : (W.val.subtype.comp e.symm.toLinearMap).comp e.toLinearMap=W.val.subtype := by
    ext x
    exact congrArg Subtype.val (e.symm_apply_apply x)
  rw [he,projectiveInside_submodule]

variable (B : LinearMap.BilinForm K V) (f : Points B≃Points B) (l : Planes B≃Planes B)
    (hinc : ∀P L,(f P).val ≤ (l L).val ↔ P.val ≤ L.val)
    (horth : ∀P Q,ZeroOn B (f P).val (f Q).val ↔ ZeroOn B P.val Q.val)

theorem coordinateRestriction_original (W : Subspaces B) (d : ℕ)
    (e : W.val≃ₗ[K](Fin d→K))
    (e' : (imageSubspace B f l hinc horth W).val≃ₗ[K](Fin d→K)) (p : ℙ K W.val) :
    ((coordinateRestriction B f l hinc horth W d e e').val (linearProjectiveEquiv e p)).submodule.map
      ((imageSubspace B f l hinc horth W).val.subtype.comp e'.symm.toLinearMap)=
        (f (projectiveInside B W p).val).val := by
  have he : linearProjectiveEquiv e.symm (linearProjectiveEquiv e p)=p :=
    (linearProjectiveEquiv e).symm_apply_apply p
  change (linearProjectiveEquiv e' (projectiveRestriction B f l hinc horth W
    (linearProjectiveEquiv e.symm (linearProjectiveEquiv e p)))).submodule.map _=_
  rw [he,coordinatePoint_original,projectiveRestriction_point]

include l hinc horth in
theorem exists_semilinearPiece [Finite K] (W : Subspaces B) (d : ℕ)
    (hd : Module.finrank K W.val=d+3) : ∃σ : K≃+*K,Nonempty (SemilinearPiece B f W σ) := by
  let W' := imageSubspace B f l hinc horth W
  let e : W.val≃ₗ[K](Fin (d+3)→K) := LinearEquiv.ofFinrankEq _ _ (by simp [hd])
  have hd' : Module.finrank K W'.val=d+3 := (imageSubspace_finrank B f l hinc horth W).trans hd
  let e' : W'.val≃ₗ[K](Fin (d+3)→K) := LinearEquiv.ofFinrankEq _ _ (by simp [hd'])
  obtain ⟨a,σ,ha⟩ := exists_coordinate_semilinear B f l hinc horth W d e e'
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
  have hleft := coordinateRestriction_original B f l hinc horth W (d+3) e e' p
  have hright : (CFSGProjectiveFrameCoordinates.linearPointEquiv a
      (CFSGProjectiveFieldAction.pointEquiv σ (linearProjectiveEquiv e p))).submodule.map L=
        Submodule.span K {R x} := by
    change (Submodule.span K {a (σ ∘ e x)}).map L=Submodule.span K {R x}
    rw [Submodule.map_span,Set.image_singleton]
    rfl
  have hp : (projectiveInside B W p).val=
      ray B x.val (fun h=>hx (Subtype.ext h)) (W.property x.val x.property x.val x.property) := by
    apply Subtype.ext
    rw [projectiveInside_submodule]
    change (Submodule.span K {x}).map W.val.subtype=Submodule.span K {x.val}
    rw [Submodule.map_span,Set.image_singleton]
    rfl
  exact hright.symm.trans (hh.symm.trans (hleft.trans (congrArg (fun Q : Points B=>(f Q).val) hp)))

end SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
