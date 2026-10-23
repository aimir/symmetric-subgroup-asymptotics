import SymmetricSubgroupAsymptotics.CFSGHermitianProjectiveRestriction

/-! Constructed semilinear representatives on actual isotropic
subspaces of dimension at least three. Their literal point-ray equation
is retained for subsequent overlap coherence; no global extension is
asserted here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
variable {K I : Type*} [Field K] [Fintype I]
local instance (tau : K ≃+* K) : RingHomInvPair tau.toRingHom tau.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv tau
local instance (tau : K ≃+* K) : RingHomInvPair tau.symm.toRingHom tau.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm tau

variable (sigma : K ≃+* K) (H : Matrix I I K)

structure SemilinearPiece (f : Equiv.Perm (SingularPoint sigma H))
    (S : IsotropicSpace sigma H) (tau : K ≃+* K) where
  map : S.val →ₛₗ[tau.toRingHom] (I → K)
  injective : Function.Injective map
  ray : ∀ x : S.val, ∀ hx : x ≠ 0,
    Submodule.span K {map x} = (f (projectiveInside sigma H S (Projectivization.mk K x hx)).val).val

open CFSGPolarSubspacePoints in
theorem coordinatePoint_original (S : IsotropicSpace sigma H) (d : ℕ)
    (e : S.val ≃ₗ[K] (Fin d → K)) (p : ℙ K S.val) :
    (linearProjectiveEquiv e p).submodule.map (S.val.subtype.comp e.symm.toLinearMap) =
      (projectiveInside sigma H S p).val.val := by
  rw [linearProjectiveEquiv_submodule, ← Submodule.map_comp]
  have he : (S.val.subtype.comp e.symm.toLinearMap).comp e.toLinearMap = S.val.subtype := by
    apply LinearMap.ext
    intro x
    exact congrArg Subtype.val (e.symm_apply_apply x)
  rw [he, projectiveInside_submodule]

variable [Finite K]
variable (hsep : ∀ S : IsotropicSpace sigma H, SeparatedByMaximal sigma H S.val)
variable (f : Equiv.Perm (SingularPoint sigma H)) (hf : PreservesOrthogonality sigma H f)

open CFSGPolarSubspacePoints in
theorem coordinateRestriction_original (S : IsotropicSpace sigma H) (d : ℕ)
    (e : S.val ≃ₗ[K] (Fin d → K))
    (e' : (isotropicSpaceImage sigma H f hf S).val ≃ₗ[K] (Fin d → K)) (p : ℙ K S.val) :
    ((coordinateRestriction sigma H hsep f hf S d e e').val (linearProjectiveEquiv e p)).submodule.map
      ((isotropicSpaceImage sigma H f hf S).val.subtype.comp e'.symm.toLinearMap) =
        (f (projectiveInside sigma H S p).val).val := by
  have he : linearProjectiveEquiv e.symm (linearProjectiveEquiv e p) = p :=
    (linearProjectiveEquiv e).symm_apply_apply p
  change (linearProjectiveEquiv e' (projectiveRestriction sigma H hsep f hf S
    (linearProjectiveEquiv e.symm (linearProjectiveEquiv e p)))).submodule.map _ = _
  rw [he, coordinatePoint_original, projectiveRestriction_point]

include hsep hf in
theorem exists_semilinearPiece (S : IsotropicSpace sigma H) (d : ℕ)
    (hd : Module.finrank K S.val = d + 3) :
    ∃ tau : K ≃+* K, Nonempty (SemilinearPiece sigma H f S tau) := by
  let S' := isotropicSpaceImage sigma H f hf S
  let e : S.val ≃ₗ[K] (Fin (d + 3) → K) := LinearEquiv.ofFinrankEq _ _ (by simp [hd])
  have hd' : Module.finrank K S'.val = d + 3 := (isotropicSpaceImage_finrank sigma H hsep f hf S).trans hd
  let e' : S'.val ≃ₗ[K] (Fin (d + 3) → K) := LinearEquiv.ofFinrankEq _ _ (by simp [hd'])
  obtain ⟨a, tau, ha⟩ := exists_coordinate_semilinear sigma H hsep f hf S d e e'
  let L : (Fin (d + 3) → K) →ₗ[K] (I → K) := S'.val.subtype.comp e'.symm.toLinearMap
  let C : S.val →ₛₗ[tau.toRingHom] (Fin (d + 3) → K) :=
    a.toLinearMap.comp ((CFSGProjectiveFieldAction.coordinateEquiv tau).toLinearMap.comp e.toLinearMap)
  let R : S.val →ₛₗ[tau.toRingHom] (I → K) := L.comp C
  have hL : Function.Injective L := S'.val.subtype_injective.comp e'.symm.injective
  have hC : Function.Injective C := a.injective.comp
    ((CFSGProjectiveFieldAction.coordinateEquiv tau).injective.comp e.injective)
  refine ⟨tau, ⟨⟨R, hL.comp hC, ?_⟩⟩⟩
  intro x hx
  let p : ℙ K S.val := Projectivization.mk K x hx
  have hh := congrArg (fun q : ℙ K (Fin (d + 3) → K) => q.submodule.map L)
    (ha (CFSGPolarSubspacePoints.linearProjectiveEquiv e p))
  have hleft := coordinateRestriction_original sigma H hsep f hf S (d + 3) e e' p
  have hright : (CFSGProjectiveFrameCoordinates.linearPointEquiv a
      (CFSGProjectiveFieldAction.pointEquiv tau (CFSGPolarSubspacePoints.linearProjectiveEquiv e p))).submodule.map L =
        Submodule.span K {R x} := by
    change (Submodule.span K {a (tau ∘ e x)}).map L = Submodule.span K {R x}
    rw [Submodule.map_span, Set.image_singleton]
    rfl
  exact hright.symm.trans (hh.symm.trans hleft)

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
