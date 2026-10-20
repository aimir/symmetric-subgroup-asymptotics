import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryBinaryCoordinates

/-!
# The three ternary translation spaces and their restricted binary actions

The paired space, augmentation space, and full space are fixed spaces of
explicit projections. Matrix identities are checked on four coordinate
columns, never by listing their vectors. The actual binary complement acts
on each space, giving the compact semidirect model and its faithful embedding
in the common signed affine group.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoFourTernaryCoreCoordinates

open TernarySignedBlockCoordinates
open PrimitiveAffineDegreeTwoFourTernaryCoordinates
open PrimitiveAffineDegreeTwoFourTernaryBinaryCoordinates

def pairedProjection : Vector →ₗ[Scalar] Vector :=
  LinearMap.pi ![LinearMap.proj 0, LinearMap.proj 1,
    LinearMap.proj 0, LinearMap.proj 1]

def augmentationProjection : Vector →ₗ[Scalar] Vector :=
  let a : Vector →ₗ[Scalar] Scalar := LinearMap.proj 0
  let b : Vector →ₗ[Scalar] Scalar := LinearMap.proj 1
  let c : Vector →ₗ[Scalar] Scalar := LinearMap.proj 2
  LinearMap.pi ![a, b, c, -(a + b + c)]

def projection : Fin 8 → Vector →ₗ[Scalar] Vector :=
  ![pairedProjection, pairedProjection, augmentationProjection,
    LinearMap.id, LinearMap.id, LinearMap.id, LinearMap.id, LinearMap.id]

theorem projection_idempotent (r : Fin 8) :
    (projection r).comp (projection r) = projection r := by
  apply LinearMap.pi_ext
  intro i c
  funext j
  fin_cases r <;> revert i c j <;> decide +kernel

def Core (r : Fin 8) : Submodule Scalar Vector where
  carrier := fun v => projection r v = v
  zero_mem' := map_zero _
  add_mem' := by
    intro v w hv hw
    change projection r (v + w) = v + w
    rw [map_add, hv, hw]
  smul_mem' := by
    intro c v hv
    change projection r (c • v) = c • v
    rw [map_smul, hv]

theorem projection_mem (r : Fin 8) (v : Vector) : projection r v ∈ Core r :=
  congrArg (fun f : Vector →ₗ[Scalar] Vector => f v) (projection_idempotent r)

theorem projection_first_two (r : Fin 8) (a b : Scalar) :
    projection r ![a, b, 0, 0] 0 = a ∧ projection r ![a, b, 0, 0] 1 = b := by
  fin_cases r <;> exact ⟨rfl, rfl⟩

def twoCoordinateEmbedding (r : Fin 8) (v : Scalar × Scalar) : Core r :=
  ⟨projection r ![v.1, v.2, 0, 0], projection_mem r _⟩

theorem twoCoordinateEmbedding_injective (r : Fin 8) :
    Function.Injective (twoCoordinateEmbedding r) := by
  intro a b he
  apply Prod.ext
  · have h := congrArg (fun v : Core r => v.val 0) he
    exact ((projection_first_two r a.1 a.2).1.symm.trans h).trans
      (projection_first_two r b.1 b.2).1
  · have h := congrArg (fun v : Core r => v.val 1) he
    exact ((projection_first_two r a.1 a.2).2.symm.trans h).trans
      (projection_first_two r b.1 b.2).2

theorem core_card_lower (r : Fin 8) : 9 ≤ Nat.card (Multiplicative (Core r)) := by
  have h := Nat.card_le_card_of_injective (twoCoordinateEmbedding r)
    (twoCoordinateEmbedding_injective r)
  have hc : Nat.card (Scalar × Scalar) = 9 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [hc] at h
  simpa only [Nat.card_congr Multiplicative.toAdd] using h

theorem core_exponent_three (r : Fin 8) (v : Multiplicative (Core r)) :
    v ^ (3 : ℕ) = 1 := by
  apply Multiplicative.toAdd.injective
  exact ZModModule.char_nsmul_eq_zero 3 v.toAdd

/-- The invariant-space calculation is an equality of four-column matrices. -/
theorem invariant_matrix (r : Fin 8) (q : Frame) (hq : q ∈ Complement r) :
    (projection r).comp ((linear (toSigned q)).toLinearMap.comp (projection r)) =
      (linear (toSigned q)).toLinearMap.comp (projection r) := by
  apply LinearMap.pi_ext
  intro i c
  funext j
  fin_cases r <;> revert q hq i c j <;> decide +kernel

theorem core_preserved (r : Fin 8) (q : Complement r) (v : Vector)
    (hv : v ∈ Core r) : linear (toSigned q.val) v ∈ Core r := by
  have h := congrArg (fun f : Vector →ₗ[Scalar] Vector => f v)
    (invariant_matrix r q.val q.property)
  change projection r v = v at hv
  change projection r (linear (toSigned q.val) v) = linear (toSigned q.val) v
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, hv] using h

def coreLinear (r : Fin 8) (q : Complement r) : Core r ≃ₗ[Scalar] Core r where
  toFun v := ⟨linear (toSigned q.val) v.val, core_preserved r q v.val v.property⟩
  invFun v := ⟨linear (toSigned (q⁻¹).val) v.val,
    core_preserved r q⁻¹ v.val v.property⟩
  left_inv v := by
    apply Subtype.ext
    change signedLinear (toSigned q.val⁻¹) (signedLinear (toSigned q.val) v.val) = v.val
    simp only [map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  right_inv v := by
    apply Subtype.ext
    change signedLinear (toSigned q.val) (signedLinear (toSigned q.val⁻¹) v.val) = v.val
    simp only [map_inv, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
  map_add' v w := Subtype.ext ((linear (toSigned q.val)).map_add v.val w.val)
  map_smul' c v := Subtype.ext ((linear (toSigned q.val)).map_smul c v.val)

def coreLinearHom (r : Fin 8) : Complement r →* (Core r ≃ₗ[Scalar] Core r) where
  toFun := coreLinear r
  map_one' := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    change signedLinear (toSigned 1) v.val = v.val
    rw [map_one, map_one]
    rfl
  map_mul' q p := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    change signedLinear (toSigned (q.val * p.val)) v.val =
      signedLinear (toSigned q.val) (signedLinear (toSigned p.val) v.val)
    rw [map_mul, map_mul]
    rfl

def coreAction (r : Fin 8) : Complement r →* MulAut (Multiplicative (Core r)) where
  toFun q := ((coreLinearHom r q).toAddEquiv).toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (coreLinearHom r 1 v.toAdd) = v
    rw [map_one]
    rfl
  map_mul' q p := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (coreLinearHom r (q * p) v.toAdd) =
      Multiplicative.ofAdd (coreLinearHom r q (coreLinearHom r p v.toAdd))
    rw [map_mul]
    rfl

abbrev Model (r : Fin 8) := Multiplicative (Core r) ⋊[coreAction r] Complement r

def coreInclusion (r : Fin 8) : Multiplicative (Core r) →* Multiplicative Vector :=
  (Core r).subtype.toAddMonoidHom.toMultiplicative

def complementInclusion (r : Fin 8) : Complement r →* Signed :=
  toSigned.comp (Complement r).subtype

def modelInclusion (r : Fin 8) : Model r →* Affine :=
  SemidirectProduct.map (coreInclusion r) (complementInclusion r) (by
    intro q
    rfl)

theorem modelInclusion_injective (r : Fin 8) : Function.Injective (modelInclusion r) := by
  intro g h he
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg (fun a : Affine => a.left.toAdd) he
  · apply Subtype.ext
    apply toSigned_injective
    exact congrArg (fun a : Affine => a.right) he

end PrimitiveAffineDegreeTwoFourTernaryCoreCoordinates
end SymmetricSubgroupAsymptotics

end
