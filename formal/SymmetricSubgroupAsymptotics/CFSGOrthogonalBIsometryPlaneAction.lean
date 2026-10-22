import SymmetricSubgroupAsymptotics.CFSGOrthogonalBAdjacencyActions
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBDisjointCommonNeighbours
import SymmetricSubgroupAsymptotics.CFSGCommonNeighbourRecognition

/-! Actual natural linear isometries permute the SAME singular planes
and their common neighbours. This uses only literal submodule images. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent CFSGOrthogonalBIntrinsicLongRoots
variable {K : Type} [Field K] [Finite K]

def isometryPlaneMap (s : ℕ) (e : (Index (s + 3) → K) ≃ₗ[K] (Index (s + 3) → K))
    (he : ∀ x y, (gram K (s + 3)).toBilin' (e x) (e y) = (gram K (s + 3)).toBilin' x y)
    (P : SingularPlanes (K := K) s) : SingularPlanes (K := K) s := by
  refine ⟨P.val.map e.toLinearMap, (e.finrank_map_eq P.val).trans P.property.1, ?_⟩
  rintro x ⟨x, hx, rfl⟩ y ⟨y, hy, rfl⟩
  exact (he x y).trans (P.property.2 x hx y hy)

theorem inverse_isometry_pairing (s : ℕ)
    (e : (Index (s + 3) → K) ≃ₗ[K] (Index (s + 3) → K))
    (he : ∀ x y, (gram K (s + 3)).toBilin' (e x) (e y) = (gram K (s + 3)).toBilin' x y)
    (x y : Index (s + 3) → K) :
    (gram K (s + 3)).toBilin' (e.symm x) (e.symm y) = (gram K (s + 3)).toBilin' x y := by
  simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm

private theorem image_inverse_image (s : ℕ)
    (e : (Index (s + 3) → K) ≃ₗ[K] (Index (s + 3) → K))
    (P : Submodule K (Index (s + 3) → K)) :
    (P.map e.toLinearMap).map e.symm.toLinearMap = P := by
  rw [← Submodule.map_comp]
  have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact e.symm_apply_apply x
  rw [h, Submodule.map_id]

def isometryPlaneEquiv (s : ℕ) (e : (Index (s + 3) → K) ≃ₗ[K] (Index (s + 3) → K))
    (he : ∀ x y, (gram K (s + 3)).toBilin' (e x) (e y) = (gram K (s + 3)).toBilin' x y) :
    SingularPlanes (K := K) s ≃ SingularPlanes (K := K) s where
  toFun := isometryPlaneMap s e he
  invFun := isometryPlaneMap s e.symm (inverse_isometry_pairing s e he)
  left_inv P := Subtype.ext (image_inverse_image s e P.val)
  right_inv P := Subtype.ext (image_inverse_image s e.symm P.val)

theorem isometryPlaneMap_adjacent (s : ℕ)
    (e : (Index (s + 3) → K) ≃ₗ[K] (Index (s + 3) → K))
    (he : ∀ x y, (gram K (s + 3)).toBilin' (e x) (e y) = (gram K (s + 3)).toBilin' x y)
    (P Q : SingularPlanes (K := K) s) (h : PlaneAdjacent s P.val Q.val) :
    PlaneAdjacent s (isometryPlaneMap s e he P).val (isometryPlaneMap s e he Q).val := by
  refine ⟨?_, ?_, ?_⟩
  · intro hPQ
    exact h.1 ((Submodule.map_injective_of_injective e.injective) hPQ)
  · have hd := e.finrank_map_eq (P.val ⊓ Q.val : Submodule K (Index (s + 3) → K))
    rw [Submodule.map_inf e.toLinearMap e.injective] at hd
    exact hd.trans h.2.1
  · change IsTotallySingular (K := K) s (P.val.map e.toLinearMap ⊔ Q.val.map e.toLinearMap)
    rw [← Submodule.map_sup]
    rintro x ⟨x, hx, rfl⟩ y ⟨y, hy, rfl⟩
    exact (he x y).trans (h.2.2 x hx y hy)

theorem isometryPlaneEquiv_adjacent_iff (s : ℕ)
    (e : (Index (s + 3) → K) ≃ₗ[K] (Index (s + 3) → K))
    (he : ∀ x y, (gram K (s + 3)).toBilin' (e x) (e y) = (gram K (s + 3)).toBilin' x y)
    (P Q : SingularPlanes (K := K) s) :
    PlaneAdjacent s (isometryPlaneEquiv s e he P).val (isometryPlaneEquiv s e he Q).val ↔
      PlaneAdjacent s P.val Q.val := by
  constructor
  · intro h
    have hh := isometryPlaneMap_adjacent s e.symm (inverse_isometry_pairing s e he) _ _ h
    change PlaneAdjacent s ((isometryPlaneEquiv s e he).symm (isometryPlaneEquiv s e he P)).val
      ((isometryPlaneEquiv s e he).symm (isometryPlaneEquiv s e he Q)).val at hh
    simpa only [Equiv.symm_apply_apply] using hh
  · exact isometryPlaneMap_adjacent s e he P Q

theorem isometry_common_neighbours_card (s : ℕ)
    (e : (Index (s + 3) → K) ≃ₗ[K] (Index (s + 3) → K))
    (he : ∀ x y, (gram K (s + 3)).toBilin' (e x) (e y) = (gram K (s + 3)).toBilin' x y)
    (P Q : SingularPlanes (K := K) s) :
    Nat.card (CommonNeighbours s (isometryPlaneEquiv s e he P) (isometryPlaneEquiv s e he Q)) =
      Nat.card (CommonNeighbours s P Q) :=
  CFSGCommonNeighbourRecognition.commonNeighbour_card
    (fun A B : SingularPlanes (K := K) s => PlaneAdjacent s A.val B.val)
    (isometryPlaneEquiv s e he) (isometryPlaneEquiv_adjacent_iff s e he) P Q

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
