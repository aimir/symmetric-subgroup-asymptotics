import SymmetricSubgroupAsymptotics.CFSGOrthogonalBNormalizedCommonNeighbours
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIsometryPlaneAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneIntersectionPartition
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBTangentCount
import SymmetricSubgroupAsymptotics.CFSGTwoDimensionalCompanion

/-! Every actual R11 pair is put into the normalized common-neighbour
frame by an actual original elementary-group word. Only its two shared
singular vectors are normalized; the other companion is kept arbitrary. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBR11FrameNormalization
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent CFSGOrthogonalBIntrinsicLongRoots
open CFSGOrthogonalBPlaneFamilyAction CFSGOrthogonalBVectorCoordinates
open CFSGOrthogonalBSingularVectorCount CFSGPolarCommonPointPlanes
open CFSGOrthogonalBNormalizedCommonNeighbours
variable {K : Type} [Field K] [Finite K]

theorem exists_normalized_frame (h2 : (2 : K) ≠ 0) (s : ℕ)
    (P Q : SingularPlanes (K := K) s) (h : IntersectingNonadjacent s P Q) :
    ∃ (e : (Index (s + 3) → K) ≃ₗ[K] (Index (s + 3) → K))
      (he : ∀ x y, (gram K (s + 3)).toBilin' (e x) (e y) = (gram K (s + 3)).toBilin' x y)
      (w : Index (s + 3) → K)
      (hw : (gram K (s + 3)).toBilin' w w = 0)
      (hwu : (gram K (s + 3)).toBilin' w (firstVector s) = 0)
      (hc : (gram K (s + 3)).toBilin' w (secondVector s) ≠ 0),
      isometryPlaneEquiv s e he P = firstPlane s ∧
        isometryPlaneEquiv s e he Q = secondPlane s w hw hwu hc := by
  have hnon : (P.val ⊓ Q.val : Submodule K (Index (s + 3) → K)) ≠ ⊥ :=
    Submodule.one_le_finrank_iff.mp (by rw [h.1])
  obtain ⟨u, huPQ, hu⟩ := (P.val ⊓ Q.val).ne_bot_iff.mp hnon
  obtain ⟨v, hvP, hvnot, hPspan⟩ := CFSGTwoDimensionalSubmoduleBasis.exists_companion
    P.val P.property.1 u huPQ.1 hu
  obtain ⟨w, hwQ, hwnot, hQspan⟩ := CFSGTwoDimensionalSubmoduleBasis.exists_companion
    Q.val Q.property.1 u huPQ.2 hu
  have hcross : (gram K (s + 3)).toBilin' v w ≠ 0 := by
    intro hvw
    apply h.2
    apply singular_sup (gram K (s + 3)).toBilin' (gram_pairing_symmetric (s + 3))
      P.val Q.val P.property.2 Q.property.2
    intro x hx y hy
    rw [← hPspan] at hx
    rw [← hQspan] at hy
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hy
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      P.property.2 u huPQ.1 u huPQ.1, Q.property.2 u huPQ.2 w hwQ,
      P.property.2 v hvP u huPQ.1, hvw, smul_zero, add_zero]
  obtain ⟨g, c, hgu, hgv⟩ := exists_singular_pair_frame K h2 s u v hu
    (P.property.2 u huPQ.1 u huPQ.1) (P.property.2 v hvP v hvP)
    (P.property.2 u huPQ.1 v hvP) hvnot
  let e := naturalLinearEquiv K (s + 3) g
  have he : ∀ x y, (gram K (s + 3)).toBilin' (e x) (e y) =
      (gram K (s + 3)).toBilin' x y := fun x y => natural_pairing_invariant h2 (s + 3) g x y
  change e u = firstVector (K := K) s at hgu
  change e v = c • firstVector (K := K) s + secondVector (K := K) s at hgv
  have hw : (gram K (s + 3)).toBilin' (e w) (e w) = 0 :=
    (he w w).trans (Q.property.2 w hwQ w hwQ)
  have hwu : (gram K (s + 3)).toBilin' (e w) (firstVector s) = 0 := by
    rw [← hgu, he]
    exact Q.property.2 w hwQ u huPQ.2
  have hp : (gram K (s + 3)).toBilin' (e w) (secondVector s) =
      (gram K (s + 3)).toBilin' w v := by
    have hh := he w v
    rw [hgv, map_add, map_smul, hwu, smul_zero, zero_add] at hh
    exact hh
  have hc : (gram K (s + 3)).toBilin' (e w) (secondVector s) ≠ 0 := by
    intro hz
    exact hcross ((gram_pairing_symmetric (s + 3) v w).trans (hp.symm.trans hz))
  refine ⟨e, he, e w, hw, hwu, hc, ?_, ?_⟩
  · apply Subtype.ext
    change P.val.map e.toLinearMap = standardRootPlane (K := K) s
    rw [← hPspan, Submodule.map_span, Set.image_pair]
    change Submodule.span K {e u, e v} = standardRootPlane (K := K) s
    rw [hgu, hgv]
    exact CFSGTwoDimensionalSubmoduleBasis.span_pair_shear
      (firstVector (K := K) s) (secondVector (K := K) s) c
  · apply Subtype.ext
    change Q.val.map e.toLinearMap = pairPlane (K := K) (firstVector s) (e w)
    rw [← hQspan, Submodule.map_span, Set.image_pair]
    change Submodule.span K {e u, e w} = pairPlane (K := K) (firstVector s) (e w)
    rw [hgu]
    rfl

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBR11FrameNormalization
