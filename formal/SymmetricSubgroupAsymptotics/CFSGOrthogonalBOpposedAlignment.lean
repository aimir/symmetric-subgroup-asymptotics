import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedGraphShear
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBMaximalSubspaceOrbit
import SymmetricSubgroupAsymptotics.CFSGMatrixSubspaceUnitAction

/-! Actual original elementary words fixing V⁺ pointwise carry every
opposed full-rank singular space to V⁻. All intermediate graph vectors
remain in the SAME original carrier. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedAlignment
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBVectorCoordinates CFSGOrthogonalBUnipotent
open CFSGOrthogonalBOpposedProjection CFSGOrthogonalBOpposedGraphShear
open CFSGOrthogonalBPositiveMiddleWords CFSGPolarSubspacePoints
variable (K : Type) [Field K] [Finite K]

theorem exists_stabilizer_align_opposed (h2 : (2 : K) ≠ 0) (s : ℕ)
    (Q : Subspaces (gram K (s + 1)).toBilin')
    (hdis : Disjoint Q.val (positiveSubspace K (s + 1)))
    (hdim : Module.finrank K Q.val = s + 1) :
    ∃ g : elementaryRootGroup K (s + 1),
      (∀ v ∈ positiveSubspace K (s + 1), (g.val : Mat K (s + 1)) *ᵥ v = v) ∧
      Q.val.map (Matrix.mulVecLin (g.val : Mat K (s + 1))) = negativeSubspace K (s + 1) := by
  let L := graphLift K (s + 1) Q hdis hdim
  have hLn : ∀ y, negativePart K (s + 1) (L y) = y :=
    graphLift_negative K (s + 1) Q hdis hdim
  have hLr : L.range = Q.val := graphLift_range K (s + 1) Q hdis hdim
  let l : (Fin (s + 1) → K) →ₗ[K] K := (LinearMap.proj (middle (s + 1))).comp L
  obtain ⟨b, hbn, hbm, hbf⟩ := exists_clear_middle_functional K h2 s l
  let L' := (Matrix.mulVecLin (b.val : Mat K (s + 1))).comp L
  have hL'n (y : Fin (s + 1) → K) : negativePart K (s + 1) (L' y) = y := by
    funext i
    change (((b.val : Mat K (s + 1)) *ᵥ L y) (neg (s + 1) i)) = y i
    rw [hbn]
    exact congrFun (hLn y) i
  have hL'm (y : Fin (s + 1) → K) : L' y (middle (s + 1)) = 0 := by
    apply hbm
    rw [hLn]
    rfl
  have hL's (x y : Fin (s + 1) → K) :
      (gram K (s + 1)).toBilin' (L' x) (L' y) = 0 := by
    change (gram K (s + 1)).toBilin' ((b.val : Mat K (s + 1)) *ᵥ L x)
      ((b.val : Mat K (s + 1)) *ᵥ L y) = 0
    rw [natural_pairing_invariant h2]
    apply Q.property
    · rw [← hLr]; exact ⟨x, rfl⟩
    · rw [← hLr]; exact ⟨y, rfl⟩
  obtain ⟨c, hcf, hc⟩ := exists_shear_align K h2 s L' hL'n hL'm hL's
  have hL'r : L'.range = Q.val.map (Matrix.mulVecLin (b.val : Mat K (s + 1))) := by
    ext v
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨L y, ?_, rfl⟩
      rw [← hLr]
      exact ⟨y, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have hxL : x ∈ L.range := by rw [hLr]; exact hx
      obtain ⟨y, rfl⟩ := hxL
      exact ⟨y, rfl⟩
  refine ⟨c * b, ?_, ?_⟩
  · intro v hv
    change ((c.val : Mat K (s + 1)) * (b.val : Mat K (s + 1))) *ᵥ v = v
    rw [← Matrix.mulVec_mulVec, hbf v hv, hcf v hv]
  · change Q.val.map (Matrix.mulVecLin
      ((c.val * b.val : (Mat K (s + 1))ˣ) : Mat K (s + 1))) = _
    rw [CFSGMatrixSubspaceUnitAction.map_mul, ← hL'r]
    exact hc

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedAlignment
